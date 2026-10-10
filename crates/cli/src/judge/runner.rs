use super::{
    config::RuntimeConfig,
    mcp::Client,
    notification,
    state::{Report, State},
};
use anyhow::{anyhow, bail, ensure, Result};
use mimir_core::learning::{ExperienceState, Review};
use serde_json::{json, Value};
use std::future::Future;
use std::pin::Pin;
use std::time::Duration;
use uuid::Uuid;

#[cfg_attr(not(test), allow(dead_code))] // Step 6/7 adapters will construct actions.
pub enum Action {
    Tool { name: String, arguments: Value },
    Done,
}

/// Backends request operations; only the host owns the MCP client and scope.
pub trait Backend {
    /// A queued tool request can be returned without another provider call.
    fn will_call_model(&self, _selected: &ExperienceState) -> bool {
        true
    }

    fn next<'a>(
        &'a mut self,
        selected: &'a ExperienceState,
        last: Option<&'a Value>,
        tools: &'a [Value],
    ) -> Pin<Box<dyn Future<Output = Result<Action>> + Send + 'a>>;
}

/// No live provider adapter exists in Step 5. Tests inject a deterministic backend.
pub struct UnavailableBackend;
impl Backend for UnavailableBackend {
    fn next<'a>(
        &'a mut self,
        _selected: &'a ExperienceState,
        _last: Option<&'a Value>,
        _tools: &'a [Value],
    ) -> Pin<Box<dyn Future<Output = Result<Action>> + Send + 'a>> {
        Box::pin(async { bail!("configured backend adapter is not installed") })
    }
}

fn parse_state(value: Value) -> Result<ExperienceState> {
    serde_json::from_value(value).map_err(|_| anyhow!("invalid experience state"))
}

fn project_for(selected: &ExperienceState) -> &str {
    &selected.experience.project
}

async fn visible_belief(client: &mut Client, id: &str, project: &str) -> Result<bool> {
    let _: Uuid = id.parse().map_err(|_| anyhow!("invalid belief id"))?;
    let belief = client.tool("get_belief", json!({"id":id})).await?;
    Ok(!belief.is_null() && (belief["project"] == project || belief["project"].is_null()))
}

async fn scoped_tool(
    client: &mut Client,
    selected: &ExperienceState,
    name: &str,
    mut args: Value,
) -> Result<Value> {
    ensure!(args.is_object(), "tool arguments must be an object");
    let project = project_for(selected);
    let id = selected.experience.id.to_string();
    match name {
        "get_experience" | "experience_history" => {
            ensure!(args["id"] == id, "experience is outside pinned batch");
            if name == "experience_history" {
                let current = client.tool("get_experience", json!({"id":id})).await?;
                let state = parse_state(current)?;
                ensure!(
                    state.experience.project == project,
                    "experience moved outside selected project"
                );
            }
        }
        "review_experience" => {
            ensure!(
                args["expected_review_revision"].as_i64() == Some(selected.review_revision),
                "stale review token"
            );
            let mut review: Review = serde_json::from_value(args["review"].clone())
                .map_err(|_| anyhow!("invalid review arguments"))?;
            ensure!(
                review.experience_id == selected.experience.id
                    && review.experience_revision == selected.revision,
                "review is outside pinned revision"
            );
            // The model never chooses reviewer identity.
            review.reviewer = "mimir-judge".into();
            review.validate()?;
            args["review"] = serde_json::to_value(review)?;
        }
        "query_relevant" | "query_learning_context" | "get_contradictions" => {
            ensure!(
                args["project"] == project,
                "query is outside selected project"
            );
            if name != "get_contradictions" {
                let limit = args["limit"].as_u64().unwrap_or(0);
                ensure!((1..=20).contains(&limit), "query limit must be 1..=20");
            }
        }
        "get_belief" | "explain_belief" | "query_intervention" => {
            let belief_id = args["id"]
                .as_str()
                .ok_or_else(|| anyhow!("missing belief id"))?;
            // Provenance lookup is host-only and not charged to the model tool budget.
            ensure!(
                visible_belief(client, belief_id, project).await?,
                "belief is outside selected project"
            );
            if name == "explain_belief" || name == "query_intervention" {
                let source = client.tool("get_belief", json!({"id":belief_id})).await?;
                ensure!(
                    source["project"] == project,
                    "cross-project graph explanation is not available to the judge"
                );
            }
            if name == "explain_belief" {
                ensure!(
                    args["limit"]
                        .as_u64()
                        .is_some_and(|n| (1..=20).contains(&n)),
                    "invalid explain limit"
                );
                ensure!(args["offset"].as_u64().is_some(), "missing explain offset");
            }
            if name == "query_intervention" {
                ensure!(
                    args["value"]
                        .as_f64()
                        .is_some_and(|n| (0.0..=1.0).contains(&n)),
                    "invalid intervention value"
                );
            }
        }
        _ => bail!("tool is not allowed for judge"),
    }
    let mut value = client.tool(name, args).await?;
    if name == "get_experience" {
        let state = parse_state(value.clone())?;
        ensure!(
            state.experience.project == project && state.experience.id == selected.experience.id,
            "MCP returned out-of-scope experience"
        );
    }
    match name {
        "query_relevant" => {
            let beliefs = value
                .as_array()
                .ok_or_else(|| anyhow!("invalid belief search result"))?;
            ensure!(
                beliefs.len() <= 20
                    && beliefs
                        .iter()
                        .all(|b| b["project"] == project || b["project"].is_null()),
                "MCP returned out-of-scope beliefs"
            );
        }
        "query_learning_context" => {
            let beliefs = value["beliefs"]
                .as_array()
                .ok_or_else(|| anyhow!("invalid learning context"))?;
            let patterns = value["patterns"]
                .as_array()
                .ok_or_else(|| anyhow!("invalid learning context"))?;
            ensure!(
                beliefs.len() <= 20
                    && patterns.len() <= 20
                    && beliefs
                        .iter()
                        .all(|b| b["project"] == project || b["project"].is_null())
                    && patterns
                        .iter()
                        .all(|p| p["pattern"]["project"] == project
                            || p["pattern"]["project"].is_null()),
                "MCP returned out-of-scope learning context"
            );
        }
        "explain_belief" => {
            let edges = value["incoming_edges"]
                .as_array()
                .ok_or_else(|| anyhow!("invalid explanation"))?;
            ensure!(edges.len() <= 64, "explanation is too large");
            let mut filtered = Vec::new();
            for edge in edges {
                let source = edge["from_id"]
                    .as_str()
                    .ok_or_else(|| anyhow!("invalid explanation edge"))?;
                if visible_belief(client, source, project).await? {
                    filtered.push(edge.clone());
                }
            }
            value["incoming_edges"] = json!(filtered);
        }
        "query_intervention" => {
            let rows = value
                .as_array()
                .ok_or_else(|| anyhow!("invalid intervention result"))?;
            ensure!(rows.len() <= 64, "intervention result is too large");
            for row in rows {
                let target = row["id"]
                    .as_str()
                    .ok_or_else(|| anyhow!("invalid intervention target"))?;
                ensure!(
                    visible_belief(client, target, project).await?,
                    "intervention crosses selected project"
                );
            }
        }
        "get_contradictions" => {
            let pairs = value
                .as_array()
                .ok_or_else(|| anyhow!("invalid contradiction result"))?;
            ensure!(pairs.len() <= 64, "contradiction result is too large");
            let mut filtered = Vec::new();
            for pair in pairs {
                let pair = pair
                    .as_array()
                    .ok_or_else(|| anyhow!("invalid contradiction pair"))?;
                ensure!(pair.len() == 2, "invalid contradiction pair");
                let a = pair[0]
                    .as_str()
                    .ok_or_else(|| anyhow!("invalid contradiction ID"))?;
                let b = pair[1]
                    .as_str()
                    .ok_or_else(|| anyhow!("invalid contradiction ID"))?;
                if visible_belief(client, a, project).await?
                    && visible_belief(client, b, project).await?
                {
                    filtered.push(json!([a, b]));
                }
            }
            value = json!(filtered);
        }
        _ => {}
    }
    Ok(value)
}

async fn observe(client: &mut Client, selected: &ExperienceState) -> Result<&'static str> {
    let value = client
        .tool("get_experience", json!({"id":selected.experience.id}))
        .await?;
    if value.is_null() {
        return Ok("unavailable");
    }
    let state = parse_state(value)?;
    ensure!(
        state.experience.id == selected.experience.id
            && state.experience.project == selected.experience.project,
        "completion read returned an out-of-scope experience"
    );
    if state.revision != selected.revision {
        return Ok("corrected");
    }
    if state.reviewed_revision == selected.revision
        && state.review_revision > selected.review_revision
    {
        Ok("confirmed")
    } else {
        Ok("pending")
    }
}

pub async fn run<B: Backend>(settings: &RuntimeConfig, state: &State, backend: &mut B) -> Report {
    let mut report = Report::new("blocked", 0, 0, 0, 0, 0);
    let result = run_inner(settings, backend, &mut report).await;
    if result.is_err() {
        report.block_reason = Some("mcp_or_configuration_error".into());
        // Errors are intentionally not included in the public status: MCP and
        // provider responses can contain private experience or credential text.
        eprintln!("judge run did not complete; inspect MCP/provider health");
    }
    if notification::notify(settings, state, &mut report)
        .await
        .is_err()
    {
        eprintln!("judge notification state or delivery could not be processed");
        report.notification = "unavailable".into();
    }
    report.stamp();
    if let Err(_error) = state.write(&report) {
        eprintln!("judge status could not be persisted");
        report.status = "blocked".into();
        report.block_reason = Some("state_write_error".into());
    }
    report
}

async fn run_inner<B: Backend>(
    settings: &RuntimeConfig,
    backend: &mut B,
    report: &mut Report,
) -> Result<()> {
    let mut client = Client::start(
        &settings.judge.mcp_command,
        &settings.judge.mcp_args,
        &settings.path,
        settings.llm.timeout_seconds,
    )
    .await?;
    let mut arguments = json!({"limit":settings.judge.batch_size});
    if let Some(project) = &settings.judge.project {
        arguments["project"] = json!(project);
    }
    let fetched = client.tool("pending_experiences", arguments).await?;
    let batch: Vec<ExperienceState> =
        serde_json::from_value(fetched).map_err(|_| anyhow!("invalid pending batch"))?;
    ensure!(
        batch.len() <= settings.judge.batch_size,
        "MCP returned oversized pending batch"
    );
    let mut seen = std::collections::HashSet::new();
    for item in &batch {
        ensure!(
            item.revision > 0 && item.review_revision >= 0 && seen.insert(item.experience.id),
            "invalid pending batch"
        );
        if let Some(project) = &settings.judge.project {
            ensure!(
                item.experience.project == *project,
                "MCP returned wrong project"
            );
        }
    }
    report.selected = batch.len();
    if batch.is_empty() {
        report.status = "idle".into();
        return Ok(());
    }
    let mut model_left = settings.llm.max_calls;
    let mut tool_left = settings.llm.max_calls;
    let mut failed = false;
    let deadline = tokio::time::Instant::now() + Duration::from_secs(settings.llm.timeout_seconds);
    for selected in &batch {
        let mut last: Option<Value> = None;
        loop {
            let will_call_model = backend.will_call_model(selected);
            if will_call_model && model_left == 0 {
                failed = true;
                report.block_reason = Some("model_budget_exhausted".into());
                break;
            }
            if will_call_model {
                model_left -= 1;
            }
            let action = match tokio::time::timeout_at(
                deadline,
                backend.next(selected, last.as_ref(), client.allowed_tools()),
            )
            .await
            {
                Ok(Ok(action)) => action,
                _ => {
                    failed = true;
                    report.block_reason = Some("backend_error_or_timeout".into());
                    break;
                }
            };
            match action {
                Action::Done => break,
                Action::Tool { name, arguments } => {
                    if tool_left == 0 {
                        failed = true;
                        report.block_reason = Some("tool_budget_exhausted".into());
                        break;
                    }
                    tool_left -= 1;
                    match scoped_tool(&mut client, selected, &name, arguments).await {
                        Ok(value) => {
                            last = Some(value);
                            // The database acknowledgement is authoritative. A model
                            // need not spend another turn saying it is done.
                            if name == "review_experience"
                                && observe(&mut client, selected).await? != "pending"
                            {
                                break;
                            }
                        }
                        Err(_) => {
                            failed = true;
                            report.block_reason = Some("tool_error".into());
                            break;
                        }
                    }
                }
            }
        }
        if failed {
            break;
        }
    }
    for selected in &batch {
        match observe(&mut client, selected)
            .await
            .unwrap_or("unavailable")
        {
            "confirmed" => report.confirmed += 1,
            "corrected" => report.corrected += 1,
            "pending" => report.pending += 1,
            _ => report.unavailable += 1,
        }
    }
    report.status = if report.confirmed == report.selected
        && report.corrected == 0
        && report.pending == 0
        && report.unavailable == 0
    {
        "complete"
    } else if report.confirmed > 0 {
        "partial"
    } else {
        "blocked"
    }
    .into();
    if failed && report.block_reason.is_none() {
        report.block_reason = Some("incomplete".into());
    }
    if report.status != "complete" && report.block_reason.is_none() {
        report.block_reason = Some("revision_not_confirmed".into());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use mimir_core::{
        config::Config,
        learning::{Experience, ObservationSource, Outcome},
        MimirService,
    };
    use mimir_notifications::config::{Auth, EmailConfig, Tls};
    use std::path::PathBuf;
    use std::sync::Arc;

    #[derive(Clone, Copy)]
    enum Mode {
        Review,
        FalseDone,
        Stale,
        Crash,
        Correct,
        Partial,
    }
    struct Fake {
        mode: Mode,
        calls: usize,
        service: Arc<MimirService>,
    }
    impl Backend for Fake {
        fn next<'a>(
            &'a mut self,
            selected: &'a ExperienceState,
            _last: Option<&'a Value>,
            _tools: &'a [Value],
        ) -> Pin<Box<dyn Future<Output = Result<Action>> + Send + 'a>> {
            Box::pin(async move {
                self.calls += 1;
                if matches!(self.mode, Mode::Partial) && self.calls > 2 {
                    bail!("fake backend crashed after one review");
                }
                if self.calls > 1 {
                    return Ok(Action::Done);
                }
                match self.mode {
                    Mode::Review | Mode::Stale | Mode::Partial => Ok(Action::Tool {
                        name: "review_experience".into(),
                        arguments: json!({"expected_review_revision": if matches!(self.mode, Mode::Stale) { 99 } else { selected.review_revision },
                            "review":{"experience_id":selected.experience.id,
                                "experience_revision":selected.revision,"reviewer":"untrusted-model",
                                "rationale":"deterministic review of test observation"}}),
                    }),
                    Mode::FalseDone => Ok(Action::Done),
                    Mode::Crash => bail!("fake backend crashed"),
                    Mode::Correct => {
                        let mut updated = selected.experience.clone();
                        updated.action = "corrected action".into();
                        self.service
                            .record_experience(&updated, selected.revision)
                            .await?;
                        Ok(Action::Done)
                    }
                }
            })
        }
    }

    #[tokio::test]
    async fn isolated_mcp_review_cycle() {
        let Ok(path) = std::env::var("MIMIR_STEP5_TEST_CONFIG") else {
            return;
        };
        let binary = std::env::var("MIMIR_STEP5_MCP_BIN").expect("MCP binary path");
        let project = format!("step5-{}", Uuid::new_v4());
        let mut settings = super::super::config::load(Some(std::path::Path::new(&path))).unwrap();
        settings.judge.project = Some(project.clone());
        settings.judge.mcp_command = binary;
        settings.judge.batch_size = 1;
        let core = Config::load_from_path(&settings.path).unwrap();
        let service = Arc::new(MimirService::connect(&core).await.unwrap());
        let state_path = PathBuf::from(format!("/var/tmp/mimir/step5/state-{}", Uuid::new_v4()));
        let state = State::lock(state_path.clone()).unwrap().unwrap();
        let make_experience = || Experience {
            id: Uuid::new_v4(),
            project: project.clone(),
            context: "test incident".into(),
            action: "checked result".into(),
            outcome: Outcome::Success,
            source: ObservationSource::ToolResult,
            evidence: vec!["isolated test receipt".into()],
            belief_ids: vec![],
            pattern_id: None,
        };
        let e = make_experience();
        service.record_experience(&e, 0).await.unwrap();
        let mut fake = Fake {
            mode: Mode::Review,
            calls: 0,
            service: service.clone(),
        };
        let success = run(&settings, &state, &mut fake).await;
        assert_eq!(success.status, "complete");
        assert_eq!(success.confirmed, 1);
        assert_eq!(fake.calls, 1);
        let committed = service.get_experience(e.id).await.unwrap().unwrap();
        assert_eq!(committed.reviewed_revision, 1);
        let history = service.experience_history(e.id).await.unwrap();
        assert_eq!(history["reviews"][0]["payload"]["reviewer"], "mimir-judge");
        fake.calls = 0;
        let idle = run(&settings, &state, &mut fake).await;
        assert_eq!(idle.status, "idle");
        assert_eq!(fake.calls, 0);
        assert_eq!(
            super::super::state::read(&state_path)
                .unwrap()
                .unwrap()
                .status,
            "idle"
        );

        let mut corrected = e.clone();
        corrected.outcome = Outcome::Failure;
        corrected.evidence = vec!["user corrected the observed result".into()];
        service.record_experience(&corrected, 1).await.unwrap();
        fake.calls = 0;
        let correction = run(&settings, &state, &mut fake).await;
        assert_eq!(correction.status, "complete");
        assert_eq!(correction.confirmed, 1);
        assert_eq!(
            service
                .get_experience(e.id)
                .await
                .unwrap()
                .unwrap()
                .reviewed_revision,
            2
        );

        for mode in [Mode::FalseDone, Mode::Stale, Mode::Crash, Mode::Correct] {
            let e = make_experience();
            service.record_experience(&e, 0).await.unwrap();
            let mut backend = Fake {
                mode,
                calls: 0,
                service: service.clone(),
            };
            let report = run(&settings, &state, &mut backend).await;
            assert_eq!(report.status, "blocked");
            if matches!(mode, Mode::Correct) {
                assert_eq!(report.corrected, 1);
            }
            // Clear only this test project's unfinished item before the next case.
            let latest = service.get_experience(e.id).await.unwrap().unwrap();
            let review = mimir_core::learning::Review {
                experience_id: e.id,
                experience_revision: latest.revision,
                reviewer: "test-cleanup".into(),
                rationale: "finish isolated fixture".into(),
                feedback: vec![],
                links: vec![],
                superseded_beliefs: vec![],
                candidates: vec![],
                candidate_feedback: vec![],
                candidate_links: vec![],
            };
            service
                .review_experience(&review, latest.review_revision)
                .await
                .unwrap();
        }
        settings.judge.batch_size = 2;
        let first = make_experience();
        let second = make_experience();
        service.record_experience(&first, 0).await.unwrap();
        service.record_experience(&second, 0).await.unwrap();
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let port = listener.local_addr().unwrap().port();
        let smtp = tokio::spawn(async move {
            let (socket, _) = listener.accept().await.unwrap();
            drop(socket); // local SMTP transport failure after a committed review
        });
        settings.email = EmailConfig {
            enabled: true,
            host: Some("127.0.0.1".into()),
            port: Some(port),
            tls: Some(Tls::Starttls),
            from_address: Some("mimir@example.test".into()),
            to: vec!["owner@example.test".into()],
            username: None,
            auth: Some(Auth::None),
            password: None,
            oauth: None,
            timeout_seconds: 3,
            retry_seconds: 10,
            max_attempts: 2,
        };
        let mut partial = Fake {
            mode: Mode::Partial,
            calls: 0,
            service: service.clone(),
        };
        let report = run(&settings, &state, &mut partial).await;
        assert_eq!(report.status, "partial");
        assert_eq!(report.confirmed, 1);
        assert_eq!(report.pending, 1);
        assert_eq!(report.notification, "retry_pending");
        let reviewed = service
            .get_experience(first.id)
            .await
            .unwrap()
            .unwrap()
            .reviewed_revision
            + service
                .get_experience(second.id)
                .await
                .unwrap()
                .unwrap()
                .reviewed_revision;
        assert_eq!(reviewed, 1);
        smtp.await.unwrap();
        service.delete_project(&project).await.unwrap();
        drop(state);
        std::fs::remove_dir_all(state_path).unwrap();
    }
}
