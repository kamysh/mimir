use super::{
    config::RuntimeConfig,
    mcp::{CandidateConflict, Client, McpApplicationError},
    notification,
    state::{
        self, DeferredReview, DiagnosticEvent, FailureDiagnostic, Report, SourceFailure, State,
    },
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
    RejectedTool { name: String, source: SourceFailure },
    Done,
}

#[derive(Debug)]
struct InputRejected(String);

#[derive(Debug)]
struct DiagnosticWriteError(String);

impl std::fmt::Display for DiagnosticWriteError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for DiagnosticWriteError {}

impl std::fmt::Display for InputRejected {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for InputRejected {}

macro_rules! input_ensure {
    ($condition:expr, $message:literal) => {
        if !$condition {
            return Err(InputRejected($message.into()).into());
        }
    };
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
    serde_json::from_value(value.clone()).map_err(|error| {
        state::SourceFailure::json(
            "invalid experience state",
            value.to_string().as_bytes(),
            error,
        )
        .into()
    })
}

fn still_deferred(deferred: &DeferredReview, revision: i64, reviewed_revision: i64) -> bool {
    revision == deferred.revision && reviewed_revision < revision
}

fn project_for(selected: &ExperienceState) -> &str {
    &selected.experience.project
}

async fn visible_belief(client: &mut Client, id: &str, project: &str) -> Result<bool> {
    let _: Uuid = id
        .parse()
        .map_err(|_| InputRejected("invalid belief id".into()))?;
    let belief = client.tool("get_belief", json!({"id":id})).await?;
    Ok(!belief.is_null() && (belief["project"] == project || belief["project"].is_null()))
}

async fn scoped_tool(
    client: &mut Client,
    selected: &ExperienceState,
    name: &str,
    mut args: Value,
) -> Result<Value> {
    input_ensure!(args.is_object(), "tool arguments must be an object");
    let project = project_for(selected);
    let id = selected.experience.id.to_string();
    match name {
        "get_experience" | "experience_history" => {
            input_ensure!(args["id"] == id, "experience is outside pinned batch");
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
            input_ensure!(
                args["expected_review_revision"].as_i64() == Some(selected.review_revision),
                "stale review token"
            );
            let mut review: Review =
                serde_json::from_value(args["review"].clone()).map_err(|error| {
                    state::SourceFailure::json(
                        "invalid review arguments",
                        args["review"].to_string().as_bytes(),
                        error,
                    )
                })?;
            input_ensure!(
                review.experience_id == selected.experience.id
                    && review.experience_revision == selected.revision,
                "review is outside pinned revision"
            );
            // The model never chooses reviewer identity.
            review.reviewer = "mimir-judge".into();
            review
                .validate()
                .map_err(|error| InputRejected(error.to_string()))?;
            args["review"] = serde_json::to_value(review)?;
        }
        "query_relevant" | "query_learning_context" | "get_contradictions" => {
            input_ensure!(
                args["project"] == project,
                "query is outside selected project"
            );
            if name != "get_contradictions" {
                let limit = args["limit"].as_u64().unwrap_or(0);
                input_ensure!((1..=20).contains(&limit), "query limit must be 1..=20");
            }
        }
        "get_belief" | "explain_belief" | "query_intervention" => {
            let belief_id = args["id"]
                .as_str()
                .ok_or_else(|| InputRejected("missing belief id".into()))?;
            // Provenance lookup is host-only and not charged to the model tool budget.
            input_ensure!(
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
                input_ensure!(
                    args["limit"]
                        .as_u64()
                        .is_some_and(|n| (1..=20).contains(&n)),
                    "invalid explain limit"
                );
                input_ensure!(args["offset"].as_u64().is_some(), "missing explain offset");
            }
            if name == "query_intervention" {
                input_ensure!(
                    args["value"]
                        .as_f64()
                        .is_some_and(|n| (0.0..=1.0).contains(&n)),
                    "invalid intervention value"
                );
            }
        }
        _ => return Err(InputRejected("tool is not allowed for judge".into()).into()),
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
    let result = run_inner(settings, state, backend, &mut report).await;
    if let Err(error) = result {
        report.block_reason = Some(
            if error.downcast_ref::<DiagnosticWriteError>().is_some() {
                "diagnostics_write_error"
            } else {
                "mcp_or_configuration_error"
            }
            .into(),
        );
        report.failure_detail = Some(state::bounded(&format!("{error:#}"), 512));
        report.capture_source(&error);
    }
    finish_report(settings, state, report).await
}

fn trace(
    state: &State,
    report: &Report,
    selected: &ExperienceState,
    kind: &str,
    model_left: usize,
    tool_left: usize,
    tool: Option<&str>,
    detail: Option<&str>,
) -> Result<()> {
    if let Some(id) = report.diagnostics_id {
        state
            .trace_event(
                id,
                DiagnosticEvent::new(
                    selected.experience.id,
                    kind,
                    model_left,
                    tool_left,
                    tool,
                    detail,
                ),
            )
            .map_err(|error| {
                DiagnosticWriteError(format!("diagnostic trace write failed: {error:#}"))
            })?;
    }
    Ok(())
}

pub async fn setup_failure(
    settings: &RuntimeConfig,
    state: &State,
    reason: &str,
    error: &anyhow::Error,
) -> Report {
    let mut report = Report::new("blocked", 0, 0, 0, 0, 0);
    report.block_reason = Some(reason.into());
    report.failure_detail = Some(state::bounded(&format!("{error:#}"), 512));
    report.capture_source(error);
    finish_report(settings, state, report).await
}

async fn finish_report(settings: &RuntimeConfig, state: &State, mut report: Report) -> Report {
    report.stamp();
    if let Some(id) = report.diagnostics_id {
        match state.finish_trace(id, &report) {
            Ok(()) if report.status == "complete" => report.diagnostics_id = None,
            Ok(()) => {}
            Err(error) => {
                report.status = "blocked".into();
                report.block_reason = Some("diagnostics_write_error".into());
                report.failure_detail = Some(state::bounded(&format!("{error:#}"), 512));
            }
        }
    }
    if state.record_incident(&report).is_err() {
        report.status = "blocked".into();
        report.block_reason = Some("incident_write_error".into());
    }
    if state.write(&report).is_err() {
        report.status = "blocked".into();
        report.block_reason = Some("state_write_error".into());
        return report;
    }
    if notification::notify(settings, state, &mut report)
        .await
        .is_err()
    {
        report.notification = "unavailable".into();
    }
    if state.write(&report).is_err() {
        report.status = "blocked".into();
        report.block_reason = Some("state_write_error".into());
    }
    report
}

async fn run_inner<B: Backend>(
    settings: &RuntimeConfig,
    state: &State,
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
    // A rejected source revision is held until it is corrected or reviewed by
    // another caller. Reconcile against the database before excluding it.
    let previous = state::read(state.path())?;
    for deferred in previous
        .into_iter()
        .flat_map(|report| report.deferred_reviews)
    {
        let current = client
            .tool("get_experience", json!({"id":deferred.id}))
            .await?;
        if current.is_null() {
            continue;
        }
        let current = parse_state(current)?;
        let in_scope = settings
            .judge
            .project
            .as_ref()
            .is_none_or(|project| *project == current.experience.project);
        if in_scope && still_deferred(&deferred, current.revision, current.reviewed_revision) {
            report.deferred_reviews.push(deferred);
        }
    }
    ensure!(
        report.deferred_reviews.len() <= 1000,
        "too many deferred reviews"
    );
    let mut arguments = json!({"limit":settings.judge.batch_size});
    arguments["exclude_ids"] = json!(report
        .deferred_reviews
        .iter()
        .map(|item| item.id)
        .collect::<Vec<_>>());
    if let Some(project) = &settings.judge.project {
        arguments["project"] = json!(project);
    }
    let fetched = client.tool("pending_experiences", arguments).await?;
    let batch: Vec<ExperienceState> = serde_json::from_value(fetched.clone()).map_err(|error| {
        state::SourceFailure::json(
            "invalid pending batch",
            fetched.to_string().as_bytes(),
            error,
        )
    })?;
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
    report.selected_ids = batch.iter().map(|item| item.experience.id).collect();
    if batch.is_empty() {
        if report.deferred_reviews.is_empty() {
            report.status = "idle".into();
        } else {
            report.status = "blocked".into();
            report.block_reason = Some("review_deferred".into());
        }
        return Ok(());
    }
    report.diagnostics_id = Some(state.begin_trace(report, settings.llm.max_calls).map_err(
        |error| DiagnosticWriteError(format!("diagnostic trace start failed: {error:#}")),
    )?);
    let mut model_left = settings.llm.max_calls;
    let mut tool_left = settings.llm.max_calls;
    let mut failed = false;
    let deadline = tokio::time::Instant::now() + Duration::from_secs(settings.llm.timeout_seconds);
    for selected in &batch {
        let mut last: Option<Value> = None;
        let mut candidate_rejections = 0;
        let mut candidate_rejection_detail = None;
        let mut last_rejection: Option<(String, String, Option<SourceFailure>)> = None;
        let mut confirmed_review = false;
        loop {
            let will_call_model = backend.will_call_model(selected);
            if will_call_model && model_left == 0 {
                trace(
                    state,
                    report,
                    selected,
                    "model_budget_exhausted",
                    model_left,
                    tool_left,
                    None,
                    None,
                )?;
                if candidate_rejections == 0 {
                    failed = true;
                    report.block_reason = Some("model_budget_exhausted".into());
                }
                break;
            }
            if will_call_model {
                model_left -= 1;
                let detail = last.as_ref().map(Value::to_string);
                trace(
                    state,
                    report,
                    selected,
                    "model_request",
                    model_left,
                    tool_left,
                    None,
                    detail.as_deref(),
                )?;
            }
            let action = match tokio::time::timeout_at(
                deadline,
                backend.next(selected, last.as_ref(), client.allowed_tools()),
            )
            .await
            {
                Ok(Ok(action)) => action,
                Ok(Err(error)) => {
                    trace(
                        state,
                        report,
                        selected,
                        "model_error",
                        model_left,
                        tool_left,
                        None,
                        Some(&format!("{error:#}")),
                    )?;
                    if candidate_rejections == 0 {
                        failed = true;
                        report.block_reason = Some("backend_error".into());
                        report.failure_detail = Some(state::bounded(&format!("{error:#}"), 512));
                        report.capture_source(&error);
                    }
                    break;
                }
                Err(_) => {
                    trace(
                        state,
                        report,
                        selected,
                        "model_timeout",
                        model_left,
                        tool_left,
                        None,
                        None,
                    )?;
                    if candidate_rejections == 0 {
                        failed = true;
                        report.block_reason = Some("backend_timeout".into());
                        report.failure_detail = Some("backend response timed out".into());
                    }
                    break;
                }
            };
            match action {
                Action::Done => {
                    trace(
                        state,
                        report,
                        selected,
                        "model_done",
                        model_left,
                        tool_left,
                        None,
                        None,
                    )?;
                    break;
                }
                Action::RejectedTool { name, source } => {
                    trace(
                        state,
                        report,
                        selected,
                        "tool_parse_rejection",
                        model_left,
                        tool_left,
                        Some(&name),
                        Some(&source.excerpt),
                    )?;
                    if tool_left == 0 {
                        trace(
                            state,
                            report,
                            selected,
                            "tool_budget_exhausted",
                            model_left,
                            tool_left,
                            Some(&name),
                            None,
                        )?;
                        failed = true;
                        report.block_reason = Some("tool_budget_exhausted".into());
                        break;
                    }
                    tool_left -= 1;
                    // The model already knows its input. Return only the parser's
                    // location and a fixed correction instruction, never the input.
                    last = Some(json!({"error":"invalid_tool_arguments",
                        "message":source.detail,
                        "guidance":"Correct the tool arguments using the supplied schema and resend the call."}));
                    last_rejection = Some((name, source.to_string(), Some(source)));
                }
                Action::Tool { name, arguments } => {
                    trace(
                        state,
                        report,
                        selected,
                        "tool_request",
                        model_left,
                        tool_left,
                        Some(&name),
                        Some(&arguments.to_string()),
                    )?;
                    if tool_left == 0 {
                        trace(
                            state,
                            report,
                            selected,
                            "tool_budget_exhausted",
                            model_left,
                            tool_left,
                            Some(&name),
                            None,
                        )?;
                        if candidate_rejections == 0 {
                            failed = true;
                            report.block_reason = Some("tool_budget_exhausted".into());
                        }
                        break;
                    }
                    tool_left -= 1;
                    match scoped_tool(&mut client, selected, &name, arguments).await {
                        Ok(value) => {
                            trace(
                                state,
                                report,
                                selected,
                                "tool_result",
                                model_left,
                                tool_left,
                                Some(&name),
                                Some(&value.to_string()),
                            )?;
                            last = Some(value);
                            // The database acknowledgement is authoritative. A model
                            // need not spend another turn saying it is done.
                            if name == "review_experience"
                                && observe(&mut client, selected).await? != "pending"
                            {
                                confirmed_review = true;
                                break;
                            }
                        }
                        Err(error)
                            if name == "review_experience"
                                && error.downcast_ref::<CandidateConflict>().is_some() =>
                        {
                            trace(
                                state,
                                report,
                                selected,
                                "candidate_conflict",
                                model_left,
                                tool_left,
                                Some(&name),
                                Some(&format!("{error:#}")),
                            )?;
                            candidate_rejections += 1;
                            candidate_rejection_detail = Some(format!("{error:#}"));
                            if candidate_rejections >= 2 {
                                break;
                            }
                            last = Some(json!({"error":"candidate_key_conflict",
                                "guidance":"A candidate key from an earlier review has a different declaration. Inspect experience_history. Reuse a key only with its exact original kind and declaration; use a new key for a revised claim."}));
                        }
                        Err(error)
                            if error.downcast_ref::<InputRejected>().is_some()
                                || error.downcast_ref::<McpApplicationError>().is_some()
                                || error.downcast_ref::<SourceFailure>().is_some_and(
                                    |source| source.stage == "invalid review arguments",
                                ) =>
                        {
                            trace(
                                state,
                                report,
                                selected,
                                "tool_rejection",
                                model_left,
                                tool_left,
                                Some(&name),
                                Some(&format!("{error:#}")),
                            )?;
                            // Tool-level rejection is feedback to the model, not
                            // a service failure. Never forward MCP error text.
                            let message = if let Some(input) = error.downcast_ref::<InputRejected>()
                            {
                                input.to_string()
                            } else if let Some(source) = error.downcast_ref::<SourceFailure>() {
                                source.detail.clone()
                            } else {
                                "Mimir rejected this tool call. Check the tool schema and arguments."
                                    .into()
                            };
                            last = Some(json!({"error":"invalid_tool_arguments",
                                "message":message,
                                "guidance":"Correct the tool arguments and resubmit the request. The rejected call changed nothing."}));
                            last_rejection = Some((
                                name,
                                state::bounded(&format!("{error:#}"), 512),
                                error.downcast_ref::<SourceFailure>().cloned(),
                            ));
                        }
                        Err(error) => {
                            trace(
                                state,
                                report,
                                selected,
                                "tool_error",
                                model_left,
                                tool_left,
                                Some(&name),
                                Some(&format!("{error:#}")),
                            )?;
                            failed = true;
                            report.block_reason = Some("tool_error".into());
                            report.diagnostic = Some(FailureDiagnostic::new(
                                selected.experience.id,
                                &name,
                                &format!("{error:#}"),
                            ));
                            report.capture_source(&error);
                            break;
                        }
                    }
                }
            }
        }
        if !confirmed_review {
            if let Some((name, detail, source)) = last_rejection {
                if report.diagnostic.is_none() {
                    report.diagnostic = Some(FailureDiagnostic::new(
                        selected.experience.id,
                        &name,
                        &detail,
                    ));
                }
                if report.failure_source.is_none() {
                    report.failure_source = source;
                }
                if report.block_reason.is_none() {
                    report.block_reason = Some("tool_rejected".into());
                }
            }
        }
        if candidate_rejections > 0 && !confirmed_review && !failed {
            if report.diagnostic.is_none() {
                report.diagnostic = Some(FailureDiagnostic::new(
                    selected.experience.id,
                    "review_experience",
                    candidate_rejection_detail
                        .as_deref()
                        .unwrap_or("review correction was not confirmed"),
                ));
            }
            ensure!(
                report.deferred_reviews.len() < 1000,
                "too many deferred reviews"
            );
            report.deferred_reviews.push(DeferredReview {
                id: selected.experience.id,
                revision: selected.revision,
            });
        }
        if failed {
            break;
        }
    }
    for selected in &batch {
        match observe(&mut client, selected).await {
            Ok("confirmed") => report.confirmed += 1,
            Ok("corrected") => report.corrected += 1,
            Ok("pending") => report.pending += 1,
            Ok(_) => report.unavailable += 1,
            Err(error) => {
                report.unavailable += 1;
                report.capture_source(&error);
                if report.diagnostic.is_none() {
                    report.diagnostic = Some(FailureDiagnostic::new(
                        selected.experience.id,
                        "get_experience",
                        &format!("{error:#}"),
                    ));
                }
            }
        }
    }
    report.status = if report.confirmed == report.selected
        && report.corrected == 0
        && report.pending == 0
        && report.unavailable == 0
        && report.deferred_reviews.is_empty()
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
        report.block_reason = Some(
            if report.deferred_reviews.is_empty() {
                "revision_not_confirmed"
            } else {
                "review_deferred"
            }
            .into(),
        );
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

    #[test]
    fn deferred_revision_is_reconsidered_only_after_change_or_external_review() {
        let item = DeferredReview {
            id: Uuid::new_v4(),
            revision: 2,
        };
        assert!(still_deferred(&item, 2, 1));
        assert!(!still_deferred(&item, 3, 1));
        assert!(!still_deferred(&item, 2, 2));
    }

    struct ReferenceCorrection {
        calls: usize,
        correct: bool,
    }

    impl Backend for ReferenceCorrection {
        fn next<'a>(
            &'a mut self,
            selected: &'a ExperienceState,
            last: Option<&'a Value>,
            _tools: &'a [Value],
        ) -> Pin<Box<dyn Future<Output = Result<Action>> + Send + 'a>> {
            Box::pin(async move {
                if self.calls > 0 {
                    let feedback = last.ok_or_else(|| anyhow!("missing validation feedback"))?;
                    ensure!(feedback["error"] == "invalid_tool_arguments");
                    ensure!(feedback["message"]
                        .as_str()
                        .is_some_and(|text| text.contains("declared in this review")));
                }
                self.calls += 1;
                let candidates = if self.calls == 2 && self.correct {
                    json!([{"kind":"belief","key":"fixture-key","content":"fixture conclusion"}])
                } else {
                    json!([])
                };
                Ok(Action::Tool {
                    name: "review_experience".into(),
                    arguments: json!({
                        "expected_review_revision":selected.review_revision,
                        "review":{
                            "experience_id":selected.experience.id,
                            "experience_revision":selected.revision,
                            "reviewer":"fixture",
                            "rationale":"fixture correction",
                            "candidates":candidates,
                            "candidate_feedback":[{"target":{"candidate_key":"fixture-key"},"verdict":"support","weight":0.8}]
                        }
                    }),
                })
            })
        }
    }

    #[derive(Clone, Copy)]
    enum RejectionCase {
        MalformedJson,
        LocalValidation,
        MimirError,
        Exhausted,
    }

    struct ToolCorrection {
        case: RejectionCase,
        calls: usize,
    }

    struct NoReview {
        calls: usize,
    }

    impl Backend for NoReview {
        fn next<'a>(
            &'a mut self,
            selected: &'a ExperienceState,
            _last: Option<&'a Value>,
            _tools: &'a [Value],
        ) -> Pin<Box<dyn Future<Output = Result<Action>> + Send + 'a>> {
            Box::pin(async move {
                self.calls += 1;
                Ok(Action::Tool {
                    name: "get_experience".into(),
                    arguments: json!({"id":selected.experience.id}),
                })
            })
        }
    }

    impl Backend for ToolCorrection {
        fn next<'a>(
            &'a mut self,
            selected: &'a ExperienceState,
            last: Option<&'a Value>,
            _tools: &'a [Value],
        ) -> Pin<Box<dyn Future<Output = Result<Action>> + Send + 'a>> {
            Box::pin(async move {
                if self.calls > 0 {
                    let feedback = last.ok_or_else(|| anyhow!("missing tool feedback"))?;
                    ensure!(feedback["error"] == "invalid_tool_arguments");
                    ensure!(!feedback
                        .to_string()
                        .contains("private fixture database detail"));
                    if matches!(self.case, RejectionCase::LocalValidation) {
                        ensure!(feedback["message"] == "stale review token");
                    }
                    if matches!(self.case, RejectionCase::MimirError) {
                        ensure!(feedback["message"]
                            .as_str()
                            .is_some_and(|message| message.contains("Mimir rejected")));
                    }
                }
                self.calls += 1;
                if self.calls == 1 || matches!(self.case, RejectionCase::Exhausted) {
                    return Ok(match self.case {
                        RejectionCase::MalformedJson | RejectionCase::Exhausted => {
                            let input = "{\"review\": }";
                            let error = serde_json::from_str::<Value>(input).err().unwrap();
                            Action::RejectedTool {
                                name: "review_experience".into(),
                                source: SourceFailure::json(
                                    "invalid harness tool arguments",
                                    input.as_bytes(),
                                    error,
                                ),
                            }
                        }
                        RejectionCase::LocalValidation => Action::Tool {
                            name: "review_experience".into(),
                            arguments: json!({"expected_review_revision":-1}),
                        },
                        RejectionCase::MimirError => Action::Tool {
                            name: "query_relevant".into(),
                            arguments: json!({"project":selected.experience.project,
                                "context":"fixture observation","limit":1}),
                        },
                    });
                }
                Ok(Action::Tool {
                    name: "review_experience".into(),
                    arguments: json!({
                        "expected_review_revision":selected.review_revision,
                        "review":{
                            "experience_id":selected.experience.id,
                            "experience_revision":selected.revision,
                            "reviewer":"fixture",
                            "rationale":"corrected tool request"
                        }
                    }),
                })
            })
        }
    }

    #[tokio::test]
    async fn invalid_tool_requests_return_feedback_and_have_bounded_retries() {
        use std::os::unix::fs::PermissionsExt;

        let fixture = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src/judge/retry_fixture.sh");
        for case in [
            RejectionCase::MalformedJson,
            RejectionCase::LocalValidation,
            RejectionCase::MimirError,
            RejectionCase::Exhausted,
        ] {
            let id = Uuid::new_v4();
            let dir =
                std::env::temp_dir().join(format!("mimir-judge-tool-feedback-{}", Uuid::new_v4()));
            std::fs::create_dir(&dir).unwrap();
            std::fs::set_permissions(&dir, std::fs::Permissions::from_mode(0o700)).unwrap();
            let config_path = dir.join("config.toml");
            std::fs::write(
                &config_path,
                format!(
                    "[database]\nhost='localhost'\nport=5432\ndbname='unused'\nuser='unused'\n[judge]\nproject='judge-retry-fixture'\nbatch_size=1\nmcp_command='bash'\nmcp_args=['{}','{}']\n[llm]\nbackend='command'\nmodel='fixture'\ncommand='/bin/true'\ntimeout_seconds=10\nmax_calls=3\n",
                    fixture.display(), id
                ),
            )
            .unwrap();
            std::fs::set_permissions(&config_path, std::fs::Permissions::from_mode(0o600)).unwrap();
            let settings = super::super::config::load(Some(&config_path)).unwrap();
            let state = State::lock(dir.join("state")).unwrap().unwrap();
            let mut backend = ToolCorrection { case, calls: 0 };
            let report = run(&settings, &state, &mut backend).await;
            if matches!(case, RejectionCase::Exhausted) {
                assert_eq!(report.status, "blocked");
                assert_eq!(backend.calls, 3);
                assert_eq!(
                    report.block_reason.as_deref(),
                    Some("model_budget_exhausted")
                );
                assert_eq!(
                    report.failure_source.as_ref().unwrap().excerpt,
                    "{\"review\": }"
                );
            } else {
                assert_eq!(report.status, "complete");
                assert_eq!(backend.calls, 2);
                assert!(report.diagnostic.is_none());
            }
            drop(state);
            std::fs::remove_dir_all(dir).unwrap();
        }
    }

    #[tokio::test]
    async fn model_budget_failure_keeps_an_actionable_trace_after_later_success() {
        use std::os::unix::fs::PermissionsExt;

        let fixture = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src/judge/retry_fixture.sh");
        let dir = std::env::temp_dir().join(format!("mimir-judge-budget-trace-{}", Uuid::new_v4()));
        std::fs::create_dir(&dir).unwrap();
        std::fs::set_permissions(&dir, std::fs::Permissions::from_mode(0o700)).unwrap();
        let config_path = dir.join("config.toml");
        std::fs::write(
            &config_path,
            format!(
                "[database]\nhost='localhost'\nport=5432\ndbname='unused'\nuser='unused'\n[judge]\nproject='judge-retry-fixture'\nbatch_size=1\nmcp_command='bash'\nmcp_args=['{}','{}']\n[llm]\nbackend='command'\nmodel='fixture'\ncommand='/bin/true'\ntimeout_seconds=10\nmax_calls=5\n",
                fixture.display(), Uuid::new_v4()
            ),
        )
        .unwrap();
        std::fs::set_permissions(&config_path, std::fs::Permissions::from_mode(0o600)).unwrap();
        let settings = super::super::config::load(Some(&config_path)).unwrap();
        let state = State::lock(dir.join("state")).unwrap().unwrap();
        let mut backend = NoReview { calls: 0 };
        let failed = run(&settings, &state, &mut backend).await;
        assert_eq!(failed.status, "blocked");
        assert_eq!(
            failed.block_reason.as_deref(),
            Some("model_budget_exhausted")
        );
        assert!(failed.diagnostic.is_none());
        assert_eq!(backend.calls, 5);
        let id = failed.diagnostics_id.unwrap();
        let diagnostics = state::read_diagnostics(state.path()).unwrap();
        let trace = diagnostics
            .attempts
            .iter()
            .find(|trace| trace.id == id)
            .unwrap();
        assert_eq!(trace.model_remaining, 0);
        assert_eq!(trace.tool_remaining, 0);
        assert_eq!(
            trace
                .events
                .iter()
                .filter(|event| event.kind == "model_request")
                .count(),
            5
        );
        assert_eq!(
            trace
                .events
                .iter()
                .filter(|event| event.kind == "tool_result")
                .count(),
            5
        );
        assert_eq!(trace.events.last().unwrap().kind, "model_budget_exhausted");
        assert_eq!(trace.events[1].tool.as_deref(), Some("get_experience"));
        let mut recovery = ToolCorrection {
            case: RejectionCase::LocalValidation,
            calls: 0,
        };
        let completed = run(&settings, &state, &mut recovery).await;
        assert_eq!(completed.status, "complete");
        assert!(state::read_diagnostics(state.path())
            .unwrap()
            .attempts
            .iter()
            .any(|trace| trace.id == id));
        assert_eq!(
            state::read_failure(state.path())
                .unwrap()
                .unwrap()
                .first
                .diagnostics_id,
            Some(id)
        );
        drop(state);
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[tokio::test]
    async fn undeclared_candidate_is_refused_before_mcp_and_stays_eligible() {
        use std::os::unix::fs::PermissionsExt;

        let fixture = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src/judge/retry_fixture.sh");
        for (correct, expected_status) in [(true, "complete"), (false, "blocked")] {
            let id = Uuid::new_v4();
            let dir = std::env::temp_dir().join(format!("mimir-judge-retry-{}", Uuid::new_v4()));
            std::fs::create_dir(&dir).unwrap();
            std::fs::set_permissions(&dir, std::fs::Permissions::from_mode(0o700)).unwrap();
            let config_path = dir.join("config.toml");
            let review_log = dir.join("review-calls.log");
            std::fs::write(
                &config_path,
                format!(
                    "[database]\nhost='localhost'\nport=5432\ndbname='unused'\nuser='unused'\n[judge]\nproject='judge-retry-fixture'\nbatch_size=1\nmcp_command='bash'\nmcp_args=['{}','{}','{}']\n[llm]\nbackend='command'\nmodel='fixture'\ncommand='/bin/true'\ntimeout_seconds=10\nmax_calls=4\n",
                    fixture.display(), id, review_log.display()
                ),
            )
            .unwrap();
            std::fs::set_permissions(&config_path, std::fs::Permissions::from_mode(0o600)).unwrap();
            let settings = super::super::config::load(Some(&config_path)).unwrap();
            let state = State::lock(dir.join("state")).unwrap().unwrap();
            let mut backend = ReferenceCorrection { calls: 0, correct };
            let report = run(&settings, &state, &mut backend).await;
            assert_eq!(report.status, expected_status, "correct={correct}");
            assert_eq!(backend.calls, if correct { 2 } else { 4 });
            assert_eq!(report.confirmed, usize::from(correct));
            assert_eq!(
                std::fs::read_to_string(&review_log)
                    .unwrap_or_default()
                    .lines()
                    .count(),
                usize::from(correct),
                "invalid review must not reach MCP"
            );
            if !correct {
                assert_eq!(
                    report.block_reason.as_deref(),
                    Some("model_budget_exhausted")
                );
                assert_eq!(report.pending, 1);
                assert!(report.deferred_reviews.is_empty());
                assert!(report
                    .diagnostic
                    .as_ref()
                    .is_some_and(|value| value.detail.contains("declared in this review")));
            } else {
                assert!(report.diagnostic.is_none());
            }
            drop(state);
            std::fs::remove_dir_all(dir).unwrap();
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
