use super::{
    config::RuntimeConfig,
    mcp::{CandidateConflict, Client, McpApplicationError, UndeclaredBeliefCandidate},
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

fn valid_result_selection(args: &Value) -> bool {
    args.get("limit")
        .is_none_or(|value| value.as_u64().is_some_and(|count| count > 0))
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
        "get_lesson_assessment" | "lesson_assessment_history" => {
            input_ensure!(
                args["project"] == project,
                "assessment is outside selected project"
            );
            if name == "lesson_assessment_history" {
                input_ensure!(
                    valid_result_selection(&args),
                    "limit must be positive or omitted for all matches"
                );
                input_ensure!(
                    args.get("offset")
                        .is_none_or(|value| value.as_u64().is_some()),
                    "offset must be nonnegative or omitted"
                );
            }
        }
        "get_experience" | "experience_history" | "get_learning_review" => {
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
            review.validate().map_err(|error| {
                InputRejected(format!(
                    "{error}. {}",
                    super::evidence::guidance(&selected.experience)
                ))
            })?;
            // Source validation needs PostgreSQL-assigned item IDs and resolved
            // assessment keys. The service performs it after allocation, inside
            // the review transaction; the judge forwards the raw keyed input.
            args["review"] = serde_json::to_value(review)?;
        }
        "query_relevant" | "query_learning_context" | "get_contradictions" => {
            input_ensure!(
                args["project"] == project,
                "query is outside selected project"
            );
            if name != "get_contradictions" {
                input_ensure!(
                    valid_result_selection(&args),
                    "limit must be positive or omitted for all matches"
                );
            }
        }
        "get_belief" | "explain_belief" | "query_intervention" => {
            let belief_id = args["id"]
                .as_str()
                .ok_or_else(|| InputRejected("missing belief id".into()))?;
            // Provenance lookup is host-only and not counted as a model tool attempt.
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
                    valid_result_selection(&args),
                    "limit must be positive or omitted for all matches"
                );
                input_ensure!(
                    args.get("offset")
                        .is_none_or(|value| value.as_u64().is_some()),
                    "offset must be nonnegative or omitted"
                );
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
    // A correction is a complete tool outcome of its own. Decode the entire
    // envelope before skipping result-shape checks; a status string alone is
    // not evidence that the server certified no business changes.
    if value.get("status").and_then(Value::as_str) == Some("needs_input") {
        serde_json::from_value::<mimir_core::interaction::NeedsInput>(value.clone())?;
        return Ok(value);
    }
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
                .get("beliefs")
                .ok_or_else(|| anyhow!("belief search result is missing beliefs"))?
                .as_array()
                .ok_or_else(|| anyhow!("invalid belief search result"))?;
            ensure!(
                beliefs
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
                beliefs
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

pub async fn run<B: Backend>(
    settings: &RuntimeConfig,
    state: &State,
    backend: &mut B,
    delivery: notification::Mode<'_>,
) -> Report {
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
        report.failure_detail = Some(format!("{error:#}"));
        report.capture_source(&error);
    }
    finish_report(settings, state, report, delivery).await
}

fn trace(
    state: &State,
    report: &Report,
    selected: &ExperienceState,
    kind: &str,
    (model_used, tool_used): (usize, usize),
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
                    model_used,
                    tool_used,
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
    delivery: notification::Mode<'_>,
) -> Report {
    let mut report = Report::new("blocked", 0, 0, 0, 0, 0);
    report.block_reason = Some(reason.into());
    report.failure_detail = Some(format!("{error:#}"));
    report.capture_source(error);
    finish_report(settings, state, report, delivery).await
}

pub(super) async fn finish_report(
    settings: &RuntimeConfig,
    state: &State,
    mut report: Report,
    delivery: notification::Mode<'_>,
) -> Report {
    report.stamp();
    if let Some(id) = report.diagnostics_id {
        match state.finish_trace(id, &report) {
            Ok(()) if report.status == "complete" => report.diagnostics_id = None,
            Ok(()) => {}
            Err(error) => {
                report.status = "blocked".into();
                report.block_reason = Some("diagnostics_write_error".into());
                report.failure_detail = Some(format!("{error:#}"));
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
    if notification::notify_with(delivery, settings, state, &mut report)
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
    let config_snapshot = super::mcp::PreparedConfig::new(settings, state.path())?;
    let mut client = Client::start(
        &settings.judge.mcp_command,
        &settings.judge.mcp_args,
        config_snapshot.path(),
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
    let mut arguments = json!({});
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
    report.diagnostics_id = Some(state.begin_trace(report, 0).map_err(|error| {
        DiagnosticWriteError(format!("diagnostic trace start failed: {error:#}"))
    })?);
    let mut model_used: usize = 0;
    let mut tool_used: usize = 0;
    let mut failed = false;
    for selected in &batch {
        let mut last: Option<Value> = None;
        let mut candidate_rejections = 0;
        let mut candidate_rejection_detail = None;
        let mut last_rejection: Option<(String, String, Option<SourceFailure>)> = None;
        let mut pending_correction: Option<(String, mimir_core::interaction::NeedsInput)> = None;
        let mut confirmed_review = false;
        loop {
            let will_call_model = backend.will_call_model(selected);
            if will_call_model {
                model_used = model_used.saturating_add(1);
                let detail = last.as_ref().map(Value::to_string);
                trace(
                    state,
                    report,
                    selected,
                    "model_request",
                    (model_used, tool_used),
                    None,
                    detail.as_deref(),
                )?;
            }
            let action = match backend
                .next(selected, last.as_ref(), client.allowed_tools())
                .await
            {
                Ok(action) => action,
                Err(error) => {
                    trace(
                        state,
                        report,
                        selected,
                        "model_error",
                        (model_used, tool_used),
                        None,
                        Some(&format!("{error:#}")),
                    )?;
                    if candidate_rejections == 0 {
                        failed = true;
                        report.block_reason = Some("backend_error".into());
                        report.failure_detail = Some(format!("{error:#}"));
                        report.capture_source(&error);
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
                        (model_used, tool_used),
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
                        (model_used, tool_used),
                        Some(&name),
                        Some(&source.excerpt),
                    )?;
                    tool_used = tool_used.saturating_add(1);
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
                        (model_used, tool_used),
                        Some(&name),
                        Some(&arguments.to_string()),
                    )?;
                    tool_used = tool_used.saturating_add(1);
                    let attempted_review = arguments.get("review").cloned();
                    match scoped_tool(&mut client, selected, &name, arguments).await {
                        Ok(value) => {
                            if value.get("status").and_then(Value::as_str) == Some("needs_input") {
                                let correction: mimir_core::interaction::NeedsInput =
                                    serde_json::from_value(value.clone())?;
                                trace(
                                    state,
                                    report,
                                    selected,
                                    "tool_correction",
                                    (model_used, tool_used),
                                    Some(&name),
                                    Some(&value.to_string()),
                                )?;
                                pending_correction = Some((name, correction));
                                last = Some(value);
                                continue;
                            }
                            if pending_correction
                                .as_ref()
                                .is_some_and(|(tool, _)| tool == &name)
                            {
                                pending_correction = None;
                            }
                            trace(
                                state,
                                report,
                                selected,
                                "tool_result",
                                (model_used, tool_used),
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
                                (model_used, tool_used),
                                Some(&name),
                                Some(&format!("{error:#}")),
                            )?;
                            candidate_rejections += 1;
                            candidate_rejection_detail = Some(format!("{error:#}"));
                            last = Some(json!({"error":"candidate_key_conflict",
                                "guidance":"A candidate key from an earlier review has a different declaration. Inspect experience_history. Reuse a key only with its exact original kind and declaration; use a new key for a revised claim."}));
                        }
                        Err(error)
                            if error.downcast_ref::<InputRejected>().is_some()
                                || error.downcast_ref::<McpApplicationError>().is_some()
                                || error.downcast_ref::<UndeclaredBeliefCandidate>().is_some()
                                || error
                                    .downcast_ref::<mimir_core::validation::Refusal>()
                                    .is_some()
                                || error.downcast_ref::<SourceFailure>().is_some_and(
                                    |source| source.stage == "invalid review arguments",
                                ) =>
                        {
                            trace(
                                state,
                                report,
                                selected,
                                "tool_rejection",
                                (model_used, tool_used),
                                Some(&name),
                                Some(&format!("{error:#}")),
                            )?;
                            // Only typed validation faults are correction feedback.
                            // Preserve the exact path, code and explanation.
                            let fault = error
                                .downcast_ref::<McpApplicationError>()
                                .map(|e| &e.0)
                                .or_else(|| {
                                    error
                                        .downcast_ref::<UndeclaredBeliefCandidate>()
                                        .map(|e| &e.0)
                                })
                                .or_else(|| {
                                    error
                                        .downcast_ref::<mimir_core::validation::Refusal>()
                                        .map(|e| &e.fault)
                                });
                            let message = if let Some(input) = error.downcast_ref::<InputRejected>()
                            {
                                input.to_string()
                            } else if let Some(source) = error.downcast_ref::<SourceFailure>() {
                                source.detail.clone()
                            } else if let Some(fault) = fault {
                                fault.message.clone()
                            } else {
                                unreachable!("only classified validation failures reach correction")
                            };
                            last = Some(json!({"error":"invalid_tool_arguments",
                                "message":message,
                                "fault":fault,
                                "guidance":"Correct the tool arguments and resubmit the request. The rejected call changed nothing."}));
                            let focused = fault.and_then(|fault| {
                                use mimir_core::validation::{Code, Segment};
                                if fault.code != Code::QuotationMismatch { return None; }
                                let index = fault.path.iter().find_map(|part| match part { Segment::Index(n)=>Some(*n), _=>None })?;
                                let item = attempted_review.as_ref()?.get("extracted_items")?.get(index)?;
                                let source_ref = item.get("source_ref")?.as_str()?;
                                let source = selected.experience.source_records.iter().find(|s|s.source_ref==source_ref)?;
                                let payload = json!({"fault":fault,"rejected_item":item,"cited_source":source}).to_string();
                                Some(SourceFailure::input("quotation_mismatch",payload.as_bytes(),&fault.message))
                            });
                            last_rejection = Some((
                                name,
                                format!("{error:#}"),
                                focused.or_else(|| error.downcast_ref::<SourceFailure>().cloned()),
                            ));
                        }
                        Err(error) => {
                            trace(
                                state,
                                report,
                                selected,
                                "tool_error",
                                (model_used, tool_used),
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
            if let Some((name, correction)) = pending_correction {
                if report.block_reason.is_none() {
                    report.block_reason = Some("needs_input".into());
                }
                if report.diagnostic.is_none() {
                    report.diagnostic = Some(FailureDiagnostic::new(
                        selected.experience.id,
                        &name,
                        &serde_json::to_string(&correction)?,
                    ));
                }
            }
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
    #[allow(dead_code)] // Shared guard also serves integration-test crates.
    mod isolation {
        include!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../tests/support/isolation.rs"
        ));
    }
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
    async fn scoped_result_selection_accepts_omission_and_large_counts_without_a_judge_ceiling(
    ) -> Result<()> {
        let fixture = isolation::fixture();
        let config = Config::load_from_path(&fixture.root.join("config.toml"))?;
        fixture.assert_database(&config.database);
        let service = MimirService::connect(&config).await?;
        let db = mimir_core::db::connect(&config.database).await?;
        let id: Uuid = db.query_one("SELECT gen_random_uuid()", &[]).await?.get(0);
        let project = format!("judge-selection-{id}");
        let belief = isolation::seed_belief_in_project(
            "judge selection fixture",
            0.5,
            0.1,
            &project,
            mimir_core::graph::MemoryType::Fact,
        )
        .await?;
        let source = Experience {
            id,
            project: project.clone(),
            context: "selection fixture".into(),
            action: "honor explicit selection".into(),
            outcome: Outcome::Unknown,
            source: ObservationSource::AgentReport,
            evidence: vec![],
            belief_ids: vec![belief.id],
            pattern_id: None,
            learning_items: vec![],
            source_records: vec![],
        };
        let selected = service.record_experience(&source, 0).await?;
        let mut client =
            Client::start(&fixture.mcp, &[], &fixture.root.join("config.toml")).await?;
        let checked=async {
            for (name,base) in [
                ("query_relevant",json!({"context":"judge selection fixture","project":project})),
                ("query_learning_context",json!({"context":"judge selection fixture","project":project})),
                ("explain_belief",json!({"id":belief.id})),
                ("lesson_assessment_history",json!({"project":project,"belief_id":belief.id,"scope":"fixture","rubric":"fixture"})),
            ] {
                for limit in [None,Some(21),Some(u64::MAX)] {
                    let mut args=base.clone();if let Some(limit)=limit {args["limit"]=json!(limit);}
                    let result=scoped_tool(&mut client,&selected,name,args).await?;
                    ensure!(result["status"]!="needs_input","valid selection refused: {result}");
                }
                for limit in [json!(0),json!(-1),json!("all"),json!(null)] {
                    let mut args=base.clone();args["limit"]=limit;
                    ensure!(scoped_tool(&mut client,&selected,name,args).await.unwrap_err().is::<InputRejected>());
                }
            }
            Ok::<_,anyhow::Error>(())
        }.await;
        drop(client);
        let cleanup = service.delete_project(&project).await;
        checked?;
        cleanup?;
        Ok(())
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
                if !self.correct && self.calls == 4 {
                    return Ok(Action::Done);
                }
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
                if self.calls == 26 {
                    return Ok(Action::Done);
                }
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
                if matches!(self.case, RejectionCase::Exhausted) && self.calls == 26 {
                    return Ok(Action::Done);
                }
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
    async fn keyed_extractions_reach_mcp_before_postgres_allocation() {
        use std::os::unix::fs::PermissionsExt;

        let fixture = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src/judge/retry_fixture.sh");
        let dir = std::env::temp_dir().join(format!("mimir-judge-keyed-review-{}", Uuid::new_v4()));
        std::fs::create_dir(&dir).unwrap();
        std::fs::set_permissions(&dir, std::fs::Permissions::from_mode(0o700)).unwrap();
        let request_log = dir.join("requests.jsonl");
        let id = Uuid::new_v4();
        let selected: ExperienceState = serde_json::from_value(json!({
            "experience": {
                "id": id, "project": "judge-retry-fixture", "context": "fixture observation",
                "action": "review the suggestion", "outcome": "unknown", "source": "user_feedback",
                "evidence": ["fixture-source"],
                "source_records": [{
                    "source_ref": "fixture-source", "actor": "user", "provenance": "user_feedback",
                    "text": "Try a smaller batch."
                }]
            },
            "revision": 1, "review_revision": 0, "reviewed_revision": 0
        }))
        .unwrap();
        let arguments = json!({
            "expected_review_revision": 0,
            "review": {
                "experience_id": id, "experience_revision": 1, "reviewer": "model-selected",
                "rationale": "review the recorded suggestion",
                "candidates": [{"kind": "belief", "key": "lesson", "content": "A smaller batch may help."}],
                "extracted_items": [{
                    "key": "smaller-batch", "kind": "suggestion", "source_ref": "fixture-source",
                    "actor": "user", "statement": "Try a smaller batch.", "conditions": "fixture observation"
                }],
                "assessments": [{
                    "target": {"candidate_key": "lesson"}, "scope": "fixture", "rubric": "fixture",
                    "correctness": {"value": null, "weight": 0},
                    "usefulness": {"value": null, "weight": 0},
                    "evidence_indices": [0], "item_keys": ["smaller-batch"], "rationale": "not tried yet"
                }],
                "source_coverage": [{"source_ref": "fixture-source", "status": "complete", "reason": "suggestion extracted"}]
            }
        });
        let mut client = Client::start(
            "bash",
            &[
                fixture.display().to_string(),
                id.to_string(),
                String::new(),
                String::new(),
                request_log.display().to_string(),
            ],
            &dir.join("unused-config.toml"),
        )
        .await
        .unwrap();

        for path in [
            "expected_review_revision",
            "experience_revision",
            "experience_id",
            "key",
        ] {
            let mut invalid = arguments.clone();
            match path {
                "expected_review_revision" => invalid[path] = json!(1),
                "experience_revision" => invalid["review"][path] = json!(2),
                "experience_id" => invalid["review"][path] = json!(Uuid::new_v4()),
                _ => {
                    invalid["review"]["extracted_items"][0]
                        .as_object_mut()
                        .unwrap()
                        .remove("key")
                        .unwrap();
                }
            }
            assert!(
                scoped_tool(&mut client, &selected, "review_experience", invalid)
                    .await
                    .is_err(),
                "{path}"
            );
        }

        scoped_tool(
            &mut client,
            &selected,
            "review_experience",
            arguments.clone(),
        )
        .await
        .expect("key-only extracted items must reach PostgreSQL allocation");
        let requests: Vec<Value> = std::fs::read_to_string(&request_log)
            .unwrap()
            .lines()
            .map(|line| serde_json::from_str::<Value>(line).unwrap())
            .filter(|request| request["params"]["name"] == "review_experience")
            .collect();
        assert_eq!(
            requests.len(),
            1,
            "invalid requests must remain local refusals"
        );
        let forwarded = &requests[0]["params"]["arguments"]["review"];
        assert_eq!(forwarded["reviewer"], "mimir-judge");
        assert!(forwarded["extracted_items"][0].get("id").is_none());
        assert_eq!(forwarded["extracted_items"][0]["key"], "smaller-batch");
        assert_eq!(
            forwarded["assessments"][0]["item_keys"],
            json!(["smaller-batch"])
        );
        drop(client);
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[tokio::test]
    async fn invalid_tool_requests_remain_correctable_until_backend_stops() {
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
                    "config_version=1\n[logging]\ndirectory='{}'\n[database]\nhost='127.0.0.1'\nport=1\ndbname='unused'\nuser='unused'\n[judge]\nproject='judge-retry-fixture'\nmcp_command='bash'\nmcp_args=['{}','{}']\n[llm]\nbackend='command'\nmodel='fixture'\ncommand='/bin/true'\n",
                    dir.join("logs").display(), fixture.display(), id
                ),
            )
            .unwrap();
            std::fs::set_permissions(&config_path, std::fs::Permissions::from_mode(0o600)).unwrap();
            let settings = super::super::config::load(Some(&config_path)).unwrap();
            let state = State::lock(dir.join("state")).unwrap().unwrap();
            let mut backend = ToolCorrection { case, calls: 0 };
            let report = run(
                &settings,
                &state,
                &mut backend,
                notification::Mode::Standalone,
            )
            .await;
            if matches!(case, RejectionCase::Exhausted) {
                assert_eq!(report.status, "blocked");
                assert_eq!(backend.calls, 26);
                assert_eq!(report.block_reason.as_deref(), Some("tool_rejected"));
                assert_eq!(
                    report.failure_source.as_ref().unwrap().excerpt,
                    "{\"review\": }"
                );
            } else if matches!(case, RejectionCase::MimirError) {
                assert_eq!(report.status, "blocked");
                assert_eq!(
                    backend.calls, 1,
                    "unclassified database failures are not argument-correction feedback"
                );
                assert_eq!(report.block_reason.as_deref(), Some("tool_error"));
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
    async fn requests_beyond_old_budget_are_counted_and_pending_review_keeps_trace() {
        use std::os::unix::fs::PermissionsExt;

        let fixture = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src/judge/retry_fixture.sh");
        let dir = std::env::temp_dir().join(format!("mimir-judge-budget-trace-{}", Uuid::new_v4()));
        std::fs::create_dir(&dir).unwrap();
        std::fs::set_permissions(&dir, std::fs::Permissions::from_mode(0o700)).unwrap();
        let config_path = dir.join("config.toml");
        std::fs::write(
            &config_path,
            format!(
                "config_version=1\n[logging]\ndirectory='{}'\n[database]\nhost='127.0.0.1'\nport=1\ndbname='unused'\nuser='unused'\n[judge]\nproject='judge-retry-fixture'\nmcp_command='bash'\nmcp_args=['{}','{}']\n[llm]\nbackend='command'\nmodel='fixture'\ncommand='/bin/true'\n",
                dir.join("logs").display(), fixture.display(), Uuid::new_v4()
            ),
        )
        .unwrap();
        std::fs::set_permissions(&config_path, std::fs::Permissions::from_mode(0o600)).unwrap();
        let settings = super::super::config::load(Some(&config_path)).unwrap();
        let state = State::lock(dir.join("state")).unwrap().unwrap();
        let mut backend = NoReview { calls: 0 };
        let failed = run(
            &settings,
            &state,
            &mut backend,
            notification::Mode::Standalone,
        )
        .await;
        assert_eq!(failed.status, "blocked");
        assert_eq!(
            failed.block_reason.as_deref(),
            Some("revision_not_confirmed")
        );
        assert!(failed.diagnostic.is_none());
        assert_eq!(backend.calls, 26);
        let id = failed.diagnostics_id.unwrap();
        let diagnostics = state::read_diagnostics(state.path()).unwrap();
        let trace = diagnostics
            .attempts
            .iter()
            .find(|trace| trace.id == id)
            .unwrap();
        assert_eq!(trace.model_requests, Some(26));
        assert_eq!(trace.tool_attempts, Some(25));
        assert!(trace
            .events
            .iter()
            .any(|event| event.kind == "model_request"));
        assert!(trace.events.iter().any(|event| event.kind == "tool_result"));
        assert_eq!(trace.events_omitted, 0, "retain every diagnostic event");
        assert_eq!(
            trace
                .events
                .iter()
                .filter(|event| event.kind == "model_request")
                .count(),
            26
        );
        assert_eq!(
            trace
                .events
                .iter()
                .filter(|event| event.kind == "tool_request")
                .count(),
            25
        );
        assert_eq!(
            trace
                .events
                .iter()
                .filter(|event| event.kind == "tool_result")
                .count(),
            25
        );
        assert_eq!(trace.events[1].tool.as_deref(), Some("get_experience"));
        let mut recovery = ToolCorrection {
            case: RejectionCase::LocalValidation,
            calls: 0,
        };
        let completed = run(
            &settings,
            &state,
            &mut recovery,
            notification::Mode::Standalone,
        )
        .await;
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
                    "config_version=1\n[logging]\ndirectory='{}'\n[database]\nhost='127.0.0.1'\nport=1\ndbname='unused'\nuser='unused'\n[judge]\nproject='judge-retry-fixture'\nmcp_command='bash'\nmcp_args=['{}','{}','{}']\n[llm]\nbackend='command'\nmodel='fixture'\ncommand='/bin/true'\n",
                    dir.join("logs").display(), fixture.display(), id, review_log.display()
                ),
            )
            .unwrap();
            std::fs::set_permissions(&config_path, std::fs::Permissions::from_mode(0o600)).unwrap();
            let settings = super::super::config::load(Some(&config_path)).unwrap();
            let state = State::lock(dir.join("state")).unwrap().unwrap();
            let mut backend = ReferenceCorrection { calls: 0, correct };
            let report = run(
                &settings,
                &state,
                &mut backend,
                notification::Mode::Standalone,
            )
            .await;
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
                assert_eq!(report.block_reason.as_deref(), Some("tool_rejected"));
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
    async fn normal_correction_result_remains_in_the_judge_dialogue() -> Result<()> {
        struct CorrectQuery {
            step: usize,
        }
        impl Backend for CorrectQuery {
            fn next<'a>(
                &'a mut self,
                selected: &'a ExperienceState,
                last: Option<&'a Value>,
                _tools: &'a [Value],
            ) -> Pin<Box<dyn Future<Output = Result<Action>> + Send + 'a>> {
                Box::pin(async move {
                    let action = match self.step {
                        0 => Action::Tool {
                            name: "query_learning_context".into(),
                            arguments: json!({"context":"check this source","project":selected.experience.project,"limit":1,"limt":1}),
                        },
                        1 => {
                            let value =
                                last.ok_or_else(|| anyhow!("missing correction feedback"))?;
                            let correction: mimir_core::interaction::NeedsInput =
                                serde_json::from_value(value.clone())?;
                            ensure!(
                                correction.issues().iter().any(|item| item.fault().path
                                    == vec![mimir_core::validation::Segment::Key("limt".into())]),
                                "correction lost its exact path"
                            );
                            Action::Tool {
                                name: "query_learning_context".into(),
                                arguments: json!({"context":"check this source","project":selected.experience.project,"limit":1}),
                            }
                        }
                        2 => {
                            let value =
                                last.ok_or_else(|| anyhow!("missing corrected query response"))?;
                            ensure!(
                                value["beliefs"].is_array() && value["patterns"].is_array(),
                                "corrected query did not execute"
                            );
                            Action::Tool {
                                name: "review_experience".into(),
                                arguments: json!({
                                "expected_review_revision":selected.review_revision,"review":{
                                    "experience_id":selected.experience.id,"experience_revision":selected.revision,
                                    "reviewer":"fixture","rationale":"corrected the query before completing review"}}),
                            }
                        }
                        _ => bail!("completed review should have been observed"),
                    };
                    self.step += 1;
                    Ok(action)
                })
            }
        }
        let fixture = isolation::fixture();
        let mut settings = super::super::config::load(Some(&fixture.root.join("config.toml")))?;
        let project = format!("judge-correction-{}", Uuid::new_v4());
        settings.judge.project = Some(project.clone());
        settings.judge.mcp_command = fixture.mcp.clone();
        let core = Config::load_from_path(&settings.path)?;
        fixture.assert_database(&core.database);
        let service = MimirService::connect(&core).await?;
        let allocated = mimir_core::db::connect(&core.database)
            .await?
            .query_one("SELECT gen_random_uuid()", &[])
            .await?;
        let source = Experience {
            id: allocated.get(0),
            project: project.clone(),
            context: "check this source".into(),
            action: "repair a misspelled request field".into(),
            outcome: Outcome::Success,
            source: ObservationSource::ToolResult,
            evidence: vec!["owned correction fixture".into()],
            belief_ids: vec![],
            pattern_id: None,
            learning_items: vec![],
            source_records: vec![],
        };
        service.record_experience(&source, 0).await?;
        let directory = super::super::harness::RunDir::new_in(&std::env::temp_dir())?;
        let state = State::lock(directory.path().join("state"))?.unwrap();
        let mut backend = CorrectQuery { step: 0 };
        let report = run(
            &settings,
            &state,
            &mut backend,
            notification::Mode::Standalone,
        )
        .await;
        service.delete_project(&project).await?;
        ensure!(
            report.status == "complete" && report.confirmed == 1 && report.pending == 0,
            "correction became a failed review: {} {:?} {:?}",
            report.status,
            report.block_reason,
            report
                .diagnostic
                .as_ref()
                .map(|value| value.detail.as_str())
        );
        ensure!(
            backend.step == 3,
            "judge did not finish the actual correction dialogue"
        );
        Ok(())
    }

    #[tokio::test]
    async fn unresolved_preparation_keeps_its_dialogue_and_other_reviews_continue() -> Result<()> {
        struct PendingOne {
            blocked: Uuid,
        }
        impl Backend for PendingOne {
            fn next<'a>(
                &'a mut self,
                selected: &'a ExperienceState,
                last: Option<&'a Value>,
                _tools: &'a [Value],
            ) -> Pin<Box<dyn Future<Output = Result<Action>> + Send + 'a>> {
                Box::pin(async move {
                    if let Some(value) = last {
                        let correction: mimir_core::interaction::NeedsInput =
                            serde_json::from_value(value.clone())?;
                        ensure!(correction.issues()[0]
                            .suggested_correction()
                            .contains("Open a dialog"));
                        return Ok(Action::Done);
                    }
                    let mut review = json!({"experience_id":selected.experience.id,"experience_revision":selected.revision,
                        "reviewer":"fixture","rationale":"other work must continue while a prerequisite awaits the user"});
                    if selected.experience.id == self.blocked {
                        review["candidates"] = json!([{"kind":"belief","key":"needs-support","content":"requires configured embedding and indexed support"}]);
                    }
                    Ok(Action::Tool {
                        name: "review_experience".into(),
                        arguments: json!({
                        "expected_review_revision":selected.review_revision,"review":review}),
                    })
                })
            }
        }
        let fixture = isolation::fixture();
        let mut settings = super::super::config::load(Some(&fixture.root.join("config.toml")))?;
        let project = format!("judge-pending-decision-{}", Uuid::new_v4());
        settings.judge.project = Some(project.clone());
        settings.judge.mcp_command = fixture.mcp.clone();
        let core = Config::load_from_path(&settings.path)?;
        fixture.assert_database(&core.database);
        let service = MimirService::connect(&core).await?;
        let client = mimir_core::db::connect(&core.database).await?;
        let mut ids = Vec::new();
        for _ in 0..2 {
            let id: Uuid = client
                .query_one("SELECT gen_random_uuid()", &[])
                .await?
                .get(0);
            service
                .record_experience(
                    &Experience {
                        id,
                        project: project.clone(),
                        context: "await the required user decision".into(),
                        action: "keep other review work moving".into(),
                        outcome: Outcome::Success,
                        source: ObservationSource::ToolResult,
                        evidence: vec!["owned fixture receipt".into()],
                        belief_ids: vec![],
                        pattern_id: None,
                        learning_items: vec![],
                        source_records: vec![],
                    },
                    0,
                )
                .await?;
            ids.push(id);
        }
        let directory = super::super::harness::RunDir::new_in(&std::env::temp_dir())?;
        let state = State::lock(directory.path().join("state"))?.unwrap();
        let report = run(
            &settings,
            &state,
            &mut PendingOne { blocked: ids[0] },
            notification::Mode::Standalone,
        )
        .await;
        ensure!(
            report.status == "partial" && report.confirmed == 1 && report.pending == 1,
            "decision stopped other work: {} {:?}",
            report.status,
            report.block_reason
        );
        ensure!(
            report.block_reason.as_deref() == Some("needs_input"),
            "decision was classified as a tool failure"
        );
        let diagnostic = report
            .diagnostic
            .as_ref()
            .ok_or_else(|| anyhow!("user decision was discarded"))?;
        ensure!(diagnostic.experience_id == ids[0]);
        let correction: mimir_core::interaction::NeedsInput =
            serde_json::from_str(&diagnostic.detail)?;
        ensure!(correction.issues()[0]
            .fault()
            .message
            .contains("candidate needs-support"));
        ensure!(
            service
                .get_experience(ids[0])
                .await?
                .unwrap()
                .reviewed_revision
                == 0
        );
        ensure!(
            service
                .get_experience(ids[1])
                .await?
                .unwrap()
                .reviewed_revision
                == 1
        );
        ensure!(service.list_beliefs(Some(&project)).await?.is_empty());
        service.delete_project(&project).await?;
        Ok(())
    }

    #[tokio::test]
    async fn isolated_judge_reviews_every_pending_experience_in_one_run() -> Result<()> {
        struct ReviewEach;
        impl Backend for ReviewEach {
            fn next<'a>(
                &'a mut self,
                selected: &'a ExperienceState,
                last: Option<&'a Value>,
                _tools: &'a [Value],
            ) -> Pin<Box<dyn Future<Output = Result<Action>> + Send + 'a>> {
                Box::pin(async move {
                    if last.is_some() {
                        return Ok(Action::Done);
                    }
                    Ok(Action::Tool {
                        name: "review_experience".into(),
                        arguments: json!({"expected_review_revision":selected.review_revision,
                            "review":{"experience_id":selected.experience.id,
                                "experience_revision":selected.revision,"reviewer":"fixture",
                                "rationale":"review each owned fixture source"}}),
                    })
                })
            }
        }
        let fixture = isolation::fixture();
        let mut settings = super::super::config::load(Some(&fixture.root.join("config.toml")))?;
        let project = format!("all-judge-work-{}", Uuid::new_v4());
        settings.judge.project = Some(project.clone());
        settings.judge.mcp_command = fixture.mcp.clone();
        let core = Config::load_from_path(&settings.path)?;
        fixture.assert_database(&core.database);
        let service = MimirService::connect(&core).await?;
        let work = super::super::harness::RunDir::new_in(&std::env::temp_dir())?;
        let state = State::lock(work.path().join("state"))?.unwrap();
        let result = async {
            for _ in 0..12 {
                service
                    .record_experience(
                        &Experience {
                            id: Uuid::new_v4(),
                            project: project.clone(),
                            context: "complete selection".into(),
                            action: "verify all reviews in one run".into(),
                            outcome: Outcome::Success,
                            source: ObservationSource::ToolResult,
                            evidence: vec!["owned fixture receipt".into()],
                            belief_ids: vec![],
                            pattern_id: None,
                            learning_items: vec![],
                            source_records: vec![],
                        },
                        0,
                    )
                    .await?;
            }
            let report = run(
                &settings,
                &state,
                &mut ReviewEach,
                notification::Mode::Standalone,
            )
            .await;
            ensure!(
                report.status == "complete",
                "{}: {:?}",
                report.status,
                report.failure_detail
            );
            ensure!(
                report.selected == 12 && report.confirmed == 12 && report.pending == 0,
                "selection/review totals: {}/{}/{}",
                report.selected,
                report.confirmed,
                report.pending
            );
            ensure!(
                service
                    .pending_experiences(Some(&project), None)
                    .await?
                    .is_empty(),
                "unreviewed fixture work remains"
            );
            Ok(())
        }
        .await;
        service.delete_project(&project).await?;
        result
    }

    #[tokio::test]
    async fn isolated_mcp_review_cycle() {
        let fixture = isolation::fixture();
        let path = fixture.root.join("config.toml");
        let binary = fixture.mcp.clone();
        let project = format!("step5-{}", Uuid::new_v4());
        let mut settings = super::super::config::load(Some(&path)).unwrap();
        settings.judge.project = Some(project.clone());
        settings.judge.mcp_command = binary;
        let core = Config::load_from_path(&settings.path).unwrap();
        fixture.assert_database(&core.database);
        let service = Arc::new(MimirService::connect(&core).await.unwrap());
        let state_path = fixture
            .root
            .join(format!("runner-state-{}", Uuid::new_v4()));
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
            learning_items: vec![],
            source_records: vec![],
        };
        let e = make_experience();
        service.record_experience(&e, 0).await.unwrap();
        let mut fake = Fake {
            mode: Mode::Review,
            calls: 0,
            service: service.clone(),
        };
        let success = run(&settings, &state, &mut fake, notification::Mode::Standalone).await;
        assert_eq!(success.status, "complete");
        assert_eq!(success.confirmed, 1);
        assert_eq!(fake.calls, 1);
        let committed = service.get_experience(e.id).await.unwrap().unwrap();
        assert_eq!(committed.reviewed_revision, 1);
        let history = service.experience_history(e.id).await.unwrap();
        assert_eq!(history["reviews"][0]["payload"]["reviewer"], "mimir-judge");
        fake.calls = 0;
        let idle = run(&settings, &state, &mut fake, notification::Mode::Standalone).await;
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
        let correction = run(&settings, &state, &mut fake, notification::Mode::Standalone).await;
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
            let report = run(
                &settings,
                &state,
                &mut backend,
                notification::Mode::Standalone,
            )
            .await;
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
                assessments: vec![],
                extracted_items: vec![],
                source_coverage: vec![],
            };
            service
                .review_experience(&review, latest.review_revision)
                .await
                .unwrap();
        }
        let first = make_experience();
        let second = make_experience();
        service.record_experience(&first, 0).await.unwrap();
        service.record_experience(&second, 0).await.unwrap();
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let port = listener.local_addr().unwrap().port();
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
        };
        let mut partial = Fake {
            mode: Mode::Partial,
            calls: 0,
            service: service.clone(),
        };
        let report = run(
            &settings,
            &state,
            &mut partial,
            notification::Mode::Standalone,
        )
        .await;
        assert_eq!(report.status, "partial");
        assert_eq!(report.confirmed, 1);
        assert_eq!(report.pending, 1);
        assert_eq!(report.notification, "queued");
        let incoming = mimir_notifications::IncomingEvents::new(&state_path).unwrap();
        let consumer = incoming.claim().unwrap();
        assert!(
            consumer.front().unwrap().is_some(),
            "mail must remain durably queued for its watcher"
        );
        assert!(
            std::future::poll_fn(|cx| std::task::Poll::Ready(
                listener.poll_accept(cx).is_pending()
            ))
            .await,
            "standalone review must not wait on SMTP"
        );
        drop(consumer);
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
        service.delete_project(&project).await.unwrap();
        drop(state);
        std::fs::remove_dir_all(state_path).unwrap();
    }
}
