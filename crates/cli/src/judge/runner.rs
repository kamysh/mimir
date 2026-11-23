use super::{
    config::RuntimeConfig,
    mcp::{CandidateConflict, Client, McpApplicationError, UndeclaredBeliefCandidate},
    notification, repair,
    state::{self, DeferredReview, FailureDiagnostic, RepairCase, Report, SourceFailure, State},
};
use anyhow::{anyhow, bail, ensure, Result};
use mimir_core::learning::{ExperienceState, Review};
use mimir_core::validation::{Code, Fault, Refusal, RefusalKind, Segment};
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
        "get_lesson_assessment" | "lesson_assessment_history" => {
            input_ensure!(
                args["project"] == project,
                "assessment is outside selected project"
            );
            if name == "lesson_assessment_history" {
                let limit = args["limit"].as_u64().unwrap_or(20);
                input_ensure!(limit > 0, "history limit must be positive");
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
                if error.is::<Refusal>() {
                    return error;
                }
                InputRejected(format!(
                    "{error}. {}",
                    super::evidence::guidance(&selected.experience)
                ))
                .into()
            })?;
            // Source validation needs PostgreSQL-assigned item IDs and resolved
            // assessment keys. The service performs it after allocation, inside
            // the review transaction; the judge forwards the raw keyed input.
            args["review"] = serde_json::to_value(review)?;
        }
        "query_relevant" | "query_learning_context" | "query_document" | "get_contradictions" => {
            input_ensure!(
                args["project"] == project,
                "query is outside selected project"
            );
            if name != "get_contradictions" && args.get("limit").is_some() {
                input_ensure!(
                    args["limit"].as_u64().is_some_and(|limit| limit > 0),
                    "query limit must be positive when supplied; omit it to request all matches"
                );
            }
        }
        "get_belief" | "explain_belief" | "query_intervention" => {
            let belief_id = args["id"]
                .as_str()
                .ok_or_else(|| InputRejected("missing belief id".into()))?;
            // Provenance lookup is host-only and not counted as a model tool attempt.
            let _: Uuid = belief_id
                .parse()
                .map_err(|_| InputRejected("invalid belief id".into()))?;
            let source = client.tool("get_belief", json!({"id":belief_id})).await?;
            if name == "get_belief" {
                input_ensure!(
                    !source.is_null()
                        && (source["project"] == project || source["project"].is_null()),
                    "belief is outside selected project"
                );
                return Ok(source);
            }
            if source["project"] != project {
                return Err(Refusal::invalid(
                    Code::WrongIdentity,
                    vec![Segment::Key("id".into())],
                    format!("Use a belief from the selected project for explanations or interventions. Belief {belief_id} cannot be used here. Global beliefs can be read with get_belief."),
                ).into());
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
    if matches!(
        value["status"].as_str(),
        Some("needs_input" | "needs_correction")
    ) {
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
            // Current servers return the retrieval report (context, beliefs,
            // semantic_search); a bare array is accepted from older servers.
            let beliefs = if value.is_array() {
                value.as_array().unwrap()
            } else {
                value["beliefs"]
                    .as_array()
                    .ok_or_else(|| anyhow!("invalid belief search result"))?
            };
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

pub(super) async fn observe(
    client: &mut Client,
    selected: &ExperienceState,
) -> Result<&'static str> {
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

#[cfg(test)]
pub async fn run<B: Backend>(settings: &RuntimeConfig, state: &State, backend: &mut B) -> Report {
    run_selected(settings, state, backend, None).await
}

pub(super) async fn run_selected<B: Backend>(
    settings: &RuntimeConfig,
    state: &State,
    backend: &mut B,
    target: Option<ExperienceState>,
) -> Report {
    run_queued(
        settings,
        state,
        backend,
        target,
        &mut super::transcript::Pending::default(),
    )
    .await
}

pub(super) async fn run_queued<B: Backend>(
    settings: &RuntimeConfig,
    state: &State,
    backend: &mut B,
    target: Option<ExperienceState>,
    queue: &mut super::transcript::Pending,
) -> Report {
    let mut report = Report::new("blocked", 0, 0, 0, 0, 0);
    let notify = target.is_none();
    let mut attempts = std::collections::HashMap::new();
    let result = run_inner(settings, state, backend, &mut report, target, &mut attempts).await;
    if let Err(error) = result {
        report.block_reason = Some("mcp_or_configuration_error".into());
        report.failure_detail = Some(format!("{error:#}"));
        report.capture_source(&error);
        if report.selected == 0 {
            report.preserve_deferrals(state.path());
        }
    }
    queue.extend(&settings.core.database, attempts.into_values());
    queue.flush(&settings.core.database, &mut report).await;
    finish_report(settings, state, report, notify).await
}

pub async fn setup_failure(
    settings: &RuntimeConfig,
    state: &State,
    reason: &str,
    error: &anyhow::Error,
) -> Report {
    let mut report = Report::new("blocked", 0, 0, 0, 0, 0);
    report.block_reason = Some(reason.into());
    report.failure_detail = Some(format!("{error:#}"));
    report.capture_source(error);
    report.preserve_deferrals(state.path());
    finish_report(settings, state, report, true).await
}

async fn finish_report(
    settings: &RuntimeConfig,
    state: &State,
    mut report: Report,
    notify: bool,
) -> Report {
    report.stamp();
    if let Err(error) = state.record_incident(&report) {
        eprintln!("Cannot save the failure incident; review result is unchanged: {error:#}");
    }
    if let Err(error) = state.write(&report) {
        eprintln!("Cannot save the local review report: {error:#}");
    }
    if notify && notification::enqueue(settings, state, &mut report).is_err() {
        report.notification = "unavailable".into();
    }
    if let Err(error) = state.write(&report) {
        eprintln!("Cannot save the local review report: {error:#}");
    }
    report
}

async fn run_inner<B: Backend>(
    settings: &RuntimeConfig,
    state: &State,
    backend: &mut B,
    report: &mut Report,
    target: Option<ExperienceState>,
    attempts: &mut std::collections::HashMap<Uuid, super::transcript::Attempt>,
) -> Result<()> {
    let mut client = Client::start(
        &settings.judge.mcp_command,
        &settings.judge.mcp_args,
        &settings.path,
    )
    .await?;
    // A rejected source revision is held until it is corrected or reviewed by
    // another caller. Reconcile against the database before excluding it.
    // Spec (Mimir.DeferredReviews.ListValid): the retained list is bounded,
    // its revisions are valid, and no identity appears twice.
    let carried = state::read(state.path())?
        .filter(|previous| previous.guided_repair && target.is_none())
        .into_iter()
        .flat_map(|report| report.deferred_reviews)
        .collect::<Vec<_>>();
    {
        let mut ids = std::collections::HashSet::new();
        for item in &carried {
            ensure!(item.revision > 0, "invalid deferred review revision");
            ensure!(ids.insert(item.id), "duplicate deferred review");
        }
    }
    for deferred in carried {
        let current = client
            .tool("get_experience", json!({"id":deferred.id}))
            .await?;
        if current.is_null() {
            continue;
        }
        let current = parse_state(current)?;
        // Spec (Mimir.DeferredReviews.checkIdentity): the deferred lookup
        // must return the same experience, not merely matching revisions.
        ensure!(
            current.experience.id == deferred.id,
            "deferred lookup returned another experience"
        );
        let in_scope = settings
            .judge
            .project
            .as_ref()
            .is_none_or(|project| *project == current.experience.project);
        if in_scope {
            if still_deferred(&deferred, current.revision, current.reviewed_revision) {
                report.deferred_reviews.push(deferred);
            } else if deferred.repair.is_some()
                && current.revision == deferred.revision
                && current.reviewed_revision == deferred.revision
            {
                if let Err(error) =
                    notification::review_recovered(settings, state.path(), &deferred)
                {
                    eprintln!("Cannot queue the review recovery notice: {error:#}");
                    report.deferred_reviews.push(deferred);
                }
            }
        }
    }
    let mut arguments = json!({});
    if let Some(count) = settings.judge.batch_size {
        arguments["limit"] = json!(count);
    }
    arguments["exclude_ids"] = json!(report
        .deferred_reviews
        .iter()
        .map(|item| item.id)
        .collect::<Vec<_>>());
    if let Some(project) = &settings.judge.project {
        arguments["project"] = json!(project);
    }
    let batch: Vec<ExperienceState> = match target {
        Some(selected) => vec![selected],
        None => {
            let fetched = client.tool("pending_experiences", arguments).await?;
            serde_json::from_value(fetched.clone()).map_err(|error| {
                state::SourceFailure::json(
                    "invalid pending batch",
                    fetched.to_string().as_bytes(),
                    error,
                )
            })?
        }
    };
    ensure!(
        settings
            .judge
            .batch_size
            .is_none_or(|count| batch.len() <= count),
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
    let mut failed = false;
    let mut repairs = std::collections::HashMap::new();
    for selected in &batch {
        let attempt = attempts
            .entry(selected.experience.id)
            .or_insert_with(|| super::transcript::Attempt::new(selected));
        let mut last: Option<Value> = None;
        let mut candidate_rejections = 0;
        let mut candidate_rejection_detail = None;
        let mut last_rejection: Option<(String, String, Option<SourceFailure>)> = None;
        let mut rejected_faults: Vec<(String, Fault)> = Vec::new();
        let mut submission_requested = false;
        let mut needs_repair = false;
        let mut corrected_draft = None;
        let mut confirmed_review = false;
        let mut repair_explanation = "The judge ended without saving a review.";
        loop {
            let action = match backend
                .next(selected, last.as_ref(), client.allowed_tools())
                .await
            {
                Ok(action) => action,
                Err(error) => {
                    let source = error.downcast_ref::<SourceFailure>();
                    attempt.event("model_error", None, json!({
                        "reason":format!("{error:#}"), "input":source.map(|source| &source.excerpt)
                    }));
                    if candidate_rejections == 0 {
                        failed = true;
                        report.block_reason = Some(
                            if error
                                .downcast_ref::<super::harness::ProviderLimit>()
                                .is_some()
                            {
                                "provider_usage_limit".into()
                            } else {
                                "backend_error".into()
                            },
                        );
                        report.failure_detail = Some(format!("{error:#}"));
                        report.capture_source(&error);
                    }
                    break;
                }
            };
            match action {
                Action::Done => {
                    attempt.event("model_done", None, Value::Null);
                    match observe(&mut client, selected).await {
                        Ok("confirmed" | "corrected") => {
                            confirmed_review = true;
                        }
                        Ok("pending") if !submission_requested => {
                            submission_requested = true;
                            last = Some(json!({
                                "error":"review_not_saved",
                                "message":"There is no saved review for the selected experience revision.",
                                "experience_id":selected.experience.id,
                                "experience_revision":selected.revision,
                                "expected_review_revision":selected.review_revision,
                                "previous_rejection":last_rejection.as_ref().map(|(_, detail, _)| detail),
                                "guidance":"Submit review_experience for the selected experience and revisions. Correct the rejected fields before submitting."
                            }));
                            continue;
                        }
                        Ok("pending") => {
                            needs_repair = true;
                            last_rejection.get_or_insert_with(|| (
                                "review_experience".into(),
                                "The judge stopped without saving a review after being asked to submit it.".into(),
                                None,
                            ));
                        }
                        other => {
                            let error = match other {
                                Err(error) => error,
                                Ok(_) => anyhow!("The selected experience is unavailable for review confirmation."),
                            };
                            failed = true;
                            report.block_reason = Some("tool_error".into());
                            report.diagnostic = Some(FailureDiagnostic::new(
                                selected.experience.id,
                                "get_experience",
                                &format!("{error:#}"),
                            ));
                            report.capture_source(&error);
                        }
                    }
                    break;
                }
                Action::RejectedTool { name, source } => {
                    if name == "review_experience" {
                        corrected_draft = None;
                    }
                    attempt.event(
                        "tool_parse_rejection",
                        Some(&name),
                        json!({
                            "reason":source.detail, "input":source.excerpt
                        }),
                    );
                    repair_explanation =
                        "The judge submitted malformed arguments and did not correct them.";

                    // The model already knows its input. Return only the parser's
                    // location and a fixed correction instruction, never the input.
                    last = Some(json!({"error":"invalid_tool_arguments",
                        "message":source.detail,
                        "guidance":"Correct the tool arguments using the supplied schema and resend the call."}));
                    last_rejection = Some((name, source.to_string(), Some(source)));
                }
                Action::Tool { name, arguments } => {
                    let submitted_review = (name == "review_experience").then(|| {
                        corrected_draft = None;
                        arguments.clone()
                    });
                    attempt.event("tool_request", Some(&name), arguments.clone());
                    match scoped_tool(&mut client, selected, &name, arguments).await {
                        Ok(value) => {
                            attempt.event("tool_result", Some(&name), value.clone());
                            if value.get("status").and_then(Value::as_str) == Some("needs_input") {
                                failed = true;
                                report.block_reason = Some("needs_input".into());
                                report.failure_detail = Some(
                                    ["reason", "next_action"]
                                        .into_iter()
                                        .filter_map(|field| value[field].as_str())
                                        .collect::<Vec<_>>()
                                        .join(" "),
                                );
                                break;
                            }
                            let correction = value.get("status").and_then(Value::as_str)
                                == Some("needs_correction");
                            last = Some(value);
                            // The database acknowledgement is authoritative. A model
                            // need not spend another turn saying it is done.
                            if !correction
                                && name == "review_experience"
                                && matches!(
                                    observe(&mut client, selected).await?,
                                    "confirmed" | "corrected"
                                )
                            {
                                confirmed_review = true;
                                break;
                            }
                        }
                        Err(error)
                            if name == "review_experience"
                                && error.downcast_ref::<CandidateConflict>().is_some() =>
                        {
                            attempt.event(
                                "tool_rejection",
                                Some(&name),
                                json!(format!("{error:#}")),
                            );
                            candidate_rejections += 1;
                            repair_explanation =
                                "The review reused a candidate key with a different declaration.";
                            candidate_rejection_detail = Some(format!("{error:#}"));
                            last = Some(json!({"error":"candidate_key_conflict",
                                "guidance":"A candidate key from an earlier review has a different declaration. Inspect experience_history. Reuse a key only with its exact original kind and declaration; use a new key for a revised claim."}));
                        }
                        Err(error)
                            if error.downcast_ref::<InputRejected>().is_some()
                                || error.downcast_ref::<McpApplicationError>().is_some()
                                || error.downcast_ref::<UndeclaredBeliefCandidate>().is_some()
                                || error.downcast_ref::<Refusal>().is_some()
                                || error.downcast_ref::<SourceFailure>().is_some_and(
                                    |source| source.stage == "invalid review arguments",
                                ) =>
                        {
                            attempt.event(
                                "tool_rejection",
                                Some(&name),
                                json!(format!("{error:#}")),
                            );
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
                                .or_else(|| error.downcast_ref::<Refusal>().map(|e| &e.fault));
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
                            let focused = fault
                                .filter(|fault| fault.code == Code::QuotationMismatch)
                                .map(|fault| {
                                    SourceFailure::input("quotation_mismatch", &[], &fault.message)
                                });
                            last_rejection = Some((
                                name.clone(),
                                fault.map_or_else(
                                    || format!("{error:#}"),
                                    |fault| {
                                        format!(
                                            "{} Field path: {}.",
                                            fault.message,
                                            json!(fault.path)
                                        )
                                    },
                                ),
                                focused.or_else(|| error.downcast_ref::<SourceFailure>().cloned()),
                            ));
                            let is_undeclared = error.is::<UndeclaredBeliefCandidate>()
                                || error.downcast_ref::<Refusal>().is_some_and(|refusal| {
                                    refusal.kind == RefusalKind::UndeclaredCandidate
                                });
                            if let (true, Some(arguments), Some(fault)) =
                                (is_undeclared, submitted_review.as_ref(), fault)
                            {
                                corrected_draft =
                                    repair::correct_pattern_assessments(arguments, fault);
                            }
                            let is_graph_scope =
                                matches!(name.as_str(), "explain_belief" | "query_intervention")
                                    && fault.is_some_and(|fault| {
                                        fault.code == Code::WrongIdentity
                                            && fault.path == [Segment::Key("id".into())]
                                    });
                            repair_explanation = if is_undeclared {
                                "The review referred to a belief candidate that it did not declare."
                            } else if is_graph_scope {
                                "The judge asked for a graph explanation outside the review's project."
                            } else {
                                "The judge submitted a request Mimir rejected and did not resolve it."
                            };
                            if let Some(fault) = fault.filter(|_| is_undeclared || is_graph_scope) {
                                let rejected = (name, fault.clone());
                                if rejected_faults.contains(&rejected) {
                                    needs_repair = true;
                                    break;
                                }
                                rejected_faults.push(rejected);
                            }
                        }
                        Err(error) => {
                            attempt.event("tool_error", Some(&name), json!(format!("{error:#}")));
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
        if needs_repair {
            if let Some(arguments) = corrected_draft {
                attempt.event(
                    "automatic_review_correction",
                    Some("review_experience"),
                    json!("Removed assessments that treated declared procedures as beliefs."),
                );
                let result =
                    scoped_tool(&mut client, selected, "review_experience", arguments).await;
                match &result {
                    Ok(value) => {
                        attempt.event("tool_result", Some("review_experience"), value.clone())
                    }
                    Err(error) => attempt.event(
                        "tool_rejection",
                        Some("review_experience"),
                        json!(format!("{error:#}")),
                    ),
                }
                confirmed_review = matches!(
                    observe(&mut client, selected).await,
                    Ok("confirmed" | "corrected")
                );
            }
            if !confirmed_review {
                report
                    .block_reason
                    .get_or_insert_with(|| "review_requires_repair".into());
            }
        }
        if confirmed_review {
            attempts.remove(&selected.experience.id);
        }
        if !confirmed_review && !failed {
            let detail = last_rejection
                .as_ref()
                .map(|(_, detail, _)| detail.clone())
                .or_else(|| candidate_rejection_detail.clone())
                .unwrap_or_else(|| repair_explanation.into());
            repairs.insert(
                selected.experience.id,
                RepairCase {
                    explanation: repair_explanation.into(),
                    detail,
                    diagnostic_id: None,
                    transcript_pending: false,
                },
            );
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
        if candidate_rejections > 0 && !confirmed_review && !failed && report.diagnostic.is_none() {
            report.diagnostic = Some(FailureDiagnostic::new(
                selected.experience.id,
                "review_experience",
                candidate_rejection_detail
                    .as_deref()
                    .unwrap_or("review correction was not confirmed"),
            ));
        }
        if failed {
            break;
        }
    }
    if failed {
        client.stop().await;
        client = Client::start(
            &settings.judge.mcp_command,
            &settings.judge.mcp_args,
            &settings.path,
        )
        .await?;
    }
    for selected in &batch {
        match observe(&mut client, selected).await {
            Ok(outcome @ ("confirmed" | "corrected")) => {
                attempts.remove(&selected.experience.id);
                if outcome == "confirmed" {
                    report.confirmed += 1;
                } else {
                    report.corrected += 1;
                }
            }
            Ok("pending") => {
                if let Some(attempt) = attempts.get_mut(&selected.experience.id) {
                    attempt.pending();
                }
                report.pending += 1;
                // Spec (Mimir.JudgeBatchReadback.pendingDeferrals): a pin
                // whose final readback stays pending — the stored revision
                // still matches the selection but no review was confirmed —
                // joins the deferred set. It is excluded from subsequent
                // selections and reconciled against fresh reads, so one
                // conflicted experience cannot park the whole watcher.
                // The deferred set is unique per pin; the candidate-conflict
                // path may already hold this pin.
                let deferred = report.deferred_reviews.iter().any(|item| {
                    item.id == selected.experience.id && item.revision == selected.revision
                });
                if !deferred && repairs.contains_key(&selected.experience.id) {
                    report.deferred_reviews.push(DeferredReview {
                        id: selected.experience.id,
                        revision: selected.revision,
                        repair: repairs.remove(&selected.experience.id),
                    });
                }
            }
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
    if report.status == "complete" {
        // Spec (Mimir.JudgeBatchReadback.reason): a completed readback
        // replaces an earlier blocking reason — the retained diagnostic and
        // failure detail still explain the attempt.
        report.block_reason = None;
    } else if failed && report.block_reason.is_none() {
        report.block_reason = Some("incomplete".into());
    }
    if report.status != "complete" && report.block_reason.is_none() {
        report.block_reason = Some(
            if report.corrected > 0 && report.pending == 0 && report.unavailable == 0 {
                "review_source_changed"
            } else if report.deferred_reviews.is_empty() {
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
    use anyhow::Context;
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

    #[ignore = "requires MIMIR_TEST_ROOT isolated fixture"]
    #[test]
    fn deferred_revision_is_reconsidered_only_after_change_or_external_review() {
        let item = DeferredReview {
            id: Uuid::new_v4(),
            revision: 2,
            repair: None,
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
                    ensure!(
                        feedback["fault"]["path"]
                            == json!([
                                "review",
                                "candidate_feedback",
                                0,
                                "target",
                                "candidate_key"
                            ])
                    );
                    ensure!(feedback["message"]
                        .as_str()
                        .is_some_and(|text| text.contains("fixture-key")));
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
        WrongProject,
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
                if self.calls >= 26 {
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
                if matches!(self.case, RejectionCase::Exhausted) && self.calls == 26 {
                    let feedback = last.ok_or_else(|| anyhow!("missing submission instruction"))?;
                    ensure!(feedback["error"] == "review_not_saved");
                    self.calls += 1;
                    return Ok(Action::Done);
                }
                if self.calls > 0 {
                    let feedback = last.ok_or_else(|| anyhow!("missing tool feedback"))?;
                    if matches!(self.case, RejectionCase::WrongProject) {
                        ensure!(feedback["status"] == "needs_correction");
                        ensure!(feedback["fault"]["code"] == "wrong_identity");
                        ensure!(feedback["next_action"]
                            .as_str()
                            .is_some_and(|text| text.contains("resubmit")));
                    } else {
                        ensure!(feedback["error"] == "invalid_tool_arguments");
                    }
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
                        RejectionCase::WrongProject => Action::Tool {
                            name: "review_experience".into(),
                            arguments: json!({"expected_review_revision":selected.review_revision,
                                "review":{"experience_id":selected.experience.id,"experience_revision":selected.revision,
                                    "reviewer":"fixture","rationale":"invalid project reference",
                                    "feedback":[{"belief_id":Uuid::new_v4(),"verdict":"support","weight":0.5}]}}),
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
            RejectionCase::WrongProject,
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
                    "config_version=1\n[logging]\ndirectory='{}'\n[database]\nhost='127.0.0.1'\nport=1\ndbname='unused'\nuser='unused'\n[judge]\nproject='judge-retry-fixture'\nbatch_size=1\nmcp_command='bash'\nmcp_args=['{}','{}','{}','{}']\n[llm]\nbackend='command'\nmodel='fixture'\ncommand='/bin/true'\n",
                    dir.join("logs").display(), fixture.display(), id,
                    dir.join("reviews.jsonl").display(),
                    if matches!(case, RejectionCase::WrongProject) { "project-correction" } else { "standard" }
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
                assert_eq!(backend.calls, 27);
                assert_eq!(
                    report.block_reason.as_deref(),
                    Some("review_requires_repair")
                );
                assert!(serde_json::to_value(&report).unwrap()["failure_source"]
                    .get("excerpt")
                    .is_none());
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
    async fn requests_beyond_old_budget_are_counted_and_pending_readback_defers() {
        use std::os::unix::fs::PermissionsExt;

        let fixture = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("src/judge/retry_fixture.sh");
        let dir = std::env::temp_dir().join(format!("mimir-judge-budget-trace-{}", Uuid::new_v4()));
        std::fs::create_dir(&dir).unwrap();
        std::fs::set_permissions(&dir, std::fs::Permissions::from_mode(0o700)).unwrap();
        let config_path = dir.join("config.toml");
        let experience_id = Uuid::new_v4();
        let write_config = |mode: &str| {
            std::fs::write(
                &config_path,
                format!(
                    "config_version=1\n[logging]\ndirectory='{}'\n[database]\nhost='127.0.0.1'\nport=1\ndbname='unused'\nuser='unused'\n[judge]\nproject='judge-retry-fixture'\nbatch_size=1\nmcp_command='bash'\nmcp_args=['{}','{}','{}','{}']\n[llm]\nbackend='command'\nmodel='fixture'\ncommand='/bin/true'\n",
                    dir.join("logs").display(),
                    fixture.display(),
                    experience_id,
                    dir.join("reviews.jsonl").display(),
                    mode
                ),
            )
            .unwrap();
            std::fs::set_permissions(&config_path, std::fs::Permissions::from_mode(0o600)).unwrap();
        };
        write_config("standard");
        std::fs::create_dir(dir.join("logs")).unwrap();
        let settings = super::super::config::load(Some(&config_path)).unwrap();
        let state = State::lock(dir.join("state")).unwrap().unwrap();
        let mut backend = NoReview { calls: 0 };
        let failed = run(&settings, &state, &mut backend).await;
        assert_eq!(failed.status, "blocked");
        assert_eq!(
            failed.block_reason.as_deref(),
            Some("review_requires_repair"),
            "a pending final readback joins the deferred set \
             (Mimir.JudgeBatchReadback.pendingDeferrals)"
        );
        assert_eq!(failed.pending, 1);
        assert_eq!(failed.deferred_reviews.len(), 1);
        assert!(failed.diagnostic.is_some());
        assert_eq!(backend.calls, 27);
        assert!(failed.diagnostics_id.is_none());
        let legacy = state.path().join("judge-diagnostics.json");
        assert!(!legacy.exists());
        let legacy_content = b"{\"attempts\":[]}";
        std::fs::write(&legacy, legacy_content).unwrap();
        std::fs::set_permissions(&legacy, std::fs::Permissions::from_mode(0o600)).unwrap();

        // The deferred pin is excluded from subsequent selections: the next
        // batch is empty and makes no model calls instead of re-selecting
        // the same experience.
        let mut parked = NoReview { calls: 0 };
        let excluded = run(&settings, &state, &mut parked).await;
        assert_eq!(excluded.status, "blocked");
        assert_eq!(excluded.block_reason.as_deref(), Some("review_deferred"));
        assert_eq!(excluded.selected, 0);
        assert_eq!(excluded.pending, 0);
        assert_eq!(parked.calls, 0);

        // A later source correction lets the watcher complete a fresh review.
        write_config("revision-bump");
        let settings = super::super::config::load(Some(&config_path)).unwrap();
        let mut recovery = ToolCorrection {
            case: RejectionCase::LocalValidation,
            calls: 0,
        };
        let completed = run(&settings, &state, &mut recovery).await;
        assert_eq!(completed.status, "complete");
        assert!(completed.deferred_reviews.is_empty());
        assert_eq!(std::fs::read(legacy).unwrap(), legacy_content);
        assert!(state::read_failure(state.path()).unwrap().is_some());
        drop(state);
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[tokio::test]
    async fn undeclared_candidate_is_refused_before_mcp_and_pending_readback_defers() {
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
                    "config_version=1\n[logging]\ndirectory='{}'\n[database]\nhost='127.0.0.1'\nport=1\ndbname='unused'\nuser='unused'\n[judge]\nproject='judge-retry-fixture'\nbatch_size=1\nmcp_command='bash'\nmcp_args=['{}','{}','{}']\n[llm]\nbackend='command'\nmodel='fixture'\ncommand='/bin/true'\n",
                    dir.join("logs").display(), fixture.display(), id, review_log.display()
                ),
            )
            .unwrap();
            std::fs::set_permissions(&config_path, std::fs::Permissions::from_mode(0o600)).unwrap();
            let settings = super::super::config::load(Some(&config_path)).unwrap();
            let state = State::lock(dir.join("state")).unwrap().unwrap();
            let mut backend = ReferenceCorrection { calls: 0, correct };
            let report = run(&settings, &state, &mut backend).await;
            assert_eq!(report.status, expected_status, "correct={correct}");
            assert_eq!(backend.calls, 2);
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
                    Some("review_requires_repair")
                );
                assert_eq!(report.pending, 1);
                assert_eq!(
                    report.deferred_reviews.len(),
                    1,
                    "the pending readback defers the unreviewed experience"
                );
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

    struct GraphScopeCorrection {
        calls: usize,
        global: Uuid,
        owned: Uuid,
    }

    impl Backend for GraphScopeCorrection {
        fn next<'a>(
            &'a mut self,
            selected: &'a ExperienceState,
            last: Option<&'a Value>,
            _tools: &'a [Value],
        ) -> Pin<Box<dyn Future<Output = Result<Action>> + Send + 'a>> {
            Box::pin(async move {
                let action = match self.calls {
                    0 => ("get_belief", json!({"id":self.global})),
                    1 => {
                        let belief = last.context("missing global belief")?;
                        ensure!(belief["id"] == self.global.to_string());
                        ensure!(belief["project"].is_null());
                        (
                            "explain_belief",
                            json!({"id":self.global,"limit":1,"offset":0}),
                        )
                    }
                    2 | 3 => {
                        let feedback = last.context("missing scope correction")?;
                        ensure!(feedback["error"] == "invalid_tool_arguments");
                        ensure!(feedback["message"].as_str().is_some_and(
                            |text| text.contains("Use a belief from the selected project")
                        ));
                        if self.calls == 2 {
                            ("query_intervention", json!({"id":self.global,"value":0.6}))
                        } else {
                            (
                                "explain_belief",
                                json!({"id":self.owned,"limit":1,"offset":0}),
                            )
                        }
                    }
                    4 => {
                        let explanation = last.context("missing project belief explanation")?;
                        ensure!(explanation["incoming_edges"].is_array());
                        (
                            "review_experience",
                            json!({
                                "expected_review_revision":selected.review_revision,
                                "review":{"experience_id":selected.experience.id,
                                    "experience_revision":selected.revision,"reviewer":"fixture",
                                    "rationale":"completed review after correcting graph scope"}
                            }),
                        )
                    }
                    _ => return Ok(Action::Done),
                };
                self.calls += 1;
                Ok(Action::Tool {
                    name: action.0.into(),
                    arguments: action.1,
                })
            })
        }
    }

    #[ignore = "requires MIMIR_TEST_ROOT isolated fixture"]
    #[tokio::test]
    async fn isolated_mcp_review_cycle() {
        let fixture = isolation::fixture();
        let path = fixture.root.join("config.toml");
        let binary = fixture.mcp.clone();
        let project = format!("step5-{}", Uuid::new_v4());
        let mut settings = super::super::config::load(Some(&path)).unwrap();
        settings.judge.project = Some(project.clone());
        settings.judge.mcp_command = binary;
        settings.judge.batch_size = Some(1);
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
        let e = service
            .create_experience(&e.clone().with_identity(()))
            .await
            .unwrap()
            .experience;
        let global = service
            .add_belief(
                "global scope fixture",
                0.6,
                0.5,
                mimir_core::graph::MemoryType::Fact,
            )
            .await
            .unwrap();
        let owned = service
            .add_belief_in_project(
                "project scope fixture",
                0.6,
                0.5,
                &project,
                mimir_core::graph::MemoryType::Fact,
            )
            .await
            .unwrap();
        let mut scope = GraphScopeCorrection {
            calls: 0,
            global: global.id,
            owned: owned.id,
        };
        let success = run(&settings, &state, &mut scope).await;
        assert_eq!(success.status, "complete");
        assert_eq!(success.confirmed, 1);
        assert_eq!(scope.calls, 5);
        assert!(service.delete_belief(global.id).await.unwrap());
        let committed = service.get_experience(e.id).await.unwrap().unwrap();
        assert_eq!(committed.reviewed_revision, 1);
        let history = service.experience_history(e.id).await.unwrap();
        assert_eq!(history["reviews"][0]["payload"]["reviewer"], "mimir-judge");
        let mut fake = Fake {
            mode: Mode::Review,
            calls: 0,
            service: service.clone(),
        };
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
            let e = service
                .create_experience(&e.clone().with_identity(()))
                .await
                .unwrap()
                .experience;
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
                assessments: vec![],
                extracted_items: vec![],
                source_coverage: vec![],
            };
            service
                .review_experience(&review, latest.review_revision)
                .await
                .unwrap();
        }
        settings.judge.batch_size = Some(2);
        let first = make_experience();
        let second = make_experience();
        let first = service
            .create_experience(&first.clone().with_identity(()))
            .await
            .unwrap()
            .experience;
        let second = service
            .create_experience(&second.clone().with_identity(()))
            .await
            .unwrap()
            .experience;
        let listener = std::net::TcpListener::bind("127.0.0.1:0").unwrap();
        listener.set_nonblocking(true).unwrap();
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
            daily_report_at: None,
            timeout_seconds: 2,
            retry_seconds: 5,
            max_attempts: 3,
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
        assert_eq!(
            listener.accept().unwrap_err().kind(),
            std::io::ErrorKind::WouldBlock,
            "standalone review must queue mail without connecting to SMTP"
        );
        service.delete_project(&project).await.unwrap();
        drop(state);
        std::fs::remove_dir_all(state_path).unwrap();
    }
}
