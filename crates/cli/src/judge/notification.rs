use super::{
    config::RuntimeConfig,
    state::{self, FailureIncident, Report, State},
};
use anyhow::Result;
use chrono::{DateTime, Local, Utc};
use mimir_notifications::{Event, EventStatus, Notifier};
use uuid::Uuid;

fn local_time(seconds: u64) -> String {
    i64::try_from(seconds)
        .ok()
        .and_then(|value| DateTime::<Utc>::from_timestamp(value, 0))
        .map(|value| {
            value
                .with_timezone(&Local)
                .format("%Y-%m-%d %H:%M:%S %:z")
                .to_string()
        })
        .unwrap_or_else(|| format!("Unix time {seconds}"))
}

fn reason(report: &Report) -> String {
    match report.block_reason.as_deref() {
        Some("model_budget_exhausted") => "model call limit reached".into(),
        Some("tool_budget_exhausted") => "tool call limit reached".into(),
        Some("backend_timeout") => "model response timed out".into(),
        Some("backend_error") => "model backend failed".into(),
        Some("review_deferred") => "review deferred after a rejected candidate".into(),
        Some(other) => format!("review incomplete ({})", state::bounded(other, 64)),
        None => "review incomplete".into(),
    }
}

fn ids(ids: &[Uuid]) -> String {
    if ids.is_empty() {
        return "none".into();
    }
    let mut rendered = ids
        .iter()
        .take(5)
        .map(Uuid::to_string)
        .collect::<Vec<_>>()
        .join(", ");
    if ids.len() > 5 {
        rendered.push_str(&format!(" (+{} more)", ids.len() - 5));
    }
    rendered
}

fn project(settings: &RuntimeConfig) -> String {
    settings
        .judge
        .project
        .as_deref()
        .map(|value| state::bounded(value, 80))
        .unwrap_or_else(|| "all projects".into())
}

fn failure_details(project: &str, max_calls: usize, report: &Report) -> String {
    let mut details = format!(
        "Project: {}\nObserved: {}\nReason: {}\nSelected: {}; confirmed: {}; corrected: {}; pending: {}; unavailable: {}\nAffected experience IDs: {}",
        project,
        local_time(report.recorded_at),
        reason(report),
        report.selected,
        report.confirmed,
        report.corrected,
        report.pending,
        report.unavailable,
        ids(&report.selected_ids),
    );
    if report.block_reason.as_deref() == Some("model_budget_exhausted") {
        details.push_str(&format!("\nConfigured model call limit: {max_calls}"));
    }
    if let Some(id) = report.diagnostics_id {
        details.push_str(&format!(
            "\nDiagnostic ID: {id}\nInspect: mimir judge diagnostics --id {id}"
        ));
    } else {
        details.push_str("\nDiagnostic ID: unavailable; inspect mimir judge status");
    }
    details
}

fn recovery_details(project: &str, report: &Report, incident: &FailureIncident) -> String {
    let first = &incident.first;
    let confirmed = first
        .selected_ids
        .iter()
        .filter(|id| {
            incident
                .confirmed_reviews
                .iter()
                .any(|review| review.id == **id)
        })
        .count();
    let mut details = format!(
        "Project: {}\nPrevious failure: {}\nPrevious reason: {}\nQueue: idle at {}; no pending reviews were selected\nAffected reviews: {} confirmed by completed batches; {} unverified",
        project,
        local_time(first.recorded_at),
        reason(first),
        local_time(report.recorded_at),
        confirmed,
        first.selected_ids.len().saturating_sub(confirmed),
    );
    if let Some(id) = first.diagnostics_id {
        details.push_str(&format!("\nPrevious diagnostic ID: {id}"));
    }
    for id in first.selected_ids.iter().take(5) {
        if let Some(review) = incident
            .confirmed_reviews
            .iter()
            .find(|review| review.id == *id)
        {
            details.push_str(&format!(
                "\n{id}: confirmed at {}",
                local_time(review.recorded_at)
            ));
        } else {
            details.push_str(&format!("\n{id}: completion unverified"));
        }
    }
    if first.selected_ids.len() > 5 {
        details.push_str(&format!(
            "\nAdditional affected reviews: {}",
            first.selected_ids.len() - 5
        ));
    }
    details
}

fn learning_status(report: &Report) -> EventStatus {
    match report.status.as_str() {
        "blocked" | "partial" => EventStatus::Failure {
            code: "judge_failure".into(),
            summary: format!("Review batch did not complete: {}", reason(report)),
        },
        "idle" => EventStatus::Recovery,
        _ => EventStatus::Progress,
    }
}

/// Translate only safe, bounded judge status into the shared notification API.
pub async fn notify(settings: &RuntimeConfig, state: &State, report: &mut Report) -> Result<()> {
    let notifier = Notifier::new(&settings.email, state.path())?;
    // A completed batch does not show that the queue is drained. Keep any
    // existing failure incident open until a later run observes an idle queue.
    let event = Event {
        source: "judge".into(),
        incident_key: settings
            .judge
            .project
            .clone()
            .unwrap_or_else(|| "all-projects".into()),
        status: learning_status(report),
        details: match report.status.as_str() {
            "blocked" | "partial" => Some(failure_details(
                &project(settings),
                settings.llm.max_calls,
                report,
            )),
            "idle" => state::read_failure(state.path())?
                .as_ref()
                .map(|incident| recovery_details(&project(settings), report, incident)),
            _ => None,
        },
    };
    report.notification = notifier.submit(&event).await?.as_str().into();
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::super::state::ConfirmedReview;
    use super::*;

    #[test]
    fn failure_and_recovery_mail_facts_distinguish_review_from_idle() {
        let affected = Uuid::new_v4();
        let diagnostic = Uuid::new_v4();
        let mut failed = Report::new("blocked", 1, 0, 0, 1, 0);
        failed.block_reason = Some("model_budget_exhausted".into());
        failed.selected_ids.push(affected);
        failed.diagnostics_id = Some(diagnostic);
        failed.recorded_at = 1_792_004_819;
        let failure = failure_details("agda2sysml", 5, &failed);
        assert!(failure.contains("Reason: model call limit reached"));
        assert!(failure.contains("Configured model call limit: 5"));
        assert!(failure.contains(&affected.to_string()));
        assert!(failure.contains(&format!("mimir judge diagnostics --id {diagnostic}")));

        let mut idle = Report::new("idle", 0, 0, 0, 0, 0);
        idle.recorded_at = 1_792_005_490;
        let mut incident = FailureIncident {
            first: failed,
            latest: None,
            confirmed_reviews: Vec::new(),
            recovered_at: Some(idle.recorded_at),
        };
        let unverified = recovery_details("agda2sysml", &idle, &incident);
        assert!(unverified.contains("0 confirmed by completed batches; 1 unverified"));
        assert!(unverified.contains(&format!("{affected}: completion unverified")));
        incident.confirmed_reviews.push(ConfirmedReview {
            id: affected,
            recorded_at: 1_792_005_190,
        });
        let confirmed = recovery_details("agda2sysml", &idle, &incident);
        assert!(confirmed.contains("1 confirmed by completed batches; 0 unverified"));
        assert!(confirmed.contains(&format!("{affected}: confirmed at")));
        assert!(!confirmed.contains("completion unverified"));
    }

    #[test]
    fn unresolved_statuses_keep_one_incident_code() {
        for status in ["blocked", "partial"] {
            let report = Report::new(status, 1, 0, 0, 1, 0);
            assert!(matches!(learning_status(&report),
                EventStatus::Failure { code, .. } if code == "judge_failure"));
        }
        assert!(matches!(
            learning_status(&Report::new("complete", 1, 1, 0, 0, 0)),
            EventStatus::Progress
        ));
        assert!(matches!(
            learning_status(&Report::new("idle", 0, 0, 0, 0, 0)),
            EventStatus::Recovery
        ));
    }
}
