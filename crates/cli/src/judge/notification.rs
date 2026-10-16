use super::{
    config::RuntimeConfig,
    state::{Report, State},
};
use anyhow::Result;
use mimir_notifications::{Event, EventStatus, Notifier};

/// Translate only safe, bounded judge status into the shared notification API.
pub async fn notify(settings: &RuntimeConfig, state: &State, report: &mut Report) -> Result<()> {
    let notifier = Notifier::new(&settings.email, state.path())?;
    let status = match report.status.as_str() {
        "blocked" => EventStatus::Failure {
            code: "blocked".into(),
            summary: "A review batch did not complete".into(),
        },
        "partial" => EventStatus::Failure {
            code: "partial".into(),
            summary: "A review batch completed only in part".into(),
        },
        _ => EventStatus::Recovery,
    };
    let event = Event {
        source: "judge".into(),
        incident_key: settings
            .judge
            .project
            .clone()
            .unwrap_or_else(|| "all-projects".into()),
        status,
    };
    report.notification = notifier.submit(&event).await?.as_str().into();
    Ok(())
}
