use super::{
    config::RuntimeConfig,
    state::{self, DeferredReview, FailureIncident, Report, State},
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
        Some("review_deferred") => {
            "review deferred; excluded until corrected or reviewed by another caller".into()
        }
        Some(other) => format!("review incomplete ({other})"),
        None => "review incomplete".into(),
    }
}

fn ids(ids: &[Uuid]) -> String {
    if ids.is_empty() {
        return "none".into();
    }
    ids.iter()
        .map(Uuid::to_string)
        .collect::<Vec<_>>()
        .join(", ")
}

fn project(settings: &RuntimeConfig) -> String {
    settings
        .judge
        .project
        .as_deref()
        .map(str::to_owned)
        .unwrap_or_else(|| "all projects".into())
}

fn failure_details(
    project: &str,
    config: &std::path::Path,
    directory: &std::path::Path,
    report: &Report,
) -> String {
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
    if let Some(id) = report.diagnostics_id {
        details.push_str(&format!(
            "\nDiagnostic ID: {id}\nInspect: {}",
            diagnostic_command(config, directory, id)
        ));
    } else if report.transcripts_pending == 0 {
        details.push_str("\nDiagnostic ID: unavailable; inspect mimir judge status");
    }
    if report.transcripts_pending != 0 {
        details.push_str(&format!(
            "\nTranscript publication is pending. Check PostgreSQL, then run mimir judge diagnostics --list --config {}.",
            quote(config)
        ));
    }
    details.push('\n');
    details.push_str(&super::diagnose::summary(Some(report)));
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
    for id in &first.selected_ids {
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

fn review_key(review: &DeferredReview) -> String {
    format!("review/{}/{}", review.id, review.revision)
}

const REVIEW_SOURCE: &str = "judge-review";
const STARTUP_SOURCE: &str = "judge-startup";

pub(super) fn repair_command(
    settings: &RuntimeConfig,
    state_dir: &std::path::Path,
    review: &DeferredReview,
) -> String {
    format!(
        "mimir judge repair --experience {} --revision {} --config {} --state-dir {}",
        review.id,
        review.revision,
        quote(&settings.path),
        quote(state_dir),
    )
}

fn quote(path: &std::path::Path) -> String {
    format!("'{}'", path.to_string_lossy().replace('\'', "'\\''"))
}

pub(super) fn diagnostic_command(
    config: &std::path::Path,
    state_dir: &std::path::Path,
    id: Uuid,
) -> String {
    format!(
        "mimir judge diagnostics --id {id} --config {} --state-dir {}",
        quote(config),
        quote(state_dir),
    )
}

fn review_failure(
    settings: &RuntimeConfig,
    state_dir: &std::path::Path,
    review: &DeferredReview,
) -> Option<Event> {
    let repair = review.repair.as_ref()?;
    let mut details = format!(
        "Experience: {}\nSource revision: {}\nProblem: {}\n\nRun this command to open the review, choose a correction, and save it:\n{}",
        review.id, review.revision, repair.explanation, repair_command(settings, state_dir, review)
    );
    if let Some(id) = repair.diagnostic_id {
        details.push_str(&format!(
            "\nRead the failure explanation: {}",
            diagnostic_command(&settings.path, state_dir, id)
        ));
    } else if repair.transcript_pending {
        details.push_str("\nThe transcript is awaiting PostgreSQL. Run the repair command above to find it after reconnection.");
    }
    Some(Event {
        source: REVIEW_SOURCE.into(),
        incident_key: review_key(review),
        status: EventStatus::Failure {
            code: "review_requires_repair".into(),
            summary: repair.explanation.clone(),
        },
        details: Some(details),
    })
}

pub(super) fn review_recovered(
    settings: &RuntimeConfig,
    state_dir: &std::path::Path,
    review: &DeferredReview,
) -> Result<()> {
    Notifier::new(&settings.email, state_dir)?.enqueue(&Event {
        source: REVIEW_SOURCE.into(),
        incident_key: review_key(review),
        status: EventStatus::Recovery,
        details: Some(format!(
            "PostgreSQL confirmed a saved review for experience {} at source revision {}.",
            review.id, review.revision
        )),
    })?;
    AVAILABLE.notify_one();
    Ok(())
}

pub(super) fn startup_failure(
    config: Option<&std::path::Path>,
    state: &State,
    report: &mut Report,
) -> Result<()> {
    let email = super::config::load_email(config)?;
    let notifier = Notifier::new(&email, state.path())?;
    let reason = report.block_reason.as_deref().unwrap_or("startup_failure");
    let event = Event {
        source: STARTUP_SOURCE.into(),
        incident_key: "startup".into(),
        status: EventStatus::Failure {
            code: reason.into(),
            summary: "The judge cannot start review work.".into(),
        },
        details: Some(super::diagnose::summary(Some(report))),
    };
    report.notification = notifier.enqueue(&event)?.as_str().into();
    AVAILABLE.notify_one();
    Ok(())
}

/// Translate public judge status into the shared notification API.
pub fn enqueue(settings: &RuntimeConfig, state: &State, report: &mut Report) -> Result<()> {
    let notifier = Notifier::new(&settings.email, state.path())?;
    if matches!(report.status.as_str(), "complete" | "idle") {
        notifier.enqueue(&Event {
            source: STARTUP_SOURCE.into(),
            incident_key: "startup".into(),
            status: EventStatus::Recovery,
            details: Some("The judge checked for review work successfully.".into()),
        })?;
    }
    let mut review_alert = None;
    for review in &report.deferred_reviews {
        if let Some(event) = review_failure(settings, state.path(), review) {
            let outcome = notifier.enqueue(&event)?;
            if review_alert.is_none() || outcome != mimir_notifications::Outcome::NotNeeded {
                review_alert = Some(outcome);
            }
            AVAILABLE.notify_one();
        }
    }
    if let Some(outcome) = review_alert.filter(|_| {
        matches!(
            report.block_reason.as_deref(),
            Some("review_requires_repair" | "tool_rejected" | "review_deferred")
        )
    }) {
        report.notification = outcome.as_str().into();
        return Ok(());
    }
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
                &settings.path,
                state.path(),
                report,
            )),
            "idle" => state::read_failure(state.path())?
                .as_ref()
                .map(|incident| recovery_details(&project(settings), report, incident)),
            _ => None,
        },
    };
    report.notification = notifier.enqueue(&event)?.as_str().into();
    AVAILABLE.notify_one();
    Ok(())
}

static AVAILABLE: tokio::sync::Notify = tokio::sync::Notify::const_new();

pub struct Worker(tokio::task::JoinHandle<()>);
impl Drop for Worker {
    fn drop(&mut self) {
        self.0.abort();
    }
}

async fn wait_until_due(due: Option<u64>) {
    match due {
        Some(timestamp) => {
            let now = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_secs();
            tokio::time::sleep(std::time::Duration::from_secs(
                timestamp.saturating_sub(now),
            ))
            .await;
        }
        None => std::future::pending::<()>().await,
    }
}

pub fn start_worker(
    config: Option<std::path::PathBuf>,
    directory: Option<std::path::PathBuf>,
) -> Worker {
    Worker(tokio::spawn(async move {
        let email = match super::config::load_email(config.as_deref()) {
            Ok(email) => email,
            Err(error) => {
                eprintln!(
                    "Mail worker unavailable: {error:#}. Reviews do not depend on mail delivery."
                );
                return;
            }
        };
        if !email.enabled {
            return;
        }
        let path = match state::resolve(directory.as_deref()) {
            Ok(path) => path,
            Err(error) => {
                eprintln!("Mail worker state: {error:#}");
                return;
            }
        };
        let notifier = match Notifier::new(&email, &path) {
            Ok(notifier) => notifier,
            Err(error) => {
                eprintln!("Mail worker unavailable: {error:#}");
                return;
            }
        };
        // Arm file events before inspecting queued messages. This also notices
        // mail queued by a standalone judge process while the watcher is idle.
        if let Err(error) = notifier.pending_ids() {
            eprintln!("Mail outbox unavailable: {error:#}");
            return;
        }
        let mut outbox_events =
            match super::config_events::ConfigEvents::new(&path.join("notification-outbox.json")) {
                Ok(events) => Some(events),
                Err(error) => {
                    eprintln!("Cannot watch the mail outbox: {error:#}");
                    None
                }
            };
        let clock = match email.daily_report_at.as_deref() {
            Some(value) => match chrono::NaiveTime::parse_from_str(value, "%H:%M") {
                Ok(time) => Some(time),
                Err(error) => {
                    eprintln!("Daily statistics unavailable: email.daily_report_at must be a local clock time such as '09:00': {error}. Correct configuration; reviews and alerts continue.");
                    None
                }
            },
            None => {
                eprintln!("Daily statistics unavailable: choose email.daily_report_at in local time, for example '09:00'. No delivery time is assumed. Reviews and alerts continue.");
                None
            }
        };
        let deliver_alerts = async {
            loop {
                match notifier.retry_pending().await {
                Ok(outcomes) => for (source, incident, outcome) in outcomes {
                    if !matches!(outcome, mimir_notifications::Outcome::Sent | mimir_notifications::Outcome::NotNeeded) {
                        eprintln!("Mail for {source}/{incident}: {}. Pending deliveries retry at the configured interval; exhausted or authentication failures require attention.", outcome.as_str());
                    }
                },
                Err(error) => eprintln!("Mail delivery unavailable: {error:#}. Reviews continue. Correct the prerequisite and send SIGHUP to retry."),
            }
                let due = notifier.next_alert_due().unwrap_or_else(|error| {
                    eprintln!("Cannot schedule pending mail: {error:#}");
                    None
                });
                tokio::select! {
                    _ = wait_until_due(due) => {},
                    _ = AVAILABLE.notified() => {},
                    changed = async { match &mut outbox_events { Some(events) => events.changed().await, None => std::future::pending().await } } => {
                        if let Err(error) = changed { eprintln!("Mail outbox events unavailable: {error:#}"); outbox_events = None; }
                    },
                }
            }
        };
        let deliver_statistics = async {
            let Some(clock) = clock else { return };
            loop {
                let retry =
                    match super::digest::tick(config.as_deref(), directory.as_deref(), clock).await
                    {
                        Ok(true) => match notifier.digest_state() {
                            Ok(cursor) => Some(cursor.next_due),
                            Err(error) => {
                                eprintln!("Cannot schedule daily statistics retry: {error:#}");
                                None
                            }
                        },
                        Ok(false) => None,
                        Err(error) => {
                            eprintln!("Daily statistics unavailable: {error:#}. Reviews continue.");
                            None
                        }
                    };
                tokio::select! {
                    _ = wait_until_due(retry) => {},
                    result = super::digest::wait_for_delivery(Some(clock)) => {
                        if let Err(error) = result {
                            eprintln!("Daily delivery scheduling unavailable: {error:#}");
                            return;
                        }
                    }
                }
            }
        };
        // Both tasks are owned by this worker and cancelled with it. A
        // statistics query or its delivery cannot put new alerts on hold.
        tokio::join!(deliver_alerts, deliver_statistics);
    }))
}

#[cfg(test)]
mod tests {
    use super::super::state::ConfirmedReview;
    use super::*;

    #[tokio::test]
    async fn queued_alerts_retry_while_daily_statistics_wait_for_postgres() {
        use std::os::unix::fs::PermissionsExt;
        use tokio::io::AsyncWriteExt;
        let root = std::env::temp_dir().join(format!("mimir-mail-worker-{}", Uuid::new_v4()));
        std::fs::create_dir(&root).unwrap();
        std::fs::set_permissions(&root, std::fs::Permissions::from_mode(0o700)).unwrap();
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let postgres = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let config_path = root.join("config.toml");
        let state_path = root.join("state");
        std::fs::write(&config_path, format!(
            "config_version=1\n[logging]\ndirectory='{}'\n[database]\nhost='127.0.0.1'\nport={}\ndbname='unused'\nuser='unused'\n[judge]\nmcp_command='/bin/true'\n[llm]\nbackend='command'\nmodel='fixture'\ncommand='/bin/true'\n[email]\nenabled=true\nhost='127.0.0.1'\nport={}\ntls='starttls'\nfrom='mimir@example.test'\nto=['owner@example.test']\nauth='none'\ntimeout_seconds=1\nretry_seconds=1\nmax_attempts=2\ndaily_report_at='00:00'\n",
            root.join("logs").display(), postgres.local_addr().unwrap().port(), listener.local_addr().unwrap().port())).unwrap();
        std::fs::set_permissions(&config_path, std::fs::Permissions::from_mode(0o600)).unwrap();
        let settings = super::super::config::load(Some(&config_path)).unwrap();
        let notifier = Notifier::new(&settings.email, &state_path).unwrap();
        let mut worker = start_worker(Some(config_path), Some(state_path.clone()));
        // Accept the statistics connection and deliberately leave its
        // PostgreSQL handshake unanswered while the alerts are queued.
        let (_statistics, _) =
            tokio::time::timeout(std::time::Duration::from_secs(15), postgres.accept())
                .await
                .expect("daily statistics should try to connect")
                .unwrap();
        notifier
            .enqueue(&Event {
                source: "mail-fixture".into(),
                incident_key: "one-message".into(),
                status: EventStatus::Failure {
                    code: "temporary".into(),
                    summary: "Retry fixture".into(),
                },
                details: None,
            })
            .unwrap();
        let mut events = super::super::config_events::ConfigEvents::new(
            &state_path.join("notification-outbox.json"),
        )
        .unwrap();
        let server = tokio::spawn(async move {
            for _ in 0..2 {
                let (mut stream, _) = listener.accept().await.unwrap();
                stream
                    .write_all(b"421 Temporary service outage\r\n")
                    .await
                    .unwrap();
                stream.shutdown().await.unwrap();
            }
        });
        tokio::time::timeout(std::time::Duration::from_secs(15), async {
            server.await.unwrap();
            loop {
                if matches!(notifier.next_alert_due(), Ok(None)) {
                    break;
                }
                events.changed().await.unwrap();
            }
        })
        .await
        .expect("queued mail did not retry automatically and reach its configured attempt limit");
        assert_eq!(
            notifier.pending_ids().unwrap().len(),
            1,
            "exhaustion must retain the message"
        );
        worker.0.abort();
        let _ = (&mut worker.0).await;
        std::fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn failure_and_recovery_mail_facts_distinguish_review_from_idle() {
        let affected = Uuid::new_v4();
        let diagnostic = Uuid::new_v4();
        let mut failed = Report::new("blocked", 1, 0, 0, 1, 0);
        failed.block_reason = Some("model_budget_exhausted".into());
        failed.selected_ids.push(affected);
        failed.diagnostics_id = Some(diagnostic);
        failed.recorded_at = 1_792_004_819;
        let failure = failure_details("agda2sysml", "/config".as_ref(), "/state".as_ref(), &failed);
        assert!(failure.contains("Reason: model call limit reached"));
        assert!(!failure.contains("Configured model call limit"));
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
