use super::recovery::Next;
use super::{
    config::RuntimeConfig,
    state::{self, DeferredReview, Report, State},
};
use anyhow::Result;
use mimir_notifications::{Event, EventStatus, Notifier};
use uuid::Uuid;

fn mail_detail(detail: &str) -> String {
    detail
        .chars()
        .map(|c| if c.is_control() && c != '\n' { ' ' } else { c })
        .collect()
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
            code: match repair.remedy {
                state::Remedy::EditReview => "review_requires_repair",
                state::Remedy::ChooseBackend => "review_needs_backend",
                state::Remedy::RestoreClient => "review_needs_client",
                state::Remedy::RestoreRead => "review_needs_readback",
            }
            .into(),
            summary: repair.explanation.clone(),
        },
        details: Some(details),
    })
}

pub(super) fn queue_repair(settings: &RuntimeConfig, state: &State, review: &DeferredReview) {
    if let Some(event) = review_failure(settings, state.path(), review) {
        match Notifier::new(&settings.email, state.path()).and_then(|mail| mail.enqueue(&event)) {
            Ok(_) => AVAILABLE.notify_one(),
            Err(error) => eprintln!("Could not queue repair mail for {}: {error:#}", review.id),
        }
    }
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
    let reason = report.block_reason.as_deref().unwrap_or("startup_failure");
    let explanation = report.failure_detail.as_deref().unwrap_or("");
    let details = format!(
        "{}\n{}",
        mail_detail(explanation),
        super::diagnose::summary(Some(report))
    );
    report.notification = shared_action(config, state.path(), reason, &details)?;
    Ok(())
}

pub(super) fn shared_action(
    config: Option<&std::path::Path>,
    directory: &std::path::Path,
    reason: &str,
    details: &str,
) -> Result<String> {
    let email = super::config::load_email(config)?;
    let notifier = Notifier::new(&email, directory)?;
    let event = Event {
        source: STARTUP_SOURCE.into(),
        incident_key: "startup".into(),
        status: EventStatus::Failure {
            code: reason.into(),
            summary: "The judge cannot start review work.".into(),
        },
        details: Some(mail_detail(details)),
    };
    let outcome = notifier.enqueue(&event)?.as_str().into();
    AVAILABLE.notify_one();
    Ok(outcome)
}

/// Translate public judge status into the shared notification API.
pub(super) fn enqueue_batch(
    settings: &RuntimeConfig,
    state: &State,
    report: &mut Report,
    next: &Next,
) -> Result<()> {
    let notifier = Notifier::new(&settings.email, state.path())?;
    let startup = match next {
        Next::Correct { code, action } => Some((
            EventStatus::Failure {
                code: (*code).into(),
                summary: "The judge needs a prerequisite restored before it can review.".into(),
            },
            mail_detail(action),
        )),
        Next::WorkEvent | Next::Scan if report.database_cases => Some((
            EventStatus::Recovery,
            "The judge opened its tool connection and read the review queue.".into(),
        )),
        _ => None,
    };
    let mut outcome = mimir_notifications::Outcome::NotNeeded;
    if let Some((status, details)) = startup {
        outcome = notifier.enqueue(&Event {
            source: STARTUP_SOURCE.into(),
            incident_key: "startup".into(),
            status,
            details: Some(details),
        })?;
    }
    for review in &report.deferred_reviews {
        if let Some(event) = review_failure(settings, state.path(), review) {
            let sent = notifier.enqueue(&event)?;
            if sent != mimir_notifications::Outcome::NotNeeded {
                outcome = sent;
            }
        }
    }
    report.notification = outcome.as_str().into();
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
    check_delivery_repair: bool,
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
            if check_delivery_repair {
                if let Err(error) = notifier.verify_delivery_repair().await {
                    eprintln!("Cannot verify the corrected mail delivery: {error:#}");
                }
            }
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
        let mut worker = start_worker(Some(config_path), Some(state_path.clone()), false);
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
    fn diagnostic_control_characters_cannot_prevent_delivery() {
        assert_eq!(mail_detail("line\nfield\tvalue\r"), "line\nfield value ");
    }
}
