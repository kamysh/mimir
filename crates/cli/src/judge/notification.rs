use super::{
    config::RuntimeConfig,
    state::{self, FailureIncident, Report, State},
};
use anyhow::Result;
use chrono::{DateTime, Local, Utc};
use mimir_core::config::DatabaseConfig;
use mimir_notifications::config::EmailConfig;
use mimir_notifications::{Event, EventStatus, Notifier};
use std::path::{Path, PathBuf};
use uuid::Uuid;

#[derive(Clone, Copy)]
pub enum Mode<'a> {
    Inline,
    Queued(&'a Worker),
}

enum Job {
    Alert {
        email: EmailConfig,
        path: PathBuf,
        event: Event,
    },
    Digest {
        email: EmailConfig,
        database: DatabaseConfig,
        path: PathBuf,
        outcome: super::RunOutcome,
    },
}

/// Own one consumer; queue admission never waits for SMTP or OAuth.
pub struct Worker {
    pending: tokio::sync::mpsc::UnboundedSender<Job>,
    task: Option<tokio::task::JoinHandle<()>>,
}

impl Worker {
    pub fn start() -> Self {
        let (pending, mut received) = tokio::sync::mpsc::unbounded_channel();
        let task = tokio::spawn(async move {
            let mut digest_problem = false;
            while let Some(job) = received.recv().await {
                let digest = matches!(&job, Job::Digest { .. });
                match deliver(job).await {
                    Ok(Some(problem)) => {
                        if problem != digest_problem {
                            eprintln!(
                                "judge daily email: {}",
                                if problem {
                                    "unavailable; inspect notification configuration"
                                } else {
                                    "available"
                                }
                            );
                            digest_problem = problem;
                        }
                    }
                    Ok(None) => (),
                    Err(error) => {
                        if digest {
                            digest_problem = true;
                        }
                        eprintln!("judge notification delivery: {error:#}. Review processing continues; inspect notification configuration.");
                    }
                }
            }
        });
        Self {
            pending,
            task: Some(task),
        }
    }

    fn send(&self, job: Job) -> Result<()> {
        self.pending
            .send(job)
            .map_err(|_| anyhow::anyhow!("notification worker is unavailable; restart the watcher"))
    }

    fn alert(
        &self,
        settings: &RuntimeConfig,
        path: &Path,
        report: &Report,
    ) -> Result<&'static str> {
        if !settings.email.enabled {
            return Ok("disabled");
        }
        self.send(Job::Alert {
            email: settings.email.clone(),
            path: path.to_owned(),
            event: event(settings, path, report)?,
        })?;
        Ok("queued")
    }

    pub fn digest(
        &self,
        settings: &RuntimeConfig,
        path: &Path,
        outcome: &super::RunOutcome,
    ) -> Result<()> {
        if !settings.email.enabled {
            return Ok(());
        }
        self.send(Job::Digest {
            email: settings.email.clone(),
            database: settings.core.database.clone(),
            path: path.to_owned(),
            outcome: *outcome,
        })
    }

    pub async fn shutdown(mut self) {
        if let Some(task) = self.task.take() {
            task.abort();
            if let Err(error) = task.await {
                if !error.is_cancelled() {
                    eprintln!("notification worker stopped unexpectedly: {error}");
                }
            }
        }
    }
}

impl Drop for Worker {
    fn drop(&mut self) {
        if let Some(task) = &self.task {
            task.abort();
        }
    }
}

async fn deliver(job: Job) -> Result<Option<bool>> {
    match job {
        Job::Alert { email, path, event } => {
            let outcome = Notifier::new(&email, path)?.submit(&event).await?;
            if !matches!(
                outcome,
                mimir_notifications::Outcome::Sent
                    | mimir_notifications::Outcome::Disabled
                    | mimir_notifications::Outcome::NotNeeded
            ) {
                eprintln!("judge notification delivery: {}", outcome.as_str());
            }
            Ok(None)
        }
        Job::Digest {
            email,
            database,
            path,
            outcome,
        } => super::digest::tick(&email, &database, Some(&path), &outcome)
            .await
            .map(Some),
    }
}

pub async fn notify_with(
    mode: Mode<'_>,
    settings: &RuntimeConfig,
    state: &State,
    report: &mut Report,
) -> Result<()> {
    match mode {
        Mode::Inline => notify(settings, state, report).await,
        Mode::Queued(worker) => {
            report.notification = worker.alert(settings, state.path(), report)?.into();
            Ok(())
        }
    }
}

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
        Some(other) => format!("review incomplete ({})", state::one_line_label(other)),
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
        .map(state::one_line_label)
        .unwrap_or_else(|| "all projects".into())
}

fn failure_details(project: &str, report: &Report) -> String {
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
            "\nDiagnostic ID: {id}\nInspect: mimir judge diagnostics --id {id}"
        ));
    } else {
        details.push_str("\nDiagnostic ID: unavailable; inspect mimir judge status");
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

/// Translate selected report facts into the shared notification API.
fn event(settings: &RuntimeConfig, path: &Path, report: &Report) -> Result<Event> {
    // A completed batch does not show that the queue is drained. Keep any
    // existing failure incident open until a later run observes an idle queue.
    Ok(Event {
        source: "judge".into(),
        incident_key: settings
            .judge
            .project
            .clone()
            .unwrap_or_else(|| "all-projects".into()),
        status: learning_status(report),
        details: match report.status.as_str() {
            "blocked" | "partial" => Some(failure_details(&project(settings), report)),
            "idle" => state::read_failure(path)?
                .as_ref()
                .map(|incident| recovery_details(&project(settings), report, incident)),
            _ => None,
        },
    })
}

pub async fn notify(settings: &RuntimeConfig, state: &State, report: &mut Report) -> Result<()> {
    let notifier = Notifier::new(&settings.email, state.path())?;
    report.notification = notifier
        .submit(&event(settings, state.path(), report)?)
        .await?
        .as_str()
        .into();
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::super::state::ConfirmedReview;
    use super::*;

    #[tokio::test]
    async fn stalled_smtp_does_not_block_reports_and_shutdown_releases_transport_and_lock() {
        use std::future::{poll_fn, Future};
        use tokio::io::AsyncReadExt;
        let work = crate::judge::harness::RunDir::new_in(&std::env::temp_dir()).unwrap();
        let server = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let text = format!(
            "config_version=1\n[logging]\ndirectory={}\n[database]\nhost='127.0.0.1'\nport=15432\nuser='fixture-user'\ndbname='fixture'\n[judge]\n[llm]\nbackend='command'\nmodel='fixture-model'\ncommand='/bin/true'\n[email]\nenabled=true\nhost='127.0.0.1'\nport={}\ntls='starttls'\nfrom='sender@example.test'\nto=['recipient@example.test']\nauth='none'\n",
            toml::Value::String(work.path().join("logs").display().to_string()), server.local_addr().unwrap().port()
        );
        let path = work.write("config.toml", text.as_bytes()).unwrap();
        let settings = crate::judge::config::load(Some(&path)).unwrap();
        let state = State::lock(work.path().join("state")).unwrap().unwrap();
        let worker = Worker::start();
        {
            let first = crate::judge::runner::finish_report(
                &settings,
                &state,
                Report::new("blocked", 1, 0, 0, 1, 0),
                Mode::Queued(&worker),
            );
            tokio::pin!(first);
            let std::task::Poll::Ready(first) =
                poll_fn(|cx| std::task::Poll::Ready(first.as_mut().poll(cx))).await
            else {
                panic!("Persisting a report waited for notification delivery")
            };
            assert_eq!(first.notification, "queued");
        }
        // Accepting establishes a real SMTP connection. Withhold the greeting;
        // its delivery future cannot complete successfully in this state.
        let (mut transport, _) = server.accept().await.unwrap();
        assert!(Notifier::new(&settings.email, state.path())
            .unwrap()
            .digest_state()
            .is_err());
        {
            let next = crate::judge::runner::finish_report(
                &settings,
                &state,
                Report::new("complete", 1, 1, 0, 0, 0),
                Mode::Queued(&worker),
            );
            tokio::pin!(next);
            let std::task::Poll::Ready(next) =
                poll_fn(|cx| std::task::Poll::Ready(next.as_mut().poll(cx))).await
            else {
                panic!("A stalled SMTP exchange blocked the next completed report")
            };
            assert_eq!(next.status, "complete");
            assert_eq!(next.confirmed, 1);
            assert_eq!(next.notification, "queued");
            assert_eq!(state::read(state.path()).unwrap().unwrap().confirmed, 1);
        }
        worker.shutdown().await;
        let mut received = Vec::new();
        transport.read_to_end(&mut received).await.unwrap();
        assert!(Notifier::new(&settings.email, state.path())
            .unwrap()
            .digest_state()
            .is_ok());
    }

    #[test]
    fn failure_and_recovery_include_complete_labels_and_every_affected_review() {
        let work = crate::judge::harness::RunDir::new_in(&std::env::temp_dir()).unwrap();
        let project_name = format!("{}-last-project-part", "資料".repeat(100));
        let settings_text = format!(
            "config_version=1\n[logging]\ndirectory={}\n[database]\nhost='127.0.0.1'\nport=15432\nuser='fixture-user'\ndbname='fixture'\n[judge]\nproject={}\n[llm]\nbackend='command'\nmodel='fixture-model'\ncommand='/bin/true'\n",
            toml::Value::String(work.path().join("logs").display().to_string()),
            toml::Value::String(project_name.clone()),
        );
        let path = work.write("config.toml", settings_text.as_bytes()).unwrap();
        let settings = crate::judge::config::load(Some(&path)).unwrap();
        let reason_code = format!("{}-last-reason-part", "unexpected_".repeat(40));
        let mut failed = Report::new("blocked", 12, 0, 0, 12, 0);
        failed.block_reason = Some(reason_code.clone());
        failed.selected_ids = (0..12).map(|_| Uuid::new_v4()).collect();
        let notification = event(&settings, work.path(), &failed).unwrap();
        let failure = notification.details.unwrap();
        assert!(failure.contains(&format!("Project: {project_name}\n")));
        assert!(failure.contains(&format!("Reason: review incomplete ({reason_code})\n")));
        assert!(failure.contains(&format!(
            "Affected experience IDs: {}",
            ids(&failed.selected_ids)
        )));
        assert!(!failure.contains(" more)"));
        let idle = Report::new("idle", 0, 0, 0, 0, 0);
        let incident = FailureIncident {
            confirmed_reviews: failed
                .selected_ids
                .iter()
                .skip(6)
                .map(|id| ConfirmedReview {
                    id: *id,
                    recorded_at: idle.recorded_at,
                })
                .collect(),
            first: failed,
            latest: None,
            recovered_at: Some(idle.recorded_at),
        };
        let recovery = recovery_details(&project(&settings), &idle, &incident);
        assert!(recovery.contains(&format!("Project: {project_name}\n")));
        assert!(recovery.contains(&format!(
            "Previous reason: review incomplete ({reason_code})\n"
        )));
        assert!(recovery.contains("6 confirmed by completed batches; 6 unverified"));
        for (index, id) in incident.first.selected_ids.iter().enumerate() {
            assert!(failure.contains(&id.to_string()));
            let outcome = if index < 6 {
                "completion unverified"
            } else {
                "confirmed at"
            };
            assert!(recovery.contains(&format!("\n{id}: {outcome}")));
        }
        assert!(!recovery.contains("Additional affected reviews:"));
        assert_eq!(ids(&[]), "none");
        assert_eq!(state::one_line_label("a\nb\r\tc\u{85}d"), "abcd");
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
        let failure = failure_details("agda2sysml", &failed);
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
