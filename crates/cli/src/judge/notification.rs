use super::{
    config::RuntimeConfig,
    state::{self, FailureIncident, Report, State},
};
use anyhow::Result;
use chrono::{DateTime, Local, Utc};
use mimir_core::config::DatabaseConfig;
use mimir_notifications::config::EmailConfig;
use mimir_notifications::{Event, EventConsumer, EventStatus, IncomingEvents, Notifier};
use std::path::{Path, PathBuf};
use uuid::Uuid;

#[derive(Clone, Copy)]
pub enum Mode<'a> {
    Standalone,
    Queued(&'a Worker),
}

#[derive(Clone)]
pub(super) struct CalendarJob {
    pub email: EmailConfig,
    pub database: DatabaseConfig,
    pub path: PathBuf,
    pub outcome: super::RunOutcome,
    pub time: super::config::DailyTime,
}

pub(super) enum Job {
    #[cfg(test)]
    Idle(tokio::sync::oneshot::Sender<()>),
    Alert {
        email: EmailConfig,
    },
    Digest(CalendarJob),
}

/// Own one consumer; queue admission never waits for SMTP or OAuth.
pub struct Worker {
    pending: tokio::sync::mpsc::UnboundedSender<Job>,
    path: PathBuf,
    task: Option<tokio::task::JoinHandle<()>>,
    calendar: Option<tokio::task::JoinHandle<()>>,
    schedule: tokio::sync::watch::Sender<Option<CalendarJob>>,
}

impl Worker {
    pub fn start(settings: &RuntimeConfig, path: &Path) -> Result<Self> {
        let incoming = IncomingEvents::new(path)?;
        let consumer = incoming.claim()?;
        // Subscribe before scanning saved events, including events from another
        // standalone process while this watcher is idle.
        let mut file_events =
            super::config_events::ConfigEvents::new(&path.join("notification-incoming.json"))?;
        let mut email = settings.email.clone();
        let mut retry_signal =
            tokio::signal::unix::signal(tokio::signal::unix::SignalKind::hangup())?;
        let owned_path = path.to_owned();
        let (pending, mut received) = tokio::sync::mpsc::unbounded_channel();
        let (schedule, updates) = tokio::sync::watch::channel(None);
        let calendar_pending = pending.clone();
        let calendar = tokio::spawn(async move {
            if let Err(error) =
                super::digest::calendar(updates, calendar_pending, Local::now, |at| async move {
                    let delay = (at - Utc::now()).to_std().unwrap_or_default();
                    tokio::time::sleep(delay).await;
                })
                .await
            {
                eprintln!("Daily report scheduler stopped: {error:#}. Correct the reported prerequisite and restart the watcher. Reviews continue.");
            }
        });
        let task = tokio::spawn(async move {
            let mut digest_problem = false;
            let mut scan = true;
            let mut force_retry = true;
            loop {
                if scan && email.enabled {
                    if let Err(error) = drain(&email, &owned_path, &consumer, force_retry).await {
                        eprintln!("judge pending mail: {error:#}. Pending events remain saved; correct the reported problem and restart the watcher.");
                    }
                }
                scan = false;
                force_retry = false;
                let job = tokio::select! {
                    job = received.recv() => match job { Some(job) => job, None => break },
                    _ = retry_signal.recv() => {
                        scan = true;
                        force_retry = true;
                        continue;
                    }
                    changed = file_events.changed() => {
                        if let Err(error) = changed.and_then(|()| file_events.rearm()) {
                            eprintln!("judge pending-mail file events: {error:#}. Pending mail remains saved; restart the watcher after correcting the reported problem.");
                            break;
                        }
                        scan = true;
                        continue;
                    }
                };
                #[cfg(test)]
                if let Job::Idle(ready) = job {
                    let _ = ready.send(());
                    continue;
                }
                if let Job::Alert { email: replacement } = job {
                    email = replacement;
                    scan = true;
                    continue;
                }
                let digest = matches!(&job, Job::Digest(_));
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
        Ok(Self {
            pending,
            path: path.to_owned(),
            task: Some(task),
            calendar: Some(calendar),
            schedule,
        })
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
        anyhow::ensure!(
            self.path == path,
            "notification worker owns a different state directory"
        );
        IncomingEvents::new(path)?.enqueue(&event(settings, path, report)?)?;
        // The durable file event is also a wake-up. A closed in-memory channel
        // cannot retract successful admission or turn a review into a failure.
        if self
            .send(Job::Alert {
                email: settings.email.clone(),
            })
            .is_err()
        {
            eprintln!(
                "judge notification worker stopped; pending mail remains saved. {}",
                resume_command(settings, path)
            );
        }
        Ok("queued")
    }

    pub fn digest(
        &self,
        settings: &RuntimeConfig,
        path: &Path,
        outcome: &super::RunOutcome,
    ) -> Result<()> {
        if !settings.email.enabled {
            let _ = self.schedule.send(None);
            return Ok(());
        }
        let time = settings.judge.daily_report_time.ok_or_else(|| {
            anyhow::anyhow!("Set judge.daily_report_time to your chosen local delivery time")
        })?;
        self.schedule
            .send(Some(CalendarJob {
                email: settings.email.clone(),
                database: settings.core.database.clone(),
                path: path.to_owned(),
                outcome: *outcome,
                time,
            }))
            .map_err(|_| {
                anyhow::anyhow!("daily report scheduler is unavailable; restart the watcher")
            })
    }

    pub async fn shutdown(mut self) {
        if let Some(calendar) = self.calendar.take() {
            calendar.abort();
            let _ = calendar.await;
        }
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
        if let Some(calendar) = &self.calendar {
            calendar.abort();
        }
        if let Some(task) = &self.task {
            task.abort();
        }
    }
}

async fn deliver(job: Job) -> Result<Option<bool>> {
    match job {
        #[cfg(test)]
        Job::Idle(_) => unreachable!("test readiness is handled before delivery"),
        Job::Alert { .. } => unreachable!("alert wake-ups are handled before delivery"),
        Job::Digest(CalendarJob {
            email,
            database,
            path,
            outcome,
            time,
        }) => super::digest::tick(&email, &database, Some(&path), &outcome, time)
            .await
            .map(Some),
    }
}

async fn drain(
    email: &EmailConfig,
    path: &Path,
    consumer: &EventConsumer,
    force_retry: bool,
) -> Result<()> {
    let notifier = Notifier::new(email, path)?;
    let mut admitted = false;
    while let Some(pending) = consumer.front()? {
        notifier.accept(&pending.event)?;
        consumer.acknowledge(&pending.id)?;
        admitted = true;
    }
    // Acknowledgements also change the watched file. An empty rescan is not
    // a new retry request, so our own writes cannot create a delivery loop.
    if admitted || force_retry {
        for (_, _, outcome) in notifier.retry_due().await? {
            if outcome != mimir_notifications::Outcome::Sent {
                eprintln!("judge notification delivery: {}. Pending mail is saved. Correct the prerequisite and send SIGHUP to process {} or restart mimir judge watch to retry.", outcome.as_str(), std::process::id());
            }
        }
    }
    Ok(())
}

fn shell_path(path: &Path) -> String {
    format!("'{}'", path.to_string_lossy().replace('\'', "'\\''"))
}

fn resume_command(settings: &RuntimeConfig, path: &Path) -> String {
    format!(
        "Resume delivery: mimir judge watch --config {} --state-dir {}",
        shell_path(&settings.path),
        shell_path(path)
    )
}

pub async fn notify_with(
    mode: Mode<'_>,
    settings: &RuntimeConfig,
    state: &State,
    report: &mut Report,
) -> Result<()> {
    match mode {
        Mode::Standalone => notify(settings, state, report).await,
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
    if !settings.email.enabled {
        report.notification = "disabled".into();
        return Ok(());
    }
    IncomingEvents::new(state.path())?.enqueue(&event(settings, state.path(), report)?)?;
    report.notification = "queued".into();
    eprintln!(
        "Pending mail is saved for the watcher. {}",
        resume_command(settings, state.path())
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::super::state::ConfirmedReview;
    use super::*;

    fn has_saved_alert(path: &Path) -> bool {
        let stored: serde_json::Value =
            serde_json::from_slice(&std::fs::read(path.join("notification-outbox.json")).unwrap())
                .unwrap();
        stored["incidents"]
            .as_object()
            .unwrap()
            .values()
            .any(|incident| incident["outbox"].is_object())
    }

    #[tokio::test]
    async fn idle_watcher_observes_standalone_alert_without_an_in_memory_wakeup() {
        use std::future::{poll_fn, Future};
        use tokio::io::AsyncReadExt;
        let work = crate::judge::harness::RunDir::new_in(&std::env::temp_dir()).unwrap();
        let server = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let text = format!(
            "config_version=1\n[logging]\ndirectory={}\n[database]\nhost='127.0.0.1'\nport=15432\nuser='fixture-user'\ndbname='fixture'\n[judge]\ndaily_report_time={{ hour=9, minute=17 }}\n[llm]\nbackend='command'\nmodel='fixture-model'\ncommand='/bin/true'\n[email]\nenabled=true\nhost='127.0.0.1'\nport={}\ntls='starttls'\nfrom='sender@example.test'\nto=['recipient@example.test']\nauth='none'\n",
            toml::Value::String(work.path().join("logs").display().to_string()), server.local_addr().unwrap().port()
        );
        let path = work.write("config.toml", text.as_bytes()).unwrap();
        let settings = crate::judge::config::load(Some(&path)).unwrap();
        let state = State::lock(work.path().join("state")).unwrap().unwrap();
        let worker = Worker::start(&settings, state.path()).unwrap();
        let (ready, idle) = tokio::sync::oneshot::channel();
        worker.pending.send(Job::Idle(ready)).unwrap();
        idle.await.unwrap();
        assert!(poll_fn(|cx| std::task::Poll::Ready(server.poll_accept(cx).is_pending())).await);
        let mut report = Report::new("blocked", 1, 0, 0, 1, 0);
        // This path has no reference to Worker and cannot send it a channel job.
        let save = notify_with(Mode::Standalone, &settings, &state, &mut report);
        tokio::pin!(save);
        let std::task::Poll::Ready(Ok(())) =
            poll_fn(|cx| std::task::Poll::Ready(save.as_mut().poll(cx))).await
        else {
            panic!("standalone notification was not saved immediately")
        };
        drop(save);
        let (transport, _) = server.accept().await.unwrap();
        // A failed exchange stays pending without a timer or self-triggered
        // delivery loop. An explicit SIGHUP requests the next attempt.
        drop(transport);
        let (ready, idle) = tokio::sync::oneshot::channel();
        worker.pending.send(Job::Idle(ready)).unwrap();
        idle.await.unwrap();
        assert!(poll_fn(|cx| std::task::Poll::Ready(server.poll_accept(cx).is_pending())).await);
        assert_eq!(
            unsafe { libc::kill(std::process::id() as libc::pid_t, libc::SIGHUP) },
            0
        );
        let (mut transport, _) = server.accept().await.unwrap();
        worker.shutdown().await;
        let mut received = Vec::new();
        transport.read_to_end(&mut received).await.unwrap();
        let incoming = IncomingEvents::new(state.path()).unwrap();
        assert!(incoming.claim().unwrap().front().unwrap().is_none());
        assert!(has_saved_alert(state.path()));
    }

    #[tokio::test]
    async fn stalled_smtp_does_not_block_reports_and_shutdown_releases_transport_and_lock() {
        use std::future::{poll_fn, Future};
        use tokio::io::AsyncReadExt;
        let work = crate::judge::harness::RunDir::new_in(&std::env::temp_dir()).unwrap();
        let server = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let text = format!(
            "config_version=1\n[logging]\ndirectory={}\n[database]\nhost='127.0.0.1'\nport=15432\nuser='fixture-user'\ndbname='fixture'\n[judge]\ndaily_report_time={{ hour=10, minute=17 }}\n[llm]\nbackend='command'\nmodel='fixture-model'\ncommand='/bin/true'\n[email]\nenabled=true\nhost='127.0.0.1'\nport={}\ntls='starttls'\nfrom='sender@example.test'\nto=['recipient@example.test']\nauth='none'\n",
            toml::Value::String(work.path().join("logs").display().to_string()), server.local_addr().unwrap().port()
        );
        let path = work.write("config.toml", text.as_bytes()).unwrap();
        let settings = crate::judge::config::load(Some(&path)).unwrap();
        let state = State::lock(work.path().join("state")).unwrap().unwrap();
        {
            let first = crate::judge::runner::finish_report(
                &settings,
                &state,
                Report::new("blocked", 1, 0, 0, 1, 0),
                Mode::Standalone,
            );
            tokio::pin!(first);
            let std::task::Poll::Ready(first) =
                poll_fn(|cx| std::task::Poll::Ready(first.as_mut().poll(cx))).await
            else {
                panic!("Persisting a report waited for notification delivery")
            };
            assert_eq!(first.notification, "queued");
        }
        assert!(poll_fn(|cx| std::task::Poll::Ready(server.poll_accept(cx).is_pending())).await);
        let worker = Worker::start(&settings, state.path()).unwrap();
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
        let calendar_updates = worker.schedule.clone();
        worker.shutdown().await;
        assert!(
            calendar_updates.is_closed(),
            "shutdown must join the calendar owner"
        );
        let mut received = Vec::new();
        transport.read_to_end(&mut received).await.unwrap();
        assert!(Notifier::new(&settings.email, state.path())
            .unwrap()
            .digest_state()
            .is_ok());
        let saved = IncomingEvents::new(state.path()).unwrap();
        let consumer = saved.claim().unwrap();
        let first = consumer.front().unwrap().unwrap();
        assert_eq!(first.event.status, EventStatus::Progress);
        assert!(has_saved_alert(state.path()));
        consumer.acknowledge(&first.id).unwrap();
        assert!(consumer.front().unwrap().is_none());
        drop(consumer);
        let reclaimed = saved.claim().unwrap();
        drop(reclaimed);
        // Restart must retry the saved sender state immediately, without an
        // incoming event or the former five-minute reservation delay.
        let restarted = Worker::start(&settings, state.path()).unwrap();
        let (mut retry_transport, _) = server.accept().await.unwrap();
        restarted.shutdown().await;
        retry_transport.read_to_end(&mut Vec::new()).await.unwrap();
        assert!(has_saved_alert(state.path()));
        assert_eq!(
            resume_command(&settings, state.path()),
            format!(
                "Resume delivery: mimir judge watch --config {} --state-dir {}",
                shell_path(&settings.path),
                shell_path(state.path())
            )
        );
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
