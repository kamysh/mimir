mod api;
pub mod config;
mod config_events;
mod diagnose;
mod digest;
mod evidence;
mod harness;
mod mcp;
mod notification;
mod process;
mod runner;
mod state;

/// Shared policy for both provider APIs and external harnesses. The host still
/// validates scope and revisions; these instructions govern evidence attribution.
fn review_guidance(selected: &mimir_core::learning::ExperienceState) -> String {
    format!(
        "{}\n{}",
        include_str!("review-guidance.txt"),
        evidence::guidance(&selected.experience)
    )
}

use clap::Subcommand;
use serde_json::json;
use std::path::PathBuf;

const INVALID_CONFIG: i32 = 2;
const UNAVAILABLE: i32 = 5;
const INCOMPLETE: i32 = 3;
const ALREADY_RUNNING: i32 = 4;

#[derive(Subcommand)]
pub enum JudgeCommand {
    /// Explain the current failure and recovery action without database/model access.
    Diagnose {
        #[arg(long)]
        config: Option<PathBuf>,
        #[arg(long)]
        state_dir: Option<PathBuf>,
    },
    /// Validate judge, LLM and optional email settings without network or database I/O.
    CheckConfig {
        /// Config file; defaults to MIMIR_CONFIG, then the XDG config path.
        #[arg(long)]
        config: Option<PathBuf>,
    },
    /// Run one bounded review batch.
    Run {
        #[arg(long)]
        config: Option<PathBuf>,
        #[arg(long)]
        state_dir: Option<PathBuf>,
    },
    /// Repeatedly review bounded batches; an empty queue makes no model call.
    Watch {
        #[arg(long)]
        config: Option<PathBuf>,
        #[arg(long)]
        state_dir: Option<PathBuf>,
    },
    /// Read the last local run report.
    Status {
        #[arg(long)]
        state_dir: Option<PathBuf>,
    },
    /// Read the private trace for the first retained failure, or a selected attempt.
    Diagnostics {
        #[arg(long)]
        state_dir: Option<PathBuf>,
        /// List retained attempt IDs without model or tool payloads.
        #[arg(long, conflicts_with = "id")]
        list: bool,
        #[arg(long)]
        id: Option<uuid::Uuid>,
    },
}

pub async fn dispatch(command: JudgeCommand) -> i32 {
    if !matches!(
        &command,
        JudgeCommand::Run { .. } | JudgeCommand::Watch { .. }
    ) {
        return dispatch_inner(command).await;
    }
    // Install before polling work. The outer race covers startup, model/tool
    // requests and watch sleeps; dropping its work future drops owned children.
    let listeners = (|| {
        use tokio::signal::unix::{signal, SignalKind};
        Ok::<_, std::io::Error>((
            signal(SignalKind::interrupt())?,
            signal(SignalKind::terminate())?,
        ))
    })();
    let (mut interrupt, mut terminate) = match listeners {
        Ok(listeners) => listeners,
        Err(error) => {
            eprintln!("Cannot install judge stop listeners: {error}");
            return UNAVAILABLE;
        }
    };
    tokio::select! {
        biased;
        _ = interrupt.recv() => 0,
        _ = terminate.recv() => 0,
        code = dispatch_inner(command) => code,
    }
}

async fn dispatch_inner(command: JudgeCommand) -> i32 {
    match command {
        JudgeCommand::Diagnose { config, state_dir } => {
            match diagnose::show(config.as_deref(), state_dir.as_deref()) {
                Ok(()) => 0,
                Err(error) => {
                    eprintln!("Cannot read diagnostic state: {error}");
                    UNAVAILABLE
                }
            }
        }
        JudgeCommand::CheckConfig { config } => match config::load(config.as_deref()) {
            Ok(_settings) => {
                println!("{}", json!({"status":"valid","schema_version":1}));
                0
            }
            Err(error) => {
                eprintln!("judge configuration: {error}");
                println!(
                    "{}",
                    json!({"status":"invalid_config","error":error.to_string()})
                );
                INVALID_CONFIG
            }
        },
        JudgeCommand::Run { config, state_dir } => run_once(config, state_dir, false).await.code,
        JudgeCommand::Watch { config, state_dir } => watch(config, state_dir).await,
        JudgeCommand::Status { state_dir } => {
            let path = match state::resolve(state_dir.as_deref()) {
                Ok(path) => path,
                Err(_) => {
                    println!(
                        "{}",
                        json!({"status":"invalid_config","reason":"invalid_state_path"})
                    );
                    return INVALID_CONFIG;
                }
            };
            match (state::read(&path), state::read_failure(&path)) {
                (Ok(Some(report)), Ok(last_failure)) => {
                    println!(
                        "{}",
                        json!({"status":report.status,"snapshot":true,"report":report,"last_failure":last_failure})
                    );
                    0
                }
                (Ok(None), Ok(last_failure)) => {
                    println!(
                        "{}",
                        json!({"status":"never_run","snapshot":true,"last_failure":last_failure})
                    );
                    0
                }
                _ => {
                    println!(
                        "{}",
                        json!({"status":"unavailable","reason":"state_unavailable"})
                    );
                    UNAVAILABLE
                }
            }
        }
        JudgeCommand::Diagnostics {
            state_dir,
            list,
            id,
        } => {
            let path = match state::resolve(state_dir.as_deref()) {
                Ok(path) => path,
                Err(_) => {
                    println!(
                        "{}",
                        json!({"status":"invalid_config","reason":"invalid_state_path"})
                    );
                    return INVALID_CONFIG;
                }
            };
            let result = (|| {
                let diagnostics = state::read_diagnostics(&path)?;
                if list {
                    let attempts = diagnostics
                        .attempts
                        .iter()
                        .map(|trace| {
                            json!({
                                "id":trace.id,
                                "status":trace.status,
                                "block_reason":trace.block_reason,
                                "started_at":trace.started_at,
                                "finished_at":trace.finished_at,
                                "selected_ids":trace.selected_ids,
                                "events":trace.events.len(),
                                "events_omitted":trace.events_omitted
                            })
                        })
                        .collect::<Vec<_>>();
                    return Ok::<_, anyhow::Error>(
                        json!({"status":"available","attempts":attempts}),
                    );
                }
                let first_failure =
                    state::read_failure(&path)?.and_then(|incident| incident.first.diagnostics_id);
                let selected = match id.or(first_failure) {
                    Some(id) => diagnostics.attempts.iter().find(|trace| trace.id == id),
                    None => diagnostics.attempts.last(),
                };
                Ok(selected.map_or_else(
                    || json!({"status":"no_diagnostics"}),
                    |trace| json!({"status":"available","trace":trace}),
                ))
            })();
            match result {
                Ok(value) => {
                    println!("{value}");
                    0
                }
                Err(_) => {
                    println!(
                        "{}",
                        json!({"status":"unavailable","reason":"state_unavailable"})
                    );
                    UNAVAILABLE
                }
            }
        }
    }
}

fn retry_command() -> String {
    format!("kill -HUP {}", std::process::id())
}

async fn receive_retry(signal: &mut tokio::signal::unix::Signal) -> anyhow::Result<()> {
    signal
        .recv()
        .await
        .ok_or_else(|| anyhow::anyhow!("SIGHUP retry event source closed"))
}

async fn wait_for_explicit_retry(signal: &mut tokio::signal::unix::Signal) -> anyhow::Result<bool> {
    tokio::select! {
        _ = tokio::signal::ctrl_c() => Ok(false),
        received = receive_retry(signal) => received.map(|()| true),
    }
}

fn write_watch_runtime(
    state_dir: Option<&std::path::Path>,
    next: NextAttempt,
    cause: Option<&str>,
) {
    let runtime = json!({
        "version":env!("CARGO_PKG_VERSION"), "pid":std::process::id(),
        "phase":match next {
            NextAttempt::Immediately => "running",
            NextAttempt::WorkEvent => "waiting_for_work",
            NextAttempt::Prerequisite => "waiting_for_prerequisite",
        },
        "waiting_for": if next == NextAttempt::Prerequisite {Some("configuration_change_or_explicit_retry")} else {None},
        "cause":cause, "retry_command":retry_command(),
    });
    if let Ok(path) = state::resolve(state_dir) {
        if let Ok(Some(state)) = state::State::lock(path) {
            let _ = state.write_runtime(&runtime);
        }
    }
}

async fn load_watch_subscription(
    path: &std::path::Path,
    state_dir: Option<&std::path::Path>,
    events: &mut config_events::ConfigEvents,
    retry: &mut tokio::signal::unix::Signal,
) -> anyhow::Result<
    Option<(
        config::RuntimeConfig,
        mimir_core::db::ReviewQueueSubscription,
    )>,
> {
    load_watch_connection(path, state_dir, events, retry, |database| async move {
        mimir_core::db::ReviewQueueSubscription::connect(&database).await
    })
    .await
}

async fn load_watch_connection<Connection, Connect, Attempt>(
    path: &std::path::Path,
    state_dir: Option<&std::path::Path>,
    events: &mut config_events::ConfigEvents,
    retry: &mut tokio::signal::unix::Signal,
    mut connect: Connect,
) -> anyhow::Result<Option<(config::RuntimeConfig, Connection)>>
where
    Connect: FnMut(mimir_core::config::DatabaseConfig) -> Attempt,
    Attempt: std::future::Future<Output = anyhow::Result<Connection>>,
{
    loop {
        let Some(settings) = load_watch_settings(path, state_dir, events, retry).await? else {
            return Ok(None);
        };
        let connected = tokio::select! {
            _ = tokio::signal::ctrl_c() => return Ok(None),
            changed = events.changed() => { changed?; continue; },
            received = receive_retry(retry) => { received?; continue; },
            connected = connect(settings.core.database.clone()) => connected,
        };
        match connected {
            Ok(subscription) => return Ok(Some((settings, subscription))),
            Err(error) => {
                write_watch_runtime(
                    state_dir,
                    NextAttempt::Prerequisite,
                    Some("database_subscription_failed"),
                );
                eprintln!("Unable to subscribe to review work: {error:#}. Restore the reported database prerequisite, then edit the selected configuration or explicitly retry with: {}. No pending work was selected.", retry_command());
            }
        }
        tokio::select! {
            _ = tokio::signal::ctrl_c() => return Ok(None),
            changed = events.changed() => changed?,
            received = receive_retry(retry) => received?,
        }
    }
}

async fn watch(config: Option<PathBuf>, state_dir: Option<PathBuf>) -> i32 {
    let mut retry = match tokio::signal::unix::signal(tokio::signal::unix::SignalKind::hangup()) {
        Ok(signal) => signal,
        Err(error) => {
            eprintln!("Unable to register the SIGHUP retry signal: {error}. Correct the reported OS error and restart the watcher.");
            return UNAVAILABLE;
        }
    };
    let path = match config::resolved_path(config.as_deref()) {
        Ok(path) => path,
        Err(error) => {
            eprintln!("Invalid watcher configuration path: {error:#}. Choose a valid --config path and retry.");
            return INVALID_CONFIG;
        }
    };
    let mut watch = WatchState::default();
    let mut digest_problem = false;
    'observe: loop {
        let mut events = match config_events::ConfigEvents::new(&path) {
            Ok(events) => events,
            Err(error) => {
                write_watch_runtime(
                    state_dir.as_deref(),
                    NextAttempt::Prerequisite,
                    Some("configuration_event_source_unavailable"),
                );
                eprintln!("Unable to observe configuration changes for {}: {error:#}. Correct the reported OS prerequisite, then explicitly retry with: {}", path.display(), retry_command());
                match wait_for_explicit_retry(&mut retry).await {
                    Ok(true) => continue,
                    Ok(false) => return 0,
                    Err(error) => {
                        eprintln!(
                            "Retry event source unavailable: {error:#}. Restart the watcher."
                        );
                        return UNAVAILABLE;
                    }
                }
            }
        };
        let (mut settings, mut subscription) = match load_watch_subscription(
            &path,
            state_dir.as_deref(),
            &mut events,
            &mut retry,
        )
        .await
        {
            Ok(Some(ready)) => ready,
            Ok(None) => return 0,
            Err(error) => {
                write_watch_runtime(
                    state_dir.as_deref(),
                    NextAttempt::Prerequisite,
                    Some("watch_event_source_unavailable"),
                );
                eprintln!("Watcher event source unavailable: {error:#}. Correct the reported prerequisite, then explicitly retry with: {}", retry_command());
                match wait_for_explicit_retry(&mut retry).await {
                    Ok(true) => continue,
                    Ok(false) => return 0,
                    Err(error) => {
                        eprintln!(
                            "Retry event source unavailable: {error:#}. Restart the watcher."
                        );
                        return UNAVAILABLE;
                    }
                }
            }
        };
        loop {
            let outcome = run_with_settings(&settings, state_dir.clone(), true).await;
            let problem = digest::tick(&settings, state_dir.as_deref(), &outcome)
                .await
                .unwrap_or(true);
            if problem != digest_problem {
                eprintln!(
                    "judge daily email: {}",
                    if problem {
                        "unavailable; awaiting the next reporting event"
                    } else {
                        "available"
                    }
                );
                digest_problem = problem;
            }
            let (next, transition) = watch.advance(outcome);
            write_watch_runtime(
                state_dir.as_deref(),
                next,
                (next == NextAttempt::Prerequisite).then_some("incomplete_or_degraded_batch"),
            );
            if let Some(message) = transition {
                eprintln!("{message}");
            }
            if next == NextAttempt::Prerequisite {
                eprintln!("Review work is paused for correction. Inspect mimir judge diagnose and correct the reported prerequisite. Configuration edits reload automatically; explicitly retry with: {}", retry_command());
            }
            let reconnect = tokio::select! {
                biased;
                _ = tokio::signal::ctrl_c() => return 0,
                changed = events.changed() => {
                    if let Err(error) = changed {
                        write_watch_runtime(state_dir.as_deref(), NextAttempt::Prerequisite, Some("watch_event_source_unavailable")); eprintln!("Watcher event source unavailable: {error:#}. Correct the reported prerequisite, then explicitly retry with: {}", retry_command());
                        match wait_for_explicit_retry(&mut retry).await { Ok(true) => continue 'observe, Ok(false) => return 0, Err(error) => {eprintln!("Retry event source unavailable: {error:#}. Restart the watcher."); return UNAVAILABLE;} }
                    }
                    true
                },
                received = receive_retry(&mut retry) => {
                    if let Err(error) = received { eprintln!("Retry event source unavailable: {error:#}. Restart the watcher."); return UNAVAILABLE; }
                    true
                },
                result = next.wait_with(std::future::pending, || subscription.changed()) => {
                    if let Err(error) = result {
                        eprintln!("Review work listener disconnected: {error:#}. Re-subscribing before reading saved pending work.");
                        true
                    } else {false}
                },
            };
            if reconnect {
                // A durable scan covers missed hints after the new LISTEN.
                // Close the old connection before waiting for its replacement.
                drop(subscription);
                match load_watch_subscription(&path, state_dir.as_deref(), &mut events, &mut retry)
                    .await
                {
                    Ok(Some((replacement, connected))) => {
                        settings = replacement;
                        subscription = connected;
                    }
                    Ok(None) => return 0,
                    Err(error) => {
                        write_watch_runtime(
                            state_dir.as_deref(),
                            NextAttempt::Prerequisite,
                            Some("watch_event_source_unavailable"),
                        );
                        eprintln!("Watcher event source unavailable: {error:#}. Correct the reported prerequisite, then explicitly retry with: {}", retry_command());
                        match wait_for_explicit_retry(&mut retry).await {
                            Ok(true) => continue 'observe,
                            Ok(false) => return 0,
                            Err(error) => {
                                eprintln!("Retry event source unavailable: {error:#}. Restart the watcher.");
                                return UNAVAILABLE;
                            }
                        }
                    }
                }
            }
        }
    }
}

struct RunOutcome {
    code: i32,
    degraded: bool,
    idle: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum NextAttempt {
    Immediately,
    WorkEvent,
    Prerequisite,
}

impl NextAttempt {
    async fn wait_with<F, W, C, E>(self, retry: F, changed: C) -> anyhow::Result<()>
    where
        F: FnOnce() -> W,
        W: std::future::Future<Output = ()>,
        C: FnOnce() -> E,
        E: std::future::Future<Output = anyhow::Result<()>>,
    {
        match self {
            Self::Immediately => Ok(()),
            Self::WorkEvent => changed().await,
            Self::Prerequisite => {
                retry().await;
                Ok(())
            }
        }
    }
}

#[derive(Default)]
struct WatchState {
    episode_active: bool,
}

impl WatchState {
    fn advance(&mut self, outcome: RunOutcome) -> (NextAttempt, Option<&'static str>) {
        let transition = if outcome.degraded {
            if self.episode_active {
                None
            } else {
                Some(match outcome.code {
                    INVALID_CONFIG => "judge watch: invalid configuration or state path; inspect mimir judge status",
                    ALREADY_RUNNING => "judge watch: another judge holds the state lock",
                    UNAVAILABLE => "judge watch: state unavailable; inspect local permissions",
                    _ => "judge watch: incomplete run; inspect mimir judge status",
                })
            }
        } else if outcome.idle && self.episode_active {
            Some("judge watch: recovered")
        } else {
            None
        };
        if outcome.degraded {
            self.episode_active = true;
        } else if outcome.idle {
            self.episode_active = false;
        }
        let next = if outcome.code == 0 && !outcome.degraded && !outcome.idle {
            NextAttempt::Immediately
        } else if outcome.code == 0 && !outcome.degraded && outcome.idle {
            NextAttempt::WorkEvent
        } else {
            NextAttempt::Prerequisite
        };
        (next, transition)
    }
}

async fn load_watch_settings(
    path: &std::path::Path,
    state_dir: Option<&std::path::Path>,
    events: &mut config_events::ConfigEvents,
    retry: &mut tokio::signal::unix::Signal,
) -> anyhow::Result<Option<config::RuntimeConfig>> {
    loop {
        events.rearm()?;
        match config::load(Some(path)) {
            Ok(settings) => return Ok(Some(settings)),
            Err(error) => {
                record_invalid_configuration(state_dir, &error);
                eprintln!("Watcher configuration needs correction: {error:#}. Run mimir judge check-config --config {}, correct that file, and save it. Save the correction or send the printed SIGHUP retry command; no batch will start with invalid settings.", path.display());
            }
        }
        tokio::select! {
            changed = events.changed() => changed?,
            received = receive_retry(retry) => received?,
            _ = tokio::signal::ctrl_c() => return Ok(None),
        }
    }
}

fn record_invalid_configuration(state_dir: Option<&std::path::Path>, error: &anyhow::Error) {
    let Ok(path) = state::resolve(state_dir) else {
        return;
    };
    let Ok(Some(state)) = state::State::lock(path) else {
        return;
    };
    let mut report = state::Report::new("blocked", 0, 0, 0, 0, 0);
    report.block_reason = Some("invalid_config".into());
    report.failure_detail = Some(state::bounded(&format!("{error:#}"), 512));
    let _ = state.record_incident(&report);
    let _ = state.write(&report);
}

async fn run_once(
    config: Option<PathBuf>,
    state_dir: Option<PathBuf>,
    watch_mode: bool,
) -> RunOutcome {
    let settings = match config::load(config.as_deref()) {
        Ok(settings) => settings,
        Err(error) => {
            record_invalid_configuration(state_dir.as_deref(), &error);
            if !watch_mode {
                eprintln!("judge configuration: {error}");
                println!(
                    "{}",
                    json!({"status":"invalid_config","error":error.to_string()})
                );
            }
            return RunOutcome {
                code: INVALID_CONFIG,
                degraded: true,
                idle: false,
            };
        }
    };
    run_with_settings(&settings, state_dir, watch_mode).await
}

// Used by watcher startup after it subscribes with these exact settings. It
// must not reread the mutable source file between subscription and first scan.
async fn run_with_settings(
    settings: &config::RuntimeConfig,
    state_dir: Option<PathBuf>,
    watch_mode: bool,
) -> RunOutcome {
    let path = match state::resolve(state_dir.as_deref()) {
        Ok(path) => path,
        Err(_) => {
            if !watch_mode {
                println!(
                    "{}",
                    json!({"status":"invalid_config","reason":"invalid_state_path"})
                );
            }
            return RunOutcome {
                code: INVALID_CONFIG,
                degraded: true,
                idle: false,
            };
        }
    };
    let state = match state::State::lock(path) {
        Ok(Some(state)) => state,
        Ok(None) => {
            if !watch_mode {
                println!("{}", json!({"status":"already_running"}));
            }
            return RunOutcome {
                code: ALREADY_RUNNING,
                degraded: true,
                idle: false,
            };
        }
        Err(_) => {
            if !watch_mode {
                println!(
                    "{}",
                    json!({"status":"unavailable","reason":"state_unavailable"})
                );
            }
            return RunOutcome {
                code: UNAVAILABLE,
                degraded: true,
                idle: false,
            };
        }
    };
    if let Err(error) = settings.operations.logging.prepare().and_then(|()| {
        settings.operations.logging.event(
            "judge",
            &format!(
                "starting batch; version={}; config_format={}; pid={}",
                env!("CARGO_PKG_VERSION"),
                settings.operations.config_version,
                std::process::id()
            ),
        )
    }) {
        let mut report = state::Report::new("blocked", 0, 0, 0, 0, 0);
        report.block_reason = Some("invalid_config".into());
        report.failure_detail = Some(format!("logging.directory is unavailable: {error}"));
        let _ = state.write(&report);
        if !watch_mode {
            eprintln!("Cannot write configured operational logs: {error}");
        }
        return RunOutcome {
            code: INVALID_CONFIG,
            degraded: true,
            idle: false,
        };
    }
    let _=state.write_runtime(&json!({"version":env!("CARGO_PKG_VERSION"),"pid":std::process::id(),"phase":"reviewing","config_format":settings.operations.config_version}));
    let report = match settings.llm.backend {
        config::Backend::Api => match api::ApiBackend::new(&settings.llm) {
            Ok(Some(mut backend)) => runner::run(settings, &state, &mut backend).await,
            Ok(None) => runner::run(settings, &state, &mut runner::UnavailableBackend).await,
            Err(error) => {
                runner::setup_failure(settings, &state, "backend_configuration", &error).await
            }
        },
        _ => match harness::Harness::new(&settings.llm) {
            Ok(mut backend) => runner::run(settings, &state, &mut backend).await,
            Err(error) => {
                runner::setup_failure(settings, &state, "backend_configuration", &error).await
            }
        },
    };
    let _ = settings.operations.logging.event(
        "judge",
        &format!(
            "batch {}; confirmed={}; pending={}; unavailable={}; reason={}; diagnostics={}",
            report.status,
            report.confirmed,
            report.pending,
            report.unavailable,
            report.block_reason.as_deref().unwrap_or("none"),
            report
                .diagnostics_id
                .map_or_else(|| "none".into(), |id| id.to_string())
        ),
    );
    let _=state.write_runtime(&json!({"version":env!("CARGO_PKG_VERSION"),"pid":std::process::id(),"phase":"batch_finished","outcome":report.status,"config_format":settings.operations.config_version}));
    let code = match report.status.as_str() {
        "idle" | "complete" => 0,
        "partial" | "blocked" => INCOMPLETE,
        _ => UNAVAILABLE,
    };
    if !watch_mode {
        println!(
            "{}",
            serde_json::to_string(&report)
                .unwrap_or_else(|_| "{\"status\":\"unavailable\"}".into())
        );
    }
    let deferred = report.block_reason.as_deref() == Some("review_deferred");
    RunOutcome {
        code: if watch_mode && deferred { 0 } else { code },
        degraded: matches!(report.status.as_str(), "blocked" | "partial"),
        idle: report.status == "idle",
    }
}

#[cfg(test)]
mod watch_tests {
    use super::*;
    use std::os::unix::fs::OpenOptionsExt;

    #[tokio::test]
    async fn malformed_config_waits_for_correction_without_replacing_admitted_settings() {
        use std::future::{poll_fn, Future};
        let work = harness::RunDir::new_in(&std::env::temp_dir()).unwrap();
        let text = |dbname: &str| {
            format!(
            "config_version=1\n[logging]\ndirectory={}\n[database]\nhost='127.0.0.1'\nport=15432\nuser='fixture-user'\ndbname={}\n[judge]\n[llm]\nbackend='command'\nmodel='fixture-model'\ncommand='/bin/true'\n",
            toml::Value::String(work.path().join("logs").display().to_string()),
            toml::Value::String(dbname.to_owned())
        )
        };
        let path = work
            .write("config.toml", text("admitted").as_bytes())
            .unwrap();
        let admitted = config::load(Some(&path)).unwrap();
        let invalid = "[database]\nunknown_field=true\n";
        std::fs::write(&path, invalid).unwrap();
        let mut events = config_events::ConfigEvents::new(&path).unwrap();
        let state = work.path().join("state");
        let mut retry =
            tokio::signal::unix::signal(tokio::signal::unix::SignalKind::hangup()).unwrap();
        let corrected = load_watch_settings(&path, Some(&state), &mut events, &mut retry);
        tokio::pin!(corrected);
        assert!(
            poll_fn(|cx| std::task::Poll::Ready(corrected.as_mut().poll(cx).is_pending())).await
        );
        assert_eq!(admitted.core.database.dbname, "admitted");
        assert_eq!(std::fs::read_to_string(&path).unwrap(), invalid);
        assert_eq!(
            state::read(&state)
                .unwrap()
                .unwrap()
                .block_reason
                .as_deref(),
            Some("invalid_config")
        );
        std::fs::write(&path, text("corrected")).unwrap();
        let corrected = corrected.await.unwrap().unwrap();
        assert_eq!(corrected.core.database.dbname, "corrected");
        assert_eq!(admitted.core.database.dbname, "admitted");
    }

    #[tokio::test]
    async fn idle_waits_for_an_event_without_a_timer_or_busy_loop() {
        use std::future::{poll_fn, Future};
        let mut watch = WatchState::default();
        let (next, _) = watch.advance(RunOutcome {
            code: 0,
            degraded: false,
            idle: true,
        });
        assert_eq!(next, NextAttempt::WorkEvent);
        let (wake, received) = tokio::sync::oneshot::channel();
        let wait = next.wait_with(
            || -> std::future::Ready<()> { panic!("Idle work must not construct a timer") },
            || async {
                received.await?;
                Ok(())
            },
        );
        tokio::pin!(wait);
        assert!(poll_fn(|cx| std::task::Poll::Ready(wait.as_mut().poll(cx).is_pending())).await);
        wake.send(()).unwrap();
        wait.await.unwrap();
    }

    #[tokio::test]
    async fn failed_connection_waits_for_correction_without_resubmitting() {
        use std::future::{poll_fn, Future};
        use std::sync::{
            atomic::{AtomicUsize, Ordering},
            Arc,
        };
        let work = harness::RunDir::new_in(&std::env::temp_dir()).unwrap();
        let text = |dbname: &str| {
            format!(
            "config_version=1\n[logging]\ndirectory={}\n[database]\nhost='127.0.0.1'\nport=15432\nuser='fixture-user'\ndbname={}\n[judge]\n[llm]\nbackend='command'\nmodel='fixture-model'\ncommand='/bin/true'\n",
            toml::Value::String(work.path().join("logs").display().to_string()),
            toml::Value::String(dbname.to_owned()))
        };
        let path = work
            .write("config.toml", text("admitted").as_bytes())
            .unwrap();
        let mut events = config_events::ConfigEvents::new(&path).unwrap();
        let mut retry =
            tokio::signal::unix::signal(tokio::signal::unix::SignalKind::hangup()).unwrap();
        let calls = Arc::new(AtomicUsize::new(0));
        let attempts = calls.clone();
        let state = work.path().join("state");
        let connection = load_watch_connection(
            &path,
            Some(&state),
            &mut events,
            &mut retry,
            move |database| {
                attempts.fetch_add(1, Ordering::SeqCst);
                std::future::ready(if database.dbname == "corrected" {
                    Ok(())
                } else {
                    Err(anyhow::anyhow!("fixture database unavailable"))
                })
            },
        );
        tokio::pin!(connection);
        assert!(
            poll_fn(|cx| std::task::Poll::Ready(connection.as_mut().poll(cx).is_pending())).await
        );
        assert_eq!(calls.load(Ordering::SeqCst), 1);
        assert!(
            poll_fn(|cx| std::task::Poll::Ready(connection.as_mut().poll(cx).is_pending())).await
        );
        assert_eq!(calls.load(Ordering::SeqCst), 1);
        std::fs::write(&path, text("corrected")).unwrap();
        let (settings, ()) = connection.await.unwrap().unwrap();
        assert_eq!(settings.core.database.dbname, "corrected");
        assert_eq!(calls.load(Ordering::SeqCst), 2);
    }

    #[tokio::test]
    async fn ready_batches_continue_without_constructing_a_timer() {
        let mut watch = WatchState::default();
        let ready = [
            RunOutcome {
                code: 0,
                degraded: false,
                idle: false,
            },
            RunOutcome {
                code: 0,
                degraded: false,
                idle: false,
            },
        ];
        let mut completed = 0;
        for outcome in ready {
            let (next, _) = watch.advance(outcome);
            assert_eq!(next, NextAttempt::Immediately);
            next.wait_with(
                || -> std::future::Ready<()> { panic!("Ready work must not construct a timer") },
                || -> std::future::Ready<anyhow::Result<()>> {
                    panic!("Ready work must not wait for a work event")
                },
            )
            .await
            .unwrap();
            completed += 1;
        }
        assert_eq!(completed, 2);
    }

    #[tokio::test]
    async fn invalid_configuration_replaces_stale_status_and_preserves_incident() {
        let dir =
            std::env::temp_dir().join(format!("mimir-judge-config-test-{}", uuid::Uuid::new_v4()));
        std::fs::create_dir(&dir).unwrap();
        let config = dir.join("invalid.toml");
        std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(&config)
            .unwrap();
        let state_dir = dir.join("state");
        let state = state::State::lock(state_dir.clone()).unwrap().unwrap();
        state
            .write(&state::Report::new("idle", 0, 0, 0, 0, 0))
            .unwrap();
        drop(state);
        let outcome = run_once(Some(config), Some(state_dir.clone()), true).await;
        assert_eq!(outcome.code, INVALID_CONFIG);
        let report = state::read(&state_dir).unwrap().unwrap();
        assert_eq!(report.status, "blocked");
        assert_eq!(report.block_reason.as_deref(), Some("invalid_config"));
        let incident = state::read_failure(&state_dir).unwrap().unwrap();
        assert_eq!(
            incident.first.block_reason.as_deref(),
            Some("invalid_config")
        );
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn failed_and_deferred_work_wait_for_a_prerequisite_without_count_policy() {
        let mut watch = WatchState::default();
        let failure = || RunOutcome {
            code: INCOMPLETE,
            degraded: true,
            idle: false,
        };
        assert_eq!(watch.advance(failure()).0, NextAttempt::Prerequisite);
        assert_eq!(watch.advance(failure()), (NextAttempt::Prerequisite, None));
        assert_eq!(
            watch.advance(RunOutcome {
                code: 0,
                degraded: true,
                idle: false
            }),
            (NextAttempt::Prerequisite, None)
        );
    }

    #[test]
    fn completed_batches_do_not_close_a_failure_episode() {
        let mut watch = WatchState::default();
        let failure = || RunOutcome {
            code: INCOMPLETE,
            degraded: true,
            idle: false,
        };
        let complete = || RunOutcome {
            code: 0,
            degraded: false,
            idle: false,
        };
        let idle = || RunOutcome {
            code: 0,
            degraded: false,
            idle: true,
        };
        assert!(watch.advance(failure()).1.is_some());
        assert_eq!(watch.advance(complete()), (NextAttempt::Immediately, None));
        assert_eq!(watch.advance(failure()), (NextAttempt::Prerequisite, None));
        assert_eq!(watch.advance(idle()).1, Some("judge watch: recovered"));
        assert_eq!(watch.advance(idle()), (NextAttempt::WorkEvent, None));
    }

    #[tokio::test]
    async fn prerequisite_wait_does_not_poll_unrelated_work_and_resumes_on_explicit_retry() {
        use std::future::{poll_fn, Future};
        let (send, receive) = tokio::sync::oneshot::channel();
        let wait = NextAttempt::Prerequisite.wait_with(
            || async {
                receive.await.unwrap();
            },
            || -> std::future::Ready<anyhow::Result<()>> {
                panic!("A work event cannot correct a missing prerequisite")
            },
        );
        tokio::pin!(wait);
        assert!(poll_fn(|cx| std::task::Poll::Ready(wait.as_mut().poll(cx).is_pending())).await);
        send.send(()).unwrap();
        wait.await.unwrap();
    }

    #[test]
    fn watch_has_no_interval_or_failure_threshold_options() {
        use clap::Parser;
        #[derive(Parser)]
        struct Args {
            #[command(subcommand)]
            command: JudgeCommand,
        }
        assert!(Args::try_parse_from(["fixture", "watch"]).is_ok());
        assert!(Args::try_parse_from(["fixture", "watch", "--interval-seconds", "300"]).is_err());
        assert!(
            Args::try_parse_from(["fixture", "watch", "--max-consecutive-failures", "3"]).is_err()
        );
    }

    #[tokio::test]
    async fn sighup_wakes_the_owned_child_retry_receiver() {
        use std::io::{BufRead, Write};
        const CHILD: &str = "MIMIR_TEST_RETRY_SIGNAL_CHILD";
        if std::env::var(CHILD).as_deref() == Ok("1") {
            let mut retry =
                tokio::signal::unix::signal(tokio::signal::unix::SignalKind::hangup()).unwrap();
            println!("retry-ready");
            std::io::stdout().flush().unwrap();
            receive_retry(&mut retry).await.unwrap();
            println!("retry-received");
            return;
        }
        struct OwnedChild(std::process::Child);
        impl Drop for OwnedChild {
            fn drop(&mut self) {
                if self.0.try_wait().is_ok_and(|status| status.is_none()) {
                    let _ = self.0.kill();
                }
                let _ = self.0.wait();
            }
        }
        use std::os::unix::fs::DirBuilderExt;
        // Keep complete child output outside the Nix shell's temporary files.
        let log_root = std::env::var_os("MIMIR_TEST_LOG_DIRECTORY")
            .map(PathBuf::from)
            .unwrap_or_else(|| PathBuf::from("/tmp"));
        let logs = log_root.join(format!("mimir-retry-signal-{}", uuid::Uuid::new_v4()));
        std::fs::DirBuilder::new()
            .mode(0o700)
            .create(&logs)
            .unwrap();
        let stderr = std::fs::File::create(logs.join("child.stderr")).unwrap();
        let mut stdout_log = std::fs::File::create(logs.join("child.stdout")).unwrap();
        let mut child = OwnedChild(
            std::process::Command::new(std::env::current_exe().unwrap())
                .args([
                    "--exact",
                    "judge::watch_tests::sighup_wakes_the_owned_child_retry_receiver",
                    "--nocapture",
                ])
                .env(CHILD, "1")
                .stdin(std::process::Stdio::null())
                .stdout(std::process::Stdio::piped())
                .stderr(stderr)
                .spawn()
                .unwrap(),
        );
        let mut output = std::io::BufReader::new(child.0.stdout.take().unwrap());
        let mut line = Vec::new();
        loop {
            line.clear();
            assert_ne!(
                output.read_until(b'\n', &mut line).unwrap(),
                0,
                "child exited before registering SIGHUP; logs {}",
                logs.display()
            );
            stdout_log.write_all(&line).unwrap();
            stdout_log.flush().unwrap();
            if line == b"retry-ready\n" {
                break;
            }
        }
        assert_eq!(
            unsafe { libc::kill(child.0.id() as libc::pid_t, libc::SIGHUP) },
            0
        );
        let mut received = false;
        loop {
            line.clear();
            if output.read_until(b'\n', &mut line).unwrap() == 0 {
                break;
            }
            stdout_log.write_all(&line).unwrap();
            stdout_log.flush().unwrap();
            received |= line == b"retry-received\n";
        }
        assert!(
            received,
            "child did not observe retry; logs {}",
            logs.display()
        );
        assert!(child.0.wait().unwrap().success());
        eprintln!("SIGHUP child output retained at {}", logs.display());
    }
}
