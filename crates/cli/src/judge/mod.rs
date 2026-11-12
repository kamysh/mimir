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
mod watcher;

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
    /// Review pending work, or the explicit selection in configuration.
    Run {
        #[arg(long)]
        config: Option<PathBuf>,
        #[arg(long)]
        state_dir: Option<PathBuf>,
    },
    /// Review continuously; wait for work events when idle. SIGHUP retries a corrected prerequisite.
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
        JudgeCommand::Watch { config, state_dir } => watcher::run(config, state_dir).await,
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

struct RunOutcome {
    code: i32,
    degraded: bool,
    idle: bool,
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
    report.failure_detail = Some(format!("{error:#}"));
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
        eprintln!("Operational logging is unavailable; reviews continue: {error:#}");
    }
    let _=state.write_runtime(&json!({"version":env!("CARGO_PKG_VERSION"),"pid":std::process::id(),"phase":"reviewing","config_format":settings.operations.config_version}));
    let report = match settings.llm.backend {
        config::Backend::Api => match api::ApiBackend::new(&settings.llm) {
            Ok(Some(mut backend)) => runner::run(&settings, &state, &mut backend).await,
            Ok(None) => runner::run(&settings, &state, &mut runner::UnavailableBackend).await,
            Err(error) => {
                runner::setup_failure(&settings, &state, "backend_configuration", &error).await
            }
        },
        _ => match harness::Harness::new(&settings.llm) {
            Ok(mut backend) => runner::run(&settings, &state, &mut backend).await,
            Err(error) => {
                runner::setup_failure(&settings, &state, "backend_configuration", &error).await
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
}
