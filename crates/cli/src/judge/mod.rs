mod api;
pub mod config;
mod digest;
mod harness;
mod mcp;
mod notification;
mod process;
mod runner;
mod state;

/// Shared policy for both provider APIs and external harnesses. The host still
/// validates scope and revisions; these instructions govern evidence attribution.
fn review_guidance() -> &'static str {
    "Treat the experience as one incident, not independent confirmation of a belief created from that same report. Distinguish tool_result, user_feedback and agent_report; unknown or agent-reported outcomes do not prove success. For a new hypothesis or procedure use review_experience candidates with stable keys, not a separate insert_belief or insert_pattern call. Every candidate_key in candidate_feedback or candidate_links must name a belief candidate declared in the candidates array of this same review; use belief_id for an existing belief. Reuse a pre-existing scoped belief only for genuinely independent evidence. If a standalone belief appears to rest on this incident already, flag possible duplicate provenance in the rationale; do not count it as a second observation. A user requirement is an authoritative constraint, not a causal hypothesis to score. Identify confounding and keep unsupported causal claims tentative. A correction replaces the prior review for this same experience ID. Inspect experience_history when correcting a source: a candidate key may be reused only with its exact original kind and declaration; give a revised claim a new key."
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
        /// Delay between runs. Must be at least one minute.
        #[arg(long, default_value_t = 300)]
        interval_seconds: u64,
        /// After this many consecutive failed runs, retry hourly and log
        /// only when the failure episode begins or ends.
        #[arg(long, default_value_t = 3)]
        max_consecutive_failures: usize,
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
    match command {
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
        JudgeCommand::Watch {
            config,
            state_dir,
            interval_seconds,
            max_consecutive_failures,
        } => {
            if interval_seconds < 60 || !(1..=100).contains(&max_consecutive_failures) {
                println!(
                    "{}",
                    json!({"status":"invalid_config","reason":"invalid_watch_bounds"})
                );
                return INVALID_CONFIG;
            }
            let mut watch = WatchState::default();
            let mut digest_problem = false;
            loop {
                let outcome = run_once(config.clone(), state_dir.clone(), true).await;
                let problem = digest::tick(config.as_deref(), state_dir.as_deref(), &outcome)
                    .await
                    .unwrap_or(true);
                if problem != digest_problem {
                    eprintln!(
                        "judge daily email: {}",
                        if problem {
                            "unavailable; will retry"
                        } else {
                            "available"
                        }
                    );
                    digest_problem = problem;
                }
                let (delay, transition) =
                    watch.advance(outcome, interval_seconds, max_consecutive_failures);
                if let Some(message) = transition {
                    eprintln!("{message}");
                }
                tokio::select! {
                    _ = tokio::signal::ctrl_c() => return 0,
                    _ = tokio::time::sleep(std::time::Duration::from_secs(delay)) => {}
                }
            }
        }
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

#[derive(Default)]
struct WatchState {
    consecutive_failures: usize,
    episode_active: bool,
}

impl WatchState {
    fn advance(
        &mut self,
        outcome: RunOutcome,
        interval_seconds: u64,
        backoff_after: usize,
    ) -> (u64, Option<&'static str>) {
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
        if outcome.code == 0 {
            self.consecutive_failures = 0;
        } else {
            self.consecutive_failures = self.consecutive_failures.saturating_add(1);
        }
        let delay = if self.consecutive_failures >= backoff_after {
            interval_seconds.max(3600)
        } else {
            interval_seconds
        };
        (delay, transition)
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

    #[test]
    fn persistent_failures_log_once_and_back_off_without_stopping() {
        let mut watch = WatchState::default();
        let failure = || RunOutcome {
            code: INCOMPLETE,
            degraded: true,
            idle: false,
        };
        assert!(watch.advance(failure(), 60, 3).1.is_some());
        assert_eq!(watch.advance(failure(), 60, 3), (60, None));
        assert_eq!(
            watch.advance(
                RunOutcome {
                    code: INVALID_CONFIG,
                    degraded: true,
                    idle: false,
                },
                60,
                3
            ),
            (3600, None)
        );
        for _ in 0..1000 {
            assert_eq!(watch.advance(failure(), 60, 3), (3600, None));
        }
        assert!(watch
            .advance(
                RunOutcome {
                    code: 0,
                    degraded: false,
                    idle: true,
                },
                60,
                3
            )
            .1
            .is_some());
        assert_eq!(
            watch.advance(
                RunOutcome {
                    code: 0,
                    degraded: false,
                    idle: true,
                },
                60,
                3
            ),
            (60, None)
        );
    }

    #[test]
    fn deferred_review_does_not_repeat_errors_or_exhaust_failure_limit() {
        let mut watch = WatchState::default();
        let deferred = || RunOutcome {
            code: 0,
            degraded: true,
            idle: false,
        };
        assert!(watch.advance(deferred(), 300, 3).1.is_some());
        for _ in 0..1000 {
            assert_eq!(watch.advance(deferred(), 300, 3), (300, None));
        }
        assert_eq!(watch.consecutive_failures, 0);
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
        assert!(watch.advance(failure(), 300, 3).1.is_some());
        for _ in 0..1000 {
            assert_eq!(watch.advance(complete(), 300, 3), (300, None));
            assert_eq!(watch.advance(failure(), 300, 3), (300, None));
        }
        assert_eq!(
            watch.advance(idle(), 300, 3).1,
            Some("judge watch: recovered")
        );
        assert_eq!(watch.advance(idle(), 300, 3), (300, None));
    }
}
