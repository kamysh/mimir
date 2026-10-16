mod api;
pub mod config;
mod harness;
mod mcp;
mod notification;
mod process;
mod runner;
mod state;

/// Shared policy for both provider APIs and external harnesses. The host still
/// validates scope and revisions; these instructions govern evidence attribution.
fn review_guidance() -> &'static str {
    "Treat the experience as one incident, not independent confirmation of a belief created from that same report. Distinguish tool_result, user_feedback and agent_report; unknown or agent-reported outcomes do not prove success. For a new hypothesis or procedure use review_experience candidates with stable keys, not a separate insert_belief or insert_pattern call. Reuse a pre-existing scoped belief only for genuinely independent evidence. If a standalone belief appears to rest on this incident already, flag possible duplicate provenance in the rationale; do not count it as a second observation. A user requirement is an authoritative constraint, not a causal hypothesis to score. Identify confounding and keep unsupported causal claims tentative. A correction replaces the prior review for this same experience ID."
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
        /// Stop after this many consecutive incomplete or unavailable runs.
        #[arg(long, default_value_t = 3)]
        max_consecutive_failures: usize,
    },
    /// Read the last local run report.
    Status {
        #[arg(long)]
        state_dir: Option<PathBuf>,
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
        JudgeCommand::Run { config, state_dir } => run_once(config, state_dir).await,
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
            let mut failures = 0;
            loop {
                let code = run_once(config.clone(), state_dir.clone()).await;
                if code == INVALID_CONFIG {
                    return code;
                }
                if code == 0 {
                    failures = 0;
                } else {
                    failures += 1;
                    if failures >= max_consecutive_failures {
                        return code;
                    }
                }
                tokio::select! {
                    _ = tokio::signal::ctrl_c() => return 0,
                    _ = tokio::time::sleep(std::time::Duration::from_secs(interval_seconds)) => {}
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
            match state::read(&path) {
                Ok(Some(report)) => {
                    println!(
                        "{}",
                        json!({"status":report.status,"snapshot":true,"report":report})
                    );
                    0
                }
                Ok(None) => {
                    println!("{}", json!({"status":"never_run","snapshot":true}));
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

async fn run_once(config: Option<PathBuf>, state_dir: Option<PathBuf>) -> i32 {
    let settings = match config::load(config.as_deref()) {
        Ok(settings) => settings,
        Err(error) => {
            eprintln!("judge configuration: {error}");
            println!(
                "{}",
                json!({"status":"invalid_config","error":error.to_string()})
            );
            return INVALID_CONFIG;
        }
    };
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
    let state = match state::State::lock(path) {
        Ok(Some(state)) => state,
        Ok(None) => {
            println!("{}", json!({"status":"already_running"}));
            return ALREADY_RUNNING;
        }
        Err(_) => {
            println!(
                "{}",
                json!({"status":"unavailable","reason":"state_unavailable"})
            );
            return UNAVAILABLE;
        }
    };
    let report = match settings.llm.backend {
        config::Backend::Api => match api::ApiBackend::new(&settings.llm) {
            Ok(Some(mut backend)) => runner::run(&settings, &state, &mut backend).await,
            Ok(None) => runner::run(&settings, &state, &mut runner::UnavailableBackend).await,
            Err(_) => {
                println!(
                    "{}",
                    json!({"status":"unavailable","reason":"backend_configuration"})
                );
                return UNAVAILABLE;
            }
        },
        _ => match harness::Harness::new(&settings.llm) {
            Ok(mut backend) => runner::run(&settings, &state, &mut backend).await,
            Err(_) => {
                println!(
                    "{}",
                    json!({"status":"unavailable","reason":"backend_configuration"})
                );
                return UNAVAILABLE;
            }
        },
    };
    let code = match report.status.as_str() {
        "idle" | "complete" => 0,
        "partial" | "blocked" => INCOMPLETE,
        _ => UNAVAILABLE,
    };
    println!(
        "{}",
        serde_json::to_string(&report).unwrap_or_else(|_| "{\"status\":\"unavailable\"}".into())
    );
    code
}
