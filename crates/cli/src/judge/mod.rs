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
mod repair;
mod runner;
mod state;
mod transcript;
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

use chrono::Timelike;
use clap::Subcommand;
use serde_json::json;
use std::path::PathBuf;
use std::time::Duration;

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
    /// Inspect or repair a deferred review for one source revision.
    Repair {
        #[arg(long)]
        config: Option<PathBuf>,
        #[arg(long)]
        state_dir: Option<PathBuf>,
        #[arg(long)]
        experience: uuid::Uuid,
        #[arg(long)]
        revision: i64,
        /// Start a new judge attempt from the stored source.
        #[arg(long, conflicts_with = "review")]
        retry: bool,
        /// Submit a complete corrected review JSON file.
        #[arg(long)]
        review: Option<PathBuf>,
    },
    /// Read the last local run report.
    Status {
        #[arg(long)]
        state_dir: Option<PathBuf>,
    },
    /// Read a failed review transcript.
    Diagnostics {
        #[arg(long)]
        config: Option<PathBuf>,
        #[arg(long)]
        state_dir: Option<PathBuf>,
        /// List retained attempt IDs without model or tool payloads.
        #[arg(long, conflicts_with = "id")]
        list: bool,
        #[arg(long)]
        id: Option<uuid::Uuid>,
        /// Print the complete machine-readable transcript.
        #[arg(long)]
        json: bool,
    },
}

pub async fn dispatch(command: JudgeCommand) -> i32 {
    if !matches!(
        &command,
        JudgeCommand::Run { .. } | JudgeCommand::Watch { .. } | JudgeCommand::Repair { .. }
    ) {
        return dispatch_inner(command).await;
    }
    let interrupted = if matches!(&command, JudgeCommand::Repair { .. }) {
        INCOMPLETE
    } else {
        0
    };
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
        _ = interrupt.recv() => interrupted,
        _ = terminate.recv() => interrupted,
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
        JudgeCommand::Run { config, state_dir } => {
            run_once(
                config,
                state_dir,
                false,
                &mut transcript::Pending::default(),
            )
            .await
            .code
        }
        JudgeCommand::Watch { config, state_dir } => watcher::run(config, state_dir).await,
        JudgeCommand::Repair {
            config,
            state_dir,
            experience,
            revision,
            retry,
            review,
        } => {
            match repair::run(
                config.as_deref(),
                state_dir.as_deref(),
                experience,
                revision,
                retry,
                review.as_deref(),
            )
            .await
            {
                Ok(code) => code,
                Err(error) => {
                    eprintln!("Review repair: {error:#}");
                    INCOMPLETE
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
            config,
            state_dir,
            list,
            id,
            json,
        } => {
            let path = match state::resolve(state_dir.as_deref()) {
                Ok(path) => path,
                Err(_) => {
                    if json {
                        println!(
                            "{}",
                            json!({"status":"invalid_config","reason":"invalid_state_path"})
                        );
                    } else {
                        eprintln!(
                            "The judge state directory is invalid. Check the --state-dir path."
                        );
                    }
                    return INVALID_CONFIG;
                }
            };
            let database = match config::load(config.as_deref()) {
                Ok(settings) => {
                    let key = id.or_else(|| {
                        state::read(&path)
                            .ok()
                            .flatten()
                            .and_then(|report| report.diagnostics_id)
                    });
                    transcript::lookup(&settings.core.database, key, list).await
                }
                Err(error) => Err(error),
            };
            if let Ok(Some(value)) = &database {
                print_diagnostics(value, json);
                return 0;
            }
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
                    if attempts.is_empty() && database.is_err() {
                        return Ok(json!({"status":"no_diagnostics"}));
                    }
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
                Ok(value) if value["status"] == "no_diagnostics" && database.is_err() => {
                    eprintln!("Cannot read PostgreSQL transcripts. Check the database connection and the selected configuration.");
                    if json {
                        println!(
                            "{}",
                            json!({"status":"unavailable","reason":"database_unavailable"})
                        );
                    }
                    UNAVAILABLE
                }
                Ok(value) => {
                    print_diagnostics(&value, json);
                    0
                }
                Err(_) => {
                    if json {
                        println!(
                            "{}",
                            json!({"status":"unavailable","reason":"state_unavailable"})
                        );
                    } else {
                        eprintln!("Cannot read the judge state directory. Check that the directory is accessible.");
                    }
                    UNAVAILABLE
                }
            }
        }
    }
}

fn print_diagnostics(value: &serde_json::Value, raw: bool) {
    if raw {
        println!("{value}");
        return;
    }
    if let Some(attempts) = value["attempts"].as_array() {
        if attempts.is_empty() {
            println!("No failed-review transcripts are available.");
        }
        for attempt in attempts {
            let id = attempt["id"].as_str().unwrap_or("unknown");
            let experience = attempt["experience_id"].as_str().unwrap_or("unknown");
            let revision = attempt["source_revision"]
                .as_i64()
                .map_or_else(|| "unknown".into(), |revision| revision.to_string());
            println!("Transcript {id} for experience {experience}, source revision {revision}.");
        }
        return;
    }
    let trace = &value["trace"];
    if trace.is_null() {
        println!("No matching failed-review transcript is available.");
        return;
    }
    let events = trace["transcript"]["events"]
        .as_array()
        .or_else(|| trace["events"].as_array());
    println!("Saved failed review attempt.");
    if let Some(events) = events {
        if let Some(event) = events.iter().rev().find(|event| {
            matches!(
                event["kind"].as_str(),
                Some("tool_rejection" | "tool_parse_rejection" | "tool_error" | "model_error")
            )
        }) {
            if let Some(reason) = event["detail"]["reason"]
                .as_str()
                .or_else(|| event["detail"].as_str())
            {
                println!("Why it failed: {reason}");
            }
        }
    }
    if let (Some(id), Some(revision)) = (
        trace["experience_id"].as_str(),
        trace["source_revision"].as_i64(),
    ) {
        println!("To open the guided repair, run the repair command from the alert for experience {id}, source revision {revision}.");
    }
    println!("Add --json to see the raw transcript.");
}

struct RunOutcome {
    code: i32,
    degraded: bool,
    idle: bool,
    /// A provider-declared usage limit arms an automatic resume: the repair
    /// wait wakes after this delay instead of waiting for a human SIGHUP.
    auto_resume: Option<Duration>,
}

/// Delay until the next occurrence of the local time a provider message
/// declares as its limit reset ("resets 6:50am"). `now_minutes` is the
/// current local time in minutes since midnight. A message without a usable
/// reset leaves the watcher waiting for a configuration edit or SIGHUP.
fn provider_resume_delay(detail: &str, now_minutes: u32) -> Option<u32> {
    let (_, reset) = detail.split_once("resets")?;
    let (hour, rest) = reset.trim_start().split_once(':')?;
    let hour = hour.parse::<u32>().ok()?;
    let minute = rest.get(..2)?.parse::<u32>().ok()?;
    let suffix = rest.get(2..)?.trim_start().get(..2)?;
    if !(1..=12).contains(&hour) || minute >= 60 {
        return None;
    }
    let is_pm = suffix.eq_ignore_ascii_case("pm");
    if !is_pm && !suffix.eq_ignore_ascii_case("am") {
        return None;
    }
    let target = ((hour % 12) + if is_pm { 12 } else { 0 }) * 60 + minute;
    let delta = (target + 1440 - now_minutes) % 1440;
    Some(if delta == 0 { 1440 } else { delta })
}

fn record_startup_failure(
    config: Option<&std::path::Path>,
    state_dir: Option<&std::path::Path>,
    reason: &str,
    error: &anyhow::Error,
    phase: Option<&str>,
) {
    let Ok(path) = state::resolve(state_dir) else {
        return;
    };
    let Ok(Some(state)) = state::State::lock(path) else {
        return;
    };
    let mut report = state::Report::new("blocked", 0, 0, 0, 0, 0);
    report.block_reason = Some(reason.into());
    report.failure_detail = Some(format!("{error:#}"));
    report.preserve_deferrals(state.path());
    report.stamp();
    if reason != "database_unavailable" {
        if let Err(error) = notification::startup_failure(config, &state, &mut report) {
            report.notification = "unavailable".into();
            eprintln!("Cannot enqueue the startup failure email: {error:#}");
        }
    }
    let _ = state.record_incident(&report);
    let _ = state.write(&report);
    if let Some(phase) = phase {
        let _ = state.write_runtime(&json!({"version":env!("CARGO_PKG_VERSION"),"pid":std::process::id(),"phase":phase,"needs_attention":true}));
    }
}

async fn run_once(
    config: Option<PathBuf>,
    state_dir: Option<PathBuf>,
    watch_mode: bool,
    transcripts: &mut transcript::Pending,
) -> RunOutcome {
    let settings = match config::load(config.as_deref()) {
        Ok(settings) => settings,
        Err(error) => {
            record_startup_failure(
                config.as_deref(),
                state_dir.as_deref(),
                "invalid_config",
                &error,
                None,
            );
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
                auto_resume: None,
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
                auto_resume: None,
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
                auto_resume: None,
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
                auto_resume: None,
            };
        }
    };
    let _=state.write_runtime(&json!({"version":env!("CARGO_PKG_VERSION"),"pid":std::process::id(),"phase":"reviewing","config_format":settings.operations.config_version}));
    let report = match settings.llm.backend {
        config::Backend::Api => match api::ApiBackend::new(&settings.llm) {
            Ok(Some(mut backend)) => {
                runner::run_queued(&settings, &state, &mut backend, None, transcripts).await
            }
            Ok(None) => {
                runner::run_queued(
                    &settings,
                    &state,
                    &mut runner::UnavailableBackend,
                    None,
                    transcripts,
                )
                .await
            }
            Err(error) => {
                runner::setup_failure(&settings, &state, "backend_configuration", &error).await
            }
        },
        _ => match harness::Harness::new(&settings.llm) {
            Ok(mut backend) => {
                runner::run_queued(&settings, &state, &mut backend, None, transcripts).await
            }
            Err(error) => {
                runner::setup_failure(&settings, &state, "backend_configuration", &error).await
            }
        },
    };
    if report.status != "idle" {
        let logging = &settings.operations.logging;
        if let Err(error) = logging.prepare().and_then(|()| {
            logging.event(
                "judge",
                &format!(
                    "batch {}; confirmed={}; pending={}; unavailable={}; reason={}",
                    report.status,
                    report.confirmed,
                    report.pending,
                    report.unavailable,
                    report.block_reason.as_deref().unwrap_or("none")
                ),
            )
        }) {
            eprintln!("Cannot save the batch outcome to the operational log: {error:#}");
        }
    }
    let _=state.write_runtime(&json!({"version":env!("CARGO_PKG_VERSION"),"pid":std::process::id(),"phase":"batch_finished","outcome":report.status,"config_format":settings.operations.config_version}));
    let code = match report.status.as_str() {
        "idle" | "complete" => 0,
        "partial" | "blocked" => INCOMPLETE,
        _ => UNAVAILABLE,
    };
    if !watch_mode {
        if report.transcripts_pending != 0 {
            eprintln!("The failed-review transcript could not be saved to PostgreSQL before this command exited.");
        }
        if report.notification == "retry_pending" {
            eprintln!("Email is queued. If no watcher is running, start `mimir judge watch` with the same configuration and state directory to deliver it.");
        }
        println!(
            "{}",
            serde_json::to_string(&report)
                .unwrap_or_else(|_| "{\"status\":\"unavailable\"}".into())
        );
    }
    // Keep the diagnostic reason intact. Once readback has deferred a
    // selected review, its refusal need not stop unrelated reviews.
    let reason = report.block_reason.as_deref();
    let deferred_only = reason == Some("review_deferred");
    let local_refusal = matches!(reason, Some("tool_rejected" | "review_requires_repair"))
        && report
            .deferred_reviews
            .iter()
            .any(|held| report.selected_ids.contains(&held.id));
    let auto_resume = if report.block_reason.as_deref() == Some("provider_usage_limit") {
        let now = chrono::Local::now();
        let minutes = provider_resume_delay(
            report.failure_detail.as_deref().unwrap_or(""),
            now.hour() * 60 + now.minute(),
        );
        minutes.map(|delay| Duration::from_secs(u64::from(delay) * 60))
    } else {
        None
    };
    RunOutcome {
        code: if watch_mode
            && (deferred_only || local_refusal || reason == Some("review_source_changed"))
        {
            0
        } else {
            code
        },
        degraded: matches!(report.status.as_str(), "blocked" | "partial"),
        idle: report.status == "idle"
            || (watch_mode && deferred_only && report.selected_ids.is_empty()),
        auto_resume,
    }
}

#[cfg(test)]
mod watch_tests {
    use super::*;
    use std::os::unix::fs::OpenOptionsExt;

    #[test]
    fn provider_reset_delay_targets_the_declared_local_time() {
        let message = "You've hit your 5-hour limit · resets 6:50am (America/Los_Angeles)";
        assert_eq!(provider_resume_delay(message, 120), Some(290));
        assert_eq!(provider_resume_delay(message, 420), Some(1430));
        assert_eq!(provider_resume_delay(message, 410), Some(1440));
    }

    #[test]
    fn provider_reset_delay_handles_pm_and_unparseable_messages() {
        assert_eq!(provider_resume_delay("resets 11:30pm", 0), Some(1410));
        for message in [
            "some unrelated failure",
            "resets 6:",
            "resets 6:é",
            "resets 6:99am",
            "resets 13:20pm",
            "resets 6:50",
        ] {
            assert_eq!(provider_resume_delay(message, 0), None);
        }
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
        let outcome = run_once(
            Some(config),
            Some(state_dir.clone()),
            true,
            &mut transcript::Pending::default(),
        )
        .await;
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
