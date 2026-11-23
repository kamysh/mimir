//! JudgeHostProtocol: subscribe before querying, continue immediately after
//! successful work, and reconnect automatically after a database outage.
use super::{
    config, config_events::ConfigEvents, record_startup_failure, run_once, RunOutcome, UNAVAILABLE,
};
use mimir_core::db::WorkSubscription;
use std::{
    io::ErrorKind,
    path::{Path, PathBuf},
    time::Duration,
};
use tokio::signal::unix::{signal, Signal, SignalKind};

const DATABASE_RETRY_INTERVAL: Duration = Duration::from_secs(5);

fn temporary_database_failure(error: &anyhow::Error) -> bool {
    error.chain().any(|cause| {
        cause
            .downcast_ref::<tokio_postgres::Error>()
            .is_some_and(|error| {
                error.is_closed()
                    || error.code().is_some_and(|code| {
                        matches!(
                            code.code(),
                            "08001" | "08003" | "08006" | "57P01" | "57P02" | "57P03" | "53300"
                        )
                    })
            })
            || cause.downcast_ref::<std::io::Error>().is_some_and(|error| {
                matches!(
                    error.kind(),
                    ErrorKind::ConnectionRefused
                        | ErrorKind::ConnectionReset
                        | ErrorKind::ConnectionAborted
                        | ErrorKind::NotConnected
                        | ErrorKind::BrokenPipe
                        | ErrorKind::NetworkDown
                        | ErrorKind::NetworkUnreachable
                        | ErrorKind::HostUnreachable
                        | ErrorKind::TimedOut
                        | ErrorKind::UnexpectedEof
                )
            })
    })
}

fn record_outage(state_dir: Option<&Path>, error: &anyhow::Error) {
    record_startup_failure(
        state_dir,
        "database_unavailable",
        error,
        Some("reconnecting_database"),
    );
    eprintln!("PostgreSQL is unavailable; Mimir will retry the connection: {error:#}");
}

#[derive(Debug, PartialEq, Eq)]
enum NextBatch {
    Immediately,
    WorkEvent,
    Repair,
}

fn next_batch(outcome: &RunOutcome) -> NextBatch {
    if outcome.code != 0 {
        NextBatch::Repair
    } else if outcome.idle {
        NextBatch::WorkEvent
    } else {
        NextBatch::Immediately
    }
}

async fn configuration_change(events: &mut Option<ConfigEvents>) -> anyhow::Result<()> {
    match events {
        Some(events) => events.changed().await,
        None => std::future::pending().await,
    }
}

async fn disconnected(subscription: &mut WorkSubscription) -> anyhow::Error {
    loop {
        if let Err(error) = subscription.changed().await {
            return error;
        }
    }
}

async fn provider_reset(delay: Option<Duration>) {
    match delay {
        Some(delay) => tokio::time::sleep(delay).await,
        None => std::future::pending().await,
    }
}

// True when an operator action should also refresh the config and mail worker.
async fn wait_for_retry(
    retry: &mut Signal,
    files: &mut Option<ConfigEvents>,
    reconnect: bool,
) -> bool {
    tokio::select! {
        _ = retry.recv() => true,
        changed = configuration_change(files) => {
            if let Err(error) = changed {
                eprintln!("Configuration events: {error:#}");
                *files = None;
            }
            true
        },
        _ = tokio::time::sleep(DATABASE_RETRY_INTERVAL), if reconnect => false,
    }
}

pub(super) async fn run(config: Option<PathBuf>, state_dir: Option<PathBuf>) -> i32 {
    let mut _mail = super::notification::start_worker(config.clone(), state_dir.clone());
    let mut retry = match signal(SignalKind::hangup()) {
        Ok(signal) => signal,
        Err(error) => {
            eprintln!("Cannot install the SIGHUP retry listener: {error}");
            return UNAVAILABLE;
        }
    };
    let mut files = match config::resolved_path(config.as_deref())
        .and_then(|path| ConfigEvents::new(&path))
    {
        Ok(events) => Some(events),
        Err(error) => {
            eprintln!("Cannot watch configuration edits: {error:#}. Correct the path/access problem and send SIGHUP to retry.");
            None
        }
    };
    let mut subscription: Option<WorkSubscription> = None;
    let mut in_outage = false;
    loop {
        if subscription.is_none() {
            let subscribed = match config::load(config.as_deref()) {
                Ok(settings) => WorkSubscription::subscribe(&settings.core.database)
                    .await
                    .map_err(|error| {
                        let reason = if temporary_database_failure(&error) {
                            "database_unavailable"
                        } else {
                            "database_setup"
                        };
                        (reason, error)
                    }),
                Err(error) => Err(("invalid_config", error)),
            };
            match subscribed {
                Ok(listener) => {
                    subscription = Some(listener);
                    in_outage = false;
                }
                Err((reason, error)) => {
                    let reconnect = reason == "database_unavailable";
                    if reconnect {
                        if !in_outage {
                            record_outage(state_dir.as_deref(), &error);
                        }
                        in_outage = true;
                    } else {
                        record_startup_failure(
                            state_dir.as_deref(),
                            reason,
                            &error,
                            Some("awaiting_repair"),
                        );
                        eprintln!("Cannot start review work: {error:#}. Correct the prerequisite and edit the configuration or run `kill -HUP {}` to retry.", std::process::id());
                    }
                    if wait_for_retry(&mut retry, &mut files, reconnect).await {
                        in_outage = false;
                        if let Ok(path) = config::resolved_path(config.as_deref()) {
                            files = ConfigEvents::new(&path).ok();
                        }
                        _mail =
                            super::notification::start_worker(config.clone(), state_dir.clone());
                    }
                    continue;
                }
            }
        }
        // Every new subscription is followed by a pending-work query, including
        // after reconnecting. Notifications during the query remain queued.
        let outcome = run_once(config.clone(), state_dir.clone(), true).await;
        if let Ok(path) = super::state::resolve(state_dir.as_deref()) {
            if let Ok(Some(state)) = super::state::State::lock(path) {
                let phase = match next_batch(&outcome) {
                    NextBatch::Immediately => "reviewing",
                    NextBatch::WorkEvent => "waiting_for_work",
                    NextBatch::Repair => "awaiting_repair",
                };
                let _ = state.write_runtime(&serde_json::json!({"version":env!("CARGO_PKG_VERSION"),"pid":std::process::id(),"phase":phase,"needs_attention":outcome.degraded}));
            }
        }
        match next_batch(&outcome) {
            NextBatch::Immediately => continue,
            NextBatch::WorkEvent => {
                tokio::select! {
                    changed = subscription.as_mut().expect("subscribed before querying").changed() => {
                        if let Err(error) = changed {
                            subscription = None;
                            record_outage(state_dir.as_deref(), &error);
                            in_outage = true;
                            if wait_for_retry(&mut retry, &mut files, true).await {
                                in_outage = false;
                                _mail = super::notification::start_worker(config.clone(), state_dir.clone());
                            }
                        }
                    },
                    _ = retry.recv() => { subscription = None; _mail = super::notification::start_worker(config.clone(), state_dir.clone()); },
                    changed = configuration_change(&mut files) => {
                        if let Err(error) = changed { eprintln!("Configuration events: {error:#}"); files = None; }
                        subscription = None;
                        _mail = super::notification::start_worker(config.clone(), state_dir.clone());
                    }
                }
            }
            NextBatch::Repair => {
                match outcome.auto_resume {
                    Some(delay) => {
                        eprintln!("Review attempt stopped by a provider usage limit; resuming automatically in {delay:?}.");
                    }
                    None => {
                        eprintln!("Review attempt stopped; unfinished reviews remain pending. Run `mimir judge diagnose`, correct the prerequisite, then edit configuration or run `kill -HUP {}` for a fresh attempt.", std::process::id());
                    }
                }
                let database_error = tokio::select! {
                    error = disconnected(subscription.as_mut().expect("subscribed before querying")) => Some(error),
                    _ = retry.recv() => None,
                    changed = configuration_change(&mut files) => {
                        if let Err(error) = changed {
                            eprintln!("Configuration events: {error:#}");
                            files = None;
                        }
                        None
                    },
                    _ = provider_reset(outcome.auto_resume) => None,
                };
                subscription = None;
                if let Some(error) = database_error {
                    record_outage(state_dir.as_deref(), &error);
                    in_outage = true;
                    if !wait_for_retry(&mut retry, &mut files, true).await {
                        continue;
                    }
                    in_outage = false;
                }
                _mail = super::notification::start_worker(config.clone(), state_dir.clone());
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn successful_batches_continue_and_failed_attempts_wait_for_repair() {
        assert_eq!(
            next_batch(&RunOutcome {
                code: 0,
                idle: false,
                degraded: false,
                auto_resume: None
            }),
            NextBatch::Immediately
        );
        assert_eq!(
            next_batch(&RunOutcome {
                code: 0,
                idle: true,
                degraded: false,
                auto_resume: None
            }),
            NextBatch::WorkEvent
        );
        assert_eq!(
            next_batch(&RunOutcome {
                code: 3,
                idle: false,
                degraded: true,
                auto_resume: None
            }),
            NextBatch::Repair
        );
        // A deferred selection does not prevent selecting other pending work.
        assert_eq!(
            next_batch(&RunOutcome {
                code: 0,
                idle: false,
                degraded: true,
                auto_resume: None
            }),
            NextBatch::Immediately
        );
    }
}
