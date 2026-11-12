//! JudgeHostProtocol: subscribe before querying, continue immediately after
//! successful work, and retry failed attempts on an explicit repair event.
use super::{
    config, config_events::ConfigEvents, record_invalid_configuration, run_once, RunOutcome,
    UNAVAILABLE,
};
use mimir_core::db::WorkSubscription;
use std::path::PathBuf;
use tokio::signal::unix::{signal, SignalKind};

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
    loop {
        if subscription.is_none() {
            let subscribed = async {
                let settings = config::load(config.as_deref())?;
                WorkSubscription::subscribe(&settings.core.database).await
            }
            .await;
            match subscribed {
                Ok(listener) => subscription = Some(listener),
                Err(error) => {
                    record_invalid_configuration(state_dir.as_deref(), &error);
                    eprintln!("Cannot start review work: {error:#}. Correct the prerequisite and edit the configuration or run `kill -HUP {}` to retry.", std::process::id());
                    tokio::select! { _ = retry.recv() => {}, changed = configuration_change(&mut files) => { if let Err(error) = changed { eprintln!("Configuration events: {error:#}"); } } }
                    if let Ok(path) = config::resolved_path(config.as_deref()) {
                        files = ConfigEvents::new(&path).ok();
                    }
                    _mail = super::notification::start_worker(config.clone(), state_dir.clone());
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
                            eprintln!("{error:#} Run `kill -HUP {}` after correcting the database problem.", std::process::id());
                            subscription = None;
                            tokio::select! { _ = retry.recv() => {}, _ = configuration_change(&mut files) => {} }
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
                subscription = None;
                eprintln!("Review attempt stopped; unfinished reviews remain pending. Run `mimir judge diagnose`, correct the prerequisite, then edit configuration or run `kill -HUP {}` for a fresh attempt.", std::process::id());
                tokio::select! { _ = retry.recv() => {}, changed = configuration_change(&mut files) => { if let Err(error) = changed { eprintln!("Configuration events: {error:#}"); files = None; } } }
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
                degraded: false
            }),
            NextBatch::Immediately
        );
        assert_eq!(
            next_batch(&RunOutcome {
                code: 0,
                idle: true,
                degraded: false
            }),
            NextBatch::WorkEvent
        );
        assert_eq!(
            next_batch(&RunOutcome {
                code: 3,
                idle: false,
                degraded: true
            }),
            NextBatch::Repair
        );
        // A deferred selection does not prevent selecting other pending work.
        assert_eq!(
            next_batch(&RunOutcome {
                code: 0,
                idle: false,
                degraded: true
            }),
            NextBatch::Immediately
        );
    }
}
