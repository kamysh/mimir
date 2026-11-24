//! JudgeHostProtocol: subscribe before querying, continue immediately after
//! successful work, and reconnect automatically after a database outage.
use super::{
    config, config_events::ConfigEvents, record_startup_failure, recovery::Next, run_once,
    UNAVAILABLE,
};
use mimir_core::db::WorkSubscription;
use std::{
    io::ErrorKind,
    path::{Path, PathBuf},
    time::Duration,
};
use tokio::signal::unix::{signal, Signal, SignalKind};

const DATABASE_RETRY_INTERVAL: Duration = Duration::from_secs(5);

pub(super) fn temporary_database_failure(error: &anyhow::Error) -> bool {
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
        None,
        state_dir,
        "database_unavailable",
        error,
        Some("reconnecting_database"),
    );
    eprintln!("PostgreSQL is unavailable; Mimir will retry the connection: {error:#}");
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
    let mut _mail = super::notification::start_worker(config.clone(), state_dir.clone(), false);
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
    let mut session = super::recovery::Session::default();
    let mut in_outage = false;
    loop {
        // A backlog can keep us scanning for hours. Consume configuration
        // and operator events between batches as well as during an idle wait.
        let refresh = tokio::select! {
            biased;
            _ = retry.recv() => true,
            changed = configuration_change(&mut files) => {
                if let Err(error) = changed { eprintln!("Configuration events: {error:#}"); files = None; }
                true
            }
            _ = std::future::ready(()) => false,
        };
        if refresh {
            subscription = None;
            _mail = super::notification::start_worker(config.clone(), state_dir.clone(), true);
        }
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
                            config.as_deref(),
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
                        _mail = super::notification::start_worker(
                            config.clone(),
                            state_dir.clone(),
                            true,
                        );
                    }
                    continue;
                }
            }
        }
        // Every new subscription is followed by a pending-work query, including
        // after reconnecting. Notifications during the query remain queued.
        let outcome = run_once(config.clone(), state_dir.clone(), true, &mut session).await;
        if let Ok(path) = super::state::resolve(state_dir.as_deref()) {
            if let Ok(Some(state)) = super::state::State::lock(path) {
                let phase = match &outcome.next {
                    Next::Scan => "reviewing",
                    Next::WorkEvent => "waiting_for_work",
                    Next::Lock(_) => "waiting_for_lock",
                    Next::Provider(_) => "waiting_for_provider",
                    Next::Reconnect => "reconnecting_database",
                    Next::Correct { .. } => "awaiting_repair",
                };
                let _ = state.write_runtime(&serde_json::json!({"version":env!("CARGO_PKG_VERSION"),"pid":std::process::id(),"phase":phase,"needs_attention":outcome.degraded}));
            }
        }
        match outcome.next {
            Next::Scan => continue,
            Next::Lock(path) => {
                if let Err(error) = super::state::State::wait_for_release(path).await {
                    eprintln!("Cannot wait for the state lock. Restore access to the state directory: {error:#}");
                    wait_for_retry(&mut retry, &mut files, false).await;
                }
                subscription = None;
            }
            Next::Reconnect => {
                subscription = None;
                wait_for_retry(&mut retry, &mut files, true).await;
            }
            Next::WorkEvent => {
                tokio::select! {
                    changed = subscription.as_mut().expect("subscribed before querying").changed() => {
                        if let Err(error) = changed {
                            subscription = None;
                            record_outage(state_dir.as_deref(), &error);
                            in_outage = true;
                            if wait_for_retry(&mut retry, &mut files, true).await {
                                in_outage = false;
                                _mail = super::notification::start_worker(config.clone(), state_dir.clone(), true);
                            }
                        }
                    },
                    _ = retry.recv() => { subscription = None; _mail = super::notification::start_worker(config.clone(), state_dir.clone(), true); },
                    changed = configuration_change(&mut files) => {
                        if let Err(error) = changed { eprintln!("Configuration events: {error:#}"); files = None; }
                        subscription = None;
                        _mail = super::notification::start_worker(config.clone(), state_dir.clone(), true);
                    }
                }
            }
            next @ (Next::Correct { .. } | Next::Provider(_)) => {
                let delay = match next {
                    Next::Provider(delay) => {
                        eprintln!(
                            "The provider supplied a reset time. Reviews resume in {delay:?}."
                        );
                        Some(delay)
                    }
                    Next::Correct { action, .. } => {
                        eprintln!("{action}");
                        None
                    }
                    _ => unreachable!(),
                };
                let (database_error, check_mail) = tokio::select! {
                    error = disconnected(subscription.as_mut().expect("subscribed before querying")) => (Some(error), false),
                    _ = retry.recv() => (None, true),
                    changed = configuration_change(&mut files) => {
                        if let Err(error) = changed {
                            eprintln!("Configuration events: {error:#}");
                            files = None;
                        }
                        (None, true)
                    },
                    _ = provider_reset(delay) => (None, false),
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
                if check_mail {
                    _mail =
                        super::notification::start_worker(config.clone(), state_dir.clone(), true);
                }
            }
        }
    }
}
