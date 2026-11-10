//! The execution body drops before its stop receipt. Publication revocation
//! is shared through PostgreSQL; this registry does not infer remote cleanup.
use crate::{embed::EmbeddingCancelled, store::OperationOutcome, MimirService};
use anyhow::{Context, Result};
use futures_util::future::{AbortHandle, AbortRegistration, Abortable, Aborted};
use std::{
    collections::HashMap,
    future::Future,
    pin::Pin,
    sync::{Arc, Mutex},
    task::{Context as TaskContext, Poll},
};
use tokio::sync::watch;
use uuid::Uuid;

struct Active {
    abort: AbortHandle,
    stopped: watch::Sender<bool>,
}
#[derive(Default)]
struct State {
    active: HashMap<Uuid, Vec<Arc<Active>>>,
    stopping: HashMap<Uuid, watch::Sender<bool>>,
}
#[derive(Default)]
pub(crate) struct OperationExecutions {
    state: Mutex<State>,
}

struct Owner {
    registry: Arc<OperationExecutions>,
    token: Uuid,
    active: Arc<Active>,
}
impl Drop for Owner {
    fn drop(&mut self) {
        // OwnedExecution declares its body first: all provider futures and
        // native child guards have already been dropped and reaped.
        self.active.stopped.send_replace(true);
        let mut state = self
            .registry
            .state
            .lock()
            .unwrap_or_else(|error| error.into_inner());
        if let Some(entries) = state.active.get_mut(&self.token) {
            entries.retain(|entry| !Arc::ptr_eq(entry, &self.active));
            if entries.is_empty() {
                state.active.remove(&self.token);
            }
        }
    }
}
pub(crate) struct OwnedExecution<F: Future> {
    work: Pin<Box<Abortable<F>>>,
    _owner: Owner,
}
impl<F: Future> Future for OwnedExecution<F> {
    type Output = std::result::Result<F::Output, Aborted>;
    fn poll(self: Pin<&mut Self>, context: &mut TaskContext<'_>) -> Poll<Self::Output> {
        self.get_mut().work.as_mut().poll(context)
    }
}
struct Stopping {
    waiting: Vec<watch::Receiver<bool>>,
}
impl Stopping {
    async fn wait(mut self) -> Result<()> {
        for receiver in &mut self.waiting {
            while !*receiver.borrow() {
                receiver
                    .changed()
                    .await
                    .context("owned execution ended without its stop receipt")?;
            }
        }
        Ok(())
    }
}
impl OperationExecutions {
    fn own<F: Future>(self: &Arc<Self>, token: Uuid, work: F) -> Result<OwnedExecution<F>> {
        let (abort, registration): (AbortHandle, AbortRegistration) = AbortHandle::new_pair();
        let (stopped, _) = watch::channel(false);
        let active = Arc::new(Active { abort, stopped });
        {
            let mut state = self
                .state
                .lock()
                .map_err(|_| anyhow::anyhow!("operation execution registry is unavailable"))?;
            if state.stopping.contains_key(&token) {
                return Err(EmbeddingCancelled.into());
            }
            state.active.entry(token).or_default().push(active.clone());
        }
        Ok(OwnedExecution {
            work: Box::pin(Abortable::new(work, registration)),
            _owner: Owner {
                registry: self.clone(),
                token,
                active,
            },
        })
    }
    fn stop(&self, token: Uuid) -> Result<Stopping> {
        let active = {
            let mut state = self
                .state
                .lock()
                .map_err(|_| anyhow::anyhow!("operation execution registry is unavailable"))?;
            state
                .stopping
                .entry(token)
                .or_insert_with(|| watch::channel(false).0)
                .send_replace(false);
            state.active.get(&token).cloned().unwrap_or_default()
        };
        let mut waiting = Vec::new();
        for entry in active {
            waiting.push(entry.stopped.subscribe());
            entry.abort.abort();
        }
        Ok(Stopping { waiting })
    }
    fn decision(&self, token: Uuid, recorded: bool) {
        let mut state = self.state.lock().unwrap_or_else(|error| error.into_inner());
        if let Some(ready) = state.stopping.get(&token) {
            ready.send_replace(true);
        }
        // An unknown database result keeps the local prohibition on new work.
        // An explicit cancellation retry can resolve it without a timer.
        if recorded {
            state.stopping.remove(&token);
        }
    }
    async fn wait_decision(&self, token: Uuid) -> Result<()> {
        let receiver = {
            let state = self
                .state
                .lock()
                .map_err(|_| anyhow::anyhow!("operation execution registry is unavailable"))?;
            state.stopping.get(&token).map(watch::Sender::subscribe)
        };
        if let Some(mut receiver) = receiver {
            while !*receiver.borrow() {
                receiver.changed().await.context(
                    "cancellation decision became unavailable; read the original operation outcome",
                )?;
            }
        }
        Ok(())
    }
}

pub struct OperationCancellation {
    outcome: OperationOutcome,
    local_cleanup_confirmed: bool,
}
impl OperationCancellation {
    pub fn local_cleanup_confirmed(&self) -> bool {
        self.local_cleanup_confirmed
    }
    pub fn into_outcome(self) -> OperationOutcome {
        self.outcome
    }
}
impl MimirService {
    pub(crate) async fn own_operation<F: Future<Output = Result<T>>, T>(
        &self,
        token: Uuid,
        work: F,
    ) -> Result<T> {
        let result = match self.operation_executions.own(token, work) {
            Ok(owned) => {
                let mut owned = Box::pin(owned);
                let result = owned.as_mut().await;
                // Drop the provider and publish its stop receipt before waiting
                // for the cancellation writer; otherwise they deadlock.
                drop(owned);
                result
            }
            Err(error) => {
                self.operation_executions.wait_decision(token).await?;
                return Err(error);
            }
        };
        match result {
            Ok(result) => result,
            Err(_) => {
                self.operation_executions.wait_decision(token).await?;
                Err(EmbeddingCancelled.into())
            }
        }
    }
    /// Stop owned calls before waiting for database revocation. A blocked
    /// database query must not keep a cancelled native provider running.
    pub async fn cancel_operation(&self, token: Uuid) -> Result<OperationCancellation> {
        let stopping = self.operation_executions.stop(token)?;
        let recorded = self.record_operation_cancellation(token).await;
        let stopped = stopping.wait().await;
        self.operation_executions
            .decision(token, recorded.is_ok() && stopped.is_ok());
        stopped?;
        recorded.context("This server's work stopped, but database cancellation is unconfirmed. Keep the token and read its outcome before retrying cancellation; do not restart its business work.")?;
        let outcome = self.read_operation_outcome(token, None).await?;
        let local_cleanup_confirmed = matches!(&outcome, OperationOutcome::Cancelled { .. });
        Ok(OperationCancellation {
            outcome,
            local_cleanup_confirmed,
        })
    }
}
