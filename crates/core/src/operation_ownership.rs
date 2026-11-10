//! The execution body drops before its stop receipt. Publication revocation
//! is shared through PostgreSQL; this registry does not infer remote cleanup.
use crate::{
    embed::{EmbeddingCancelled, EmbeddingStopHandle, WorkerCleanupIssue},
    store::OperationOutcome,
    MimirService,
};
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
    embedding_cleanup: HashMap<Uuid, Vec<EmbeddingStopHandle>>,
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
        // OwnedExecution declares its body first, so provider futures and
        // native guards have dropped. Physical cleanup errors remain tracked
        // separately and cannot become a confirmed stop receipt.
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
                if let Some(jobs) = state.embedding_cleanup.get_mut(&self.token) {
                    jobs.retain(EmbeddingStopHandle::cleanup_pending);
                    if jobs.is_empty() {
                        state.embedding_cleanup.remove(&self.token);
                    }
                }
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
    fn track_embedding(&self, token: Uuid, handle: EmbeddingStopHandle) -> Result<()> {
        self.state
            .lock()
            .map_err(|_| anyhow::anyhow!("operation execution registry is unavailable"))?
            .embedding_cleanup
            .entry(token)
            .or_default()
            .push(handle);
        Ok(())
    }

    fn confirm_embedding_cleanup(&self, token: Uuid) -> Result<Vec<WorkerCleanupIssue>> {
        let handles = self
            .state
            .lock()
            .map_err(|_| anyhow::anyhow!("operation execution registry is unavailable"))?
            .embedding_cleanup
            .get(&token)
            .cloned()
            .unwrap_or_default();
        // No registry lock is held while retrying the actual owned children.
        let issues = handles
            .iter()
            .flat_map(EmbeddingStopHandle::confirm_cleanup)
            .collect();
        let mut state = self
            .state
            .lock()
            .map_err(|_| anyhow::anyhow!("operation execution registry is unavailable"))?;
        if let Some(jobs) = state.embedding_cleanup.get_mut(&token) {
            jobs.retain(EmbeddingStopHandle::cleanup_pending);
            if jobs.is_empty() {
                state.embedding_cleanup.remove(&token);
            }
        }
        Ok(issues)
    }

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
    cleanup_issues: Vec<WorkerCleanupIssue>,
}
impl OperationCancellation {
    pub fn local_cleanup_confirmed(&self) -> bool {
        self.local_cleanup_confirmed
    }
    pub fn into_outcome(self) -> OperationOutcome {
        self.outcome
    }
    pub fn cleanup_issues(&self) -> &[WorkerCleanupIssue] {
        &self.cleanup_issues
    }
}
impl MimirService {
    pub(crate) fn operation_embedding_job<'a>(
        &self,
        backend: &'a crate::embed::OwnedEmbeddingBackend,
        texts: &'a [String],
        token: Option<Uuid>,
    ) -> Result<crate::embed::EmbeddingJob<'a>> {
        let job = backend.embed(texts);
        if let Some(token) = token {
            self.operation_executions
                .track_embedding(token, job.stop_handle())?;
        }
        Ok(job)
    }

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
        let cleanup = self.operation_executions.confirm_embedding_cleanup(token);
        self.operation_executions.decision(
            token,
            recorded.is_ok()
                && stopped.is_ok()
                && cleanup.as_ref().is_ok_and(|issues| issues.is_empty()),
        );
        stopped?;
        let cleanup_issues = cleanup?;
        recorded.context(if cleanup_issues.is_empty() {
            "This process's work stopped, but database cancellation is unconfirmed. Keep the token and read its outcome before retrying cancellation; do not restart its business work."
        } else {
            "The request future was dropped, but local worker cleanup and database cancellation remain unconfirmed. Keep the token and retry cancellation; inspect the private worker diagnostics and ask the user before starting replacement work."
        })?;
        let outcome = self.read_operation_outcome(token, None).await?;
        let local_cleanup_confirmed =
            cleanup_issues.is_empty() && matches!(&outcome, OperationOutcome::Cancelled { .. });
        Ok(OperationCancellation {
            outcome,
            local_cleanup_confirmed,
            cleanup_issues,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::store::CancellationReceipt;

    fn cancelled(token: Uuid) -> OperationOutcome {
        OperationOutcome::Cancelled {
            cancellation: CancellationReceipt {
                operation_token: token,
                cancelled_at: chrono::Utc::now(),
            },
            binding: None,
            saved_replies: Vec::new(),
        }
    }

    #[test]
    fn cancellation_reports_unconfirmed_physical_cleanup_without_erasing_saved_state() {
        let token = Uuid::new_v4();
        let report = crate::operation_reporting::cancellation(
            token,
            OperationCancellation {
                outcome: cancelled(token),
                local_cleanup_confirmed: false,
                cleanup_issues: vec![WorkerCleanupIssue {
                    pid: 123,
                    diagnostics: "/private/worker/diagnostics".into(),
                    error: "the operating system did not provide a child exit receipt".into(),
                }],
            },
        )
        .unwrap();
        assert_eq!(report["status"], "cancelled");
        assert_eq!(report["worker_cleanup"], "unconfirmed_for_this_server");
        assert_eq!(report["next_action"], "open_user_dialog");
        assert_eq!(report["cleanup_issues"][0]["pid"], 123);
        assert_eq!(
            report["cleanup_issues"][0]["diagnostics"],
            "/private/worker/diagnostics"
        );
        assert!(report["cleanup_issues"][0]["error"]
            .as_str()
            .unwrap()
            .contains("exit receipt"));
        assert!(report.get("cancellation").is_some());
        assert!(report.get("saved_replies").is_some());
        assert!(report.get("business_changes").is_none());
    }

    #[test]
    fn cancellation_confirmed_here_does_not_claim_remote_cleanup() {
        let token = Uuid::new_v4();
        let report = crate::operation_reporting::cancellation(
            token,
            OperationCancellation {
                outcome: cancelled(token),
                local_cleanup_confirmed: true,
                cleanup_issues: Vec::new(),
            },
        )
        .unwrap();
        assert_eq!(report["worker_cleanup"], "confirmed_for_this_server");
        assert!(report["message"]
            .as_str()
            .unwrap()
            .contains("other processes is not confirmed"));
        assert!(report.get("cleanup_issues").is_none());
    }

    #[tokio::test]
    async fn stop_waits_until_the_actual_body_has_been_dropped() {
        use std::sync::atomic::{AtomicBool, Ordering};
        struct Body(Arc<AtomicBool>);
        impl Drop for Body {
            fn drop(&mut self) {
                self.0.store(true, Ordering::SeqCst);
            }
        }
        let registry = Arc::new(OperationExecutions::default());
        let token = Uuid::new_v4();
        let dropped = Arc::new(AtomicBool::new(false));
        let body = Body(dropped.clone());
        let owned = registry
            .own(token, async move {
                let _body = body;
                std::future::pending::<()>().await;
            })
            .unwrap();
        let stopping = registry.stop(token).unwrap();
        assert!(!dropped.load(Ordering::SeqCst));
        drop(owned);
        stopping.wait().await.unwrap();
        assert!(dropped.load(Ordering::SeqCst));
    }
}
