//! The execution body drops before its stop receipt. Publication revocation
//! is shared through PostgreSQL; this registry does not infer remote cleanup.
use crate::{
    embed::{EmbeddingCancelled, EmbeddingStopHandle, WorkerCleanupIssue},
    store::{executions, ExecutionReceipt, OperationOutcome},
    MimirService,
};
use anyhow::{Context, Result};
use futures_util::future::{AbortHandle, AbortRegistration, Abortable, Aborted};
use std::{
    collections::HashMap,
    future::Future,
    pin::Pin,
    sync::{Arc, Mutex, Weak},
    task::{Context as TaskContext, Poll},
};
use tokio::sync::watch;
use uuid::Uuid;

// This capability exists only while the exact registered request is polled.
// It cannot be supplied by a caller or inferred from another active token.
tokio::task_local! {
    static CURRENT_REQUEST: Arc<RequestScope>;
}

#[derive(Default)]
struct Children {
    body_destroyed: bool,
    stopped: Vec<watch::Receiver<bool>>,
}

struct RequestScope {
    execution: ExecutionReceipt,
    registry: Weak<OperationExecutions>,
    children: Mutex<Children>,
}

impl RequestScope {
    fn admits(&self, registry: &Arc<OperationExecutions>, token: Uuid) -> bool {
        self.execution.operation_token == token && self.registry.ptr_eq(&Arc::downgrade(registry))
    }

    fn own_child(&self, child: &Active) -> Result<()> {
        let mut children = self
            .children
            .lock()
            .map_err(|_| anyhow::anyhow!("request child ownership is unavailable"))?;
        if children.body_destroyed {
            return Err(EmbeddingCancelled.into());
        }
        children.stopped.push(child.stopped.subscribe());
        Ok(())
    }

    fn body_destroyed(&self) {
        self.children
            .lock()
            .unwrap_or_else(|error| error.into_inner())
            .body_destroyed = true;
    }

    async fn join_children(&self) -> Result<()> {
        let waiting = {
            let children = self
                .children
                .lock()
                .map_err(|_| anyhow::anyhow!("request child ownership is unavailable"))?;
            anyhow::ensure!(
                children.body_destroyed,
                "The request body has not stopped; its execution cannot be acknowledged"
            );
            children.stopped.clone()
        };
        Stopping { waiting }.wait().await
    }
}

struct Active {
    abort: AbortHandle,
    stopped: watch::Sender<bool>,
    execution: Option<ExecutionReceipt>,
}
#[derive(Clone)]
struct PendingAcknowledgement {
    execution: ExecutionReceipt,
    registration_uncertain: bool,
    scope: Option<Arc<RequestScope>>,
}
#[derive(Default)]
struct State {
    active: HashMap<Uuid, Vec<Arc<Active>>>,
    stopping: HashMap<Uuid, watch::Sender<bool>>,
    embedding_cleanup: HashMap<Uuid, Vec<EmbeddingStopHandle>>,
    awaiting_ack: HashMap<Uuid, PendingAcknowledgement>,
}
#[derive(Default)]
pub(crate) struct OperationExecutions {
    state: Mutex<State>,
}

struct Owner {
    registry: Arc<OperationExecutions>,
    token: Uuid,
    active: Arc<Active>,
    scope: Option<Arc<RequestScope>>,
}
impl Drop for Owner {
    fn drop(&mut self) {
        // OwnedExecution declares its body first, so provider futures and
        // native guards have dropped. Physical cleanup errors remain tracked
        // separately and cannot become a confirmed stop receipt.
        if let Some(scope) = &self.scope {
            scope.body_destroyed();
        }
        let mut state = self
            .registry
            .state
            .lock()
            .unwrap_or_else(|error| error.into_inner());
        if let Some(execution) = &self.active.execution {
            state.awaiting_ack.insert(
                execution.execution_id,
                PendingAcknowledgement {
                    execution: execution.clone(),
                    registration_uncertain: false,
                    scope: self.scope.clone(),
                },
            );
        }
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
        // A waiter may flush immediately when this event wakes it. Publish
        // only after the stopped execution is queued and the registry unlocks.
        drop(state);
        self.active.stopped.send_replace(true);
    }
}

struct RegistrationOwner {
    registry: Arc<OperationExecutions>,
    execution: Option<ExecutionReceipt>,
}
impl Drop for RegistrationOwner {
    fn drop(&mut self) {
        if let Some(execution) = self.execution.take() {
            self.registry.remember_stopped(execution, true);
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
        let still_active = state
            .active
            .get(&token)
            .is_some_and(|entries| !entries.is_empty());
        if let Some(jobs) = state.embedding_cleanup.get_mut(&token) {
            jobs.retain(|job| still_active || job.cleanup_pending());
            if jobs.is_empty() {
                state.embedding_cleanup.remove(&token);
            }
        }
        Ok(issues)
    }

    #[cfg(test)]
    fn own<F: Future>(self: &Arc<Self>, token: Uuid, work: F) -> Result<OwnedExecution<F>> {
        self.own_registered(token, work, None)
    }

    fn own_registered<F: Future>(
        self: &Arc<Self>,
        token: Uuid,
        work: F,
        execution: Option<ExecutionReceipt>,
    ) -> Result<OwnedExecution<F>> {
        let (abort, registration): (AbortHandle, AbortRegistration) = AbortHandle::new_pair();
        let (stopped, _) = watch::channel(false);
        let active = Arc::new(Active {
            abort,
            stopped,
            execution,
        });
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
                scope: None,
            },
        })
    }

    fn remember_stopped(&self, execution: ExecutionReceipt, registration_uncertain: bool) {
        self.state
            .lock()
            .unwrap_or_else(|error| error.into_inner())
            .awaiting_ack
            .insert(
                execution.execution_id,
                PendingAcknowledgement {
                    execution,
                    registration_uncertain,
                    scope: None,
                },
            );
    }

    fn acknowledgements(&self) -> Result<Vec<PendingAcknowledgement>> {
        Ok(self
            .state
            .lock()
            .map_err(|_| anyhow::anyhow!("operation execution registry is unavailable"))?
            .awaiting_ack
            .values()
            .cloned()
            .collect())
    }

    fn acknowledged(&self, identity: Uuid) {
        self.state
            .lock()
            .unwrap_or_else(|error| error.into_inner())
            .awaiting_ack
            .remove(&identity);
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
    all_cleanup_confirmed: bool,
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
    pub fn all_cleanup_confirmed(&self) -> bool {
        self.all_cleanup_confirmed
    }
}
impl MimirService {
    pub(crate) fn operation_embedding_job<'a>(
        &'a self,
        backend: &'a crate::embed::OwnedEmbeddingBackend,
        texts: &'a [String],
        token: Option<Uuid>,
    ) -> crate::embed::EmbedFuture<'a> {
        Box::pin(async move {
            let work = async {
                let job = backend.embed(texts);
                if let Some(token) = token {
                    self.operation_executions
                        .track_embedding(token, job.stop_handle())?;
                }
                job.await
            };
            match token {
                Some(token) => {
                    let parent = CURRENT_REQUEST
                        .try_with(|scope| {
                            scope
                                .admits(&self.operation_executions, token)
                                .then(|| scope.clone())
                        })
                        .ok()
                        .flatten();
                    if let Some(parent) = parent {
                        self.own_child(parent, token, work).await
                    } else {
                        self.own_execution(token, work, true).await
                    }
                }
                None => work.await,
            }
        })
    }

    async fn own_child<F: Future<Output = Result<T>> + Send, T: Send>(
        &self,
        parent: Arc<RequestScope>,
        token: Uuid,
        work: F,
    ) -> Result<T> {
        let mut client = crate::db::connect(&self.database).await?;
        if !executions::permits_child(&mut client, token).await? {
            return Err(EmbeddingCancelled.into());
        }
        drop(client);
        let owned = self
            .operation_executions
            .own_registered(token, work, None)?;
        parent.own_child(&owned._owner.active)?;
        let result = owned
            .await
            .map_err(|_| anyhow::Error::from(EmbeddingCancelled))
            .and_then(std::convert::identity);
        let cleanup = self.operation_executions.confirm_embedding_cleanup(token);
        match result {
            Ok(value) => {
                ensure_physical_cleanup(&cleanup?)?;
                Ok(value)
            }
            Err(error) => {
                let issues = cleanup.context(format!("Original cause: {error:#}"))?;
                ensure_physical_cleanup(&issues).context(format!("Original cause: {error:#}"))?;
                Err(error)
            }
        }
    }

    pub(crate) async fn own_operation<F: Future<Output = Result<T>> + Send, T: Send>(
        &self,
        token: Uuid,
        work: F,
    ) -> Result<T> {
        self.own_execution(token, work, false).await
    }

    async fn own_execution<F: Future<Output = Result<T>> + Send, T: Send>(
        &self,
        token: Uuid,
        work: F,
        provider: bool,
    ) -> Result<T> {
        // LISTEN is acknowledged before registration can commit. A later
        // cancellation therefore either prevents registration or is queued.
        let mut revoked =
            crate::db::OperationExecutionSubscription::cancelled(&self.database, token).await?;
        let mut client = crate::db::connect(&self.database).await?;
        let (execution, mut starting) =
            match executions::register(&mut client, token, |execution| RegistrationOwner {
                registry: self.operation_executions.clone(),
                execution: Some(execution.clone()),
            })
            .await
            {
                Ok(Some(execution)) => execution,
                Ok(None) if provider => return Err(EmbeddingCancelled.into()),
                // A terminal action may only perform the existing exact readback.
                // Provider work never uses this branch.
                Ok(None) => return work.await,
                Err(error) => {
                    return Err(error);
                }
            };
        // Registration is durable; this connection has no remaining work.
        // The separately owned cancellation subscription stays active.
        drop(client);
        let scope = Arc::new(RequestScope {
            execution: execution.clone(),
            registry: Arc::downgrade(&self.operation_executions),
            children: Default::default(),
        });
        let work = CURRENT_REQUEST.scope(scope.clone(), work);
        let result = match self.operation_executions.own_registered(
            token,
            work,
            Some(execution.clone()),
        ) {
            Ok(mut owned) => {
                owned._owner.scope = Some(scope);
                starting.execution = None;
                let mut owned = Box::pin(owned);
                let result = tokio::select! {
                    biased;
                    observed = revoked.changed() => {
                        match observed {
                            Ok(()) => Err(EmbeddingCancelled.into()),
                            Err(error) => Err(error.context("Cancellation monitoring disconnected. This execution stopped; physical confirmation remains pending until its owner can acknowledge it.")),
                        }
                    }
                    result = owned.as_mut() => result.map_err(|_| anyhow::Error::from(EmbeddingCancelled)),
                };
                // Drop the provider and publish its stop receipt before waiting
                // for the cancellation writer; otherwise they deadlock.
                drop(owned);
                result
            }
            Err(error) => {
                // Registration committed, but the local cancellation gate won
                // before this body was ever polled.
                drop(starting);
                let _ = self.acknowledge_stopped(Some(token)).await;
                self.operation_executions.wait_decision(token).await?;
                return Err(error);
            }
        };
        let cleanup = self.acknowledge_stopped(Some(token)).await;
        match result {
            Ok(result) => {
                let issues = cleanup?;
                ensure_physical_cleanup(&issues)?;
                result
            }
            Err(error) => {
                let issues = cleanup.context(format!("Execution stopped, but global acknowledgement remains pending. Original cause: {error:#}"))?;
                ensure_physical_cleanup(&issues).context(format!("Original cause: {error:#}"))?;
                self.operation_executions.wait_decision(token).await?;
                Err(error)
            }
        }
    }

    /// Host-owned async finalization. Drop only queues stopped executions;
    /// this method publishes acknowledgements after their physical cleanup.
    pub async fn confirm_stopped_executions(&self) -> Result<Vec<WorkerCleanupIssue>> {
        self.acknowledge_stopped(None).await
    }

    async fn acknowledge_stopped(&self, token: Option<Uuid>) -> Result<Vec<WorkerCleanupIssue>> {
        let pending: Vec<_> = self
            .operation_executions
            .acknowledgements()?
            .into_iter()
            .filter(|pending| token.is_none_or(|token| pending.execution.operation_token == token))
            .collect();
        if pending.is_empty() {
            return Ok(Vec::new());
        }
        let mut issues = Vec::new();
        let mut client = crate::db::connect(&self.database).await?;
        for pending in pending {
            if let Some(scope) = &pending.scope {
                scope.join_children().await?;
            }
            let execution = pending.execution;
            let local = self
                .operation_executions
                .confirm_embedding_cleanup(execution.operation_token)?;
            if !local.is_empty() {
                issues.extend(local);
                continue;
            }
            match executions::acknowledge(&mut client, &execution).await? {
                Some(receipt) if receipt.stopped_at.is_some() => self.operation_executions.acknowledged(execution.execution_id),
                None if pending.registration_uncertain => { // No body ever began under this uncertain registration.
                    self.operation_executions.acknowledged(execution.execution_id);
                }
                Some(_) => anyhow::bail!("Execution {} has no physical-stop acknowledgement; keep it pending and open the user dialog", execution.execution_id),
                None => anyhow::bail!("Registered execution {} disappeared without its stop acknowledgement; keep the original token and open the user dialog", execution.execution_id),
            }
        }
        Ok(issues)
    }

    pub async fn finish_operation_host(&self) -> Result<()> {
        ensure_physical_cleanup(&self.confirm_stopped_executions().await?)
    }
    /// Stop owned calls before waiting for database revocation. A blocked
    /// database query must not keep a cancelled native provider running.
    pub async fn cancel_operation(&self, token: Uuid) -> Result<OperationCancellation> {
        let stopping = self.operation_executions.stop(token)?;
        let mut acknowledgements =
            crate::db::OperationExecutionSubscription::stopped(&self.database, token).await?;
        let recorded = async {
            let store = crate::store::AgeStore::new(
                crate::db::connect(&self.database).await?,
                self.database.dbname.clone(),
            )?;
            store.record_operation_cancellation(token).await?;
            Ok::<_, anyhow::Error>(store)
        }
        .await;
        let stopped = stopping.wait().await;
        let cleanup = self.acknowledge_stopped(Some(token)).await;
        self.operation_executions.decision(
            token,
            recorded.is_ok()
                && stopped.is_ok()
                && cleanup.as_ref().is_ok_and(|issues| issues.is_empty()),
        );
        stopped?;
        let cleanup_issues = cleanup?;
        let store = recorded.context(if cleanup_issues.is_empty() {
            "This process's work stopped, but database cancellation is unconfirmed. Keep the token and read its outcome before retrying cancellation; do not restart its business work."
        } else {
            "The request future was dropped, but local worker cleanup and database cancellation remain unconfirmed. Keep the token and retry cancellation; inspect the private worker diagnostics and ask the user before starting replacement work."
        })?;
        let mut outcome = store.read_operation_outcome(token, None).await?;
        // After revocation commits, registration is fenced under the same
        // reservation lock. Only actual owner acknowledgements shrink this set.
        while cleanup_issues.is_empty() {
            let pending = match &outcome {
                OperationOutcome::Cancelled {
                    pending_executions, ..
                } => pending_executions.clone(),
                OperationOutcome::Completed { .. } => store.pending_execution_stops(token).await?,
                _ => break,
            };
            if pending.is_empty() {
                break;
            }
            acknowledgements.changed().await.context("Global worker cleanup remains pending. A disconnected copy has not confirmed physical stop; read operation_outcome and restore that owner's connection, without inventing a deadline or replacement action")?;
            outcome = store.read_operation_outcome(token, None).await?;
        }
        let local_cleanup_confirmed = cleanup_issues.is_empty()
            && matches!(
                &outcome,
                OperationOutcome::Cancelled { .. } | OperationOutcome::Completed { .. }
            );
        let all_cleanup_confirmed = local_cleanup_confirmed;
        Ok(OperationCancellation {
            outcome,
            local_cleanup_confirmed,
            cleanup_issues,
            all_cleanup_confirmed,
        })
    }
}

fn ensure_physical_cleanup(issues: &[WorkerCleanupIssue]) -> Result<()> {
    if issues.is_empty() {
        return Ok(());
    }
    let mut message = String::from("Physical cleanup remains unconfirmed; no execution acknowledgement was published. Open the user dialog before replacement work.");
    for issue in issues {
        message.push_str(&format!(
            "\nWorker {}: {}; private diagnostics: {}",
            issue.pid,
            issue.error,
            issue.diagnostics.display()
        ));
    }
    anyhow::bail!(message)
}

#[cfg(test)]
#[path = "operation_global_tests.rs"]
mod global_tests;

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
            pending_executions: Vec::new(),
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
                all_cleanup_confirmed: false,
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
                all_cleanup_confirmed: false,
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

    #[test]
    fn stop_receipt_wakes_only_after_its_acknowledgement_is_queued() {
        use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
        use std::task::{Wake, Waker};
        struct ObserveQueue {
            registry: Arc<OperationExecutions>,
            identity: Uuid,
            correct: AtomicBool,
            observations: AtomicUsize,
        }
        impl Wake for ObserveQueue {
            fn wake(self: Arc<Self>) {
                let queued = self
                    .registry
                    .acknowledgements()
                    .unwrap()
                    .iter()
                    .any(|row| row.execution.execution_id == self.identity);
                self.correct.fetch_and(queued, Ordering::SeqCst);
                self.observations.fetch_add(1, Ordering::SeqCst);
            }
        }
        // Local registry observation only: this mock receipt is never stored.
        let token = Uuid::new_v4();
        let execution = ExecutionReceipt {
            execution_id: Uuid::new_v4(),
            operation_token: token,
            registered_at: chrono::Utc::now(),
            stopped_at: None,
            owner_program: "test-registry".into(),
            owner_pid: i64::from(std::process::id()),
            owner_host: None,
            owner_host_source: None,
            client_address: None,
        };
        let registry = Arc::new(OperationExecutions::default());
        let owned = registry
            .own_registered(token, std::future::pending::<()>(), Some(execution.clone()))
            .unwrap();
        let mut receiver = owned._owner.active.stopped.subscribe();
        let observer = Arc::new(ObserveQueue {
            registry,
            identity: execution.execution_id,
            correct: AtomicBool::new(true),
            observations: AtomicUsize::new(0),
        });
        let waker = Waker::from(observer.clone());
        let mut changed = Box::pin(receiver.changed());
        assert!(changed
            .as_mut()
            .poll(&mut TaskContext::from_waker(&waker))
            .is_pending());
        drop(owned);
        assert!(observer.observations.load(Ordering::SeqCst) > 0);
        assert!(
            observer.correct.load(Ordering::SeqCst),
            "stop receipt became observable before its owner could acknowledge"
        );
    }
}
