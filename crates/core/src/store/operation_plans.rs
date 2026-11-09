//! Frozen selections and checked, token-scoped execution capabilities.
use super::{reservations::decode_binding, AgeStore, OperationBinding, OperationBindingRequest};
use crate::operation_catalogue::{CommitSite, RegisteredOperation as Operation};
use anyhow::{anyhow, ensure, Result};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::{
    collections::{BTreeMap, BTreeSet},
    future::Future,
    pin::Pin,
    sync::Arc,
};
use tokio_postgres::{GenericClient, Transaction};
use uuid::Uuid;

pub(super) const RESULT_KEY: &str = "@operation-result";
const PLAN_BINDING_MISMATCH: &str = "The saved plan belongs to a different operation than this token's original request. Read its binding, plan and saved answers and ask the user to resolve the mismatch. Do not repeat changes or invent a completion answer.";
pub type Selections = Vec<(CommitSite, Vec<String>)>;
pub type SelectionWork<'a> = Pin<Box<dyn Future<Output = Result<Selections>> + Send + 'a>>;
pub(super) struct CapturedSelection {
    pub selections: Selections,
    pub capture: Option<Value>,
}
pub(super) type CaptureWork<'a> =
    Pin<Box<dyn Future<Output = Result<CapturedSelection>> + Send + 'a>>;

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct Shape {
    site: String,
    may_repeat: bool,
}
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct PlannedStep {
    pub site: String,
    pub key: Option<String>,
    id: String,
}
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct StoredPlan {
    operation: String,
    shape: Vec<Shape>,
    steps: Vec<PlannedStep>,
    #[serde(
        default,
        deserialize_with = "present_capture",
        skip_serializing_if = "Option::is_none"
    )]
    capture: Option<mimir_json::Document>,
}

// Omission retains the old three-field plan. An explicitly supplied null is
// still present and must be rejected rather than treated as omission.
fn present_capture<'de, D: serde::Deserializer<'de>>(
    deserializer: D,
) -> std::result::Result<Option<mimir_json::Document>, D::Error> {
    mimir_json::Document::deserialize(deserializer).map(Some)
}

fn shape(operation: Operation) -> Vec<Shape> {
    operation
        .committed_boundaries()
        .iter()
        .map(|b| Shape {
            site: b.site.name().into(),
            may_repeat: b.may_repeat,
        })
        .collect()
}
fn build(
    operation: Operation,
    selections: Selections,
    capture: Option<Value>,
) -> Result<StoredPlan> {
    let capture = capture.map(mimir_json::Document::new);
    if operation == Operation::Reembed {
        let captured = capture.as_ref().ok_or_else(|| anyhow!(
            "Backfill requires its original server-captured selection; use prepare_reembed_operation rather than guessing row keys"))?;
        let pending = super::backfill::pending_keys(captured)?;
        ensure!(selections == vec![(CommitSite::BeliefVectorPublication, pending)],
            "The backfill steps do not match its original captured pending selection; read the plan and ask the user to resolve it");
    } else {
        ensure!(capture.is_none(), "Captured backfill metadata cannot be attached to another operation; read its original binding and plan");
    }
    let mut selected = BTreeMap::new();
    for (site, keys) in selections {
        ensure!(
            selected.insert(site.name(), keys).is_none(),
            "selection was supplied twice for {}",
            site.name()
        );
    }
    let mut steps = Vec::new();
    for boundary in operation.committed_boundaries() {
        let site = boundary.site.name();
        let keys = if boundary.may_repeat {
            selected.remove(site).ok_or_else(|| anyhow!("provide the captured selection for {site}, including an explicit empty selection when no rows matched"))?.into_iter().map(Some).collect::<Vec<_>>()
        } else {
            vec![None]
        };
        let mut seen = BTreeSet::new();
        for key in keys {
            if let Some(key) = &key {
                ensure!(
                    !key.is_empty() && key == key.trim() && !key.chars().any(char::is_control),
                    "invalid selected key for {site}"
                );
                ensure!(
                    seen.insert(key.clone()),
                    "duplicate selected key for {site}"
                );
            }
            let id = mimir_json::to_string(&(site, &key))?;
            steps.push(PlannedStep {
                site: site.into(),
                key,
                id,
            });
        }
    }
    ensure!(
        selected.is_empty(),
        "selection supplied for a site outside this operation's repeated boundaries"
    );
    Ok(StoredPlan {
        operation: operation.name().into(),
        shape: shape(operation),
        steps,
        capture,
    })
}
fn validate(plan: &StoredPlan) -> Result<()> {
    let operation = Operation::named(&plan.operation).ok_or_else(|| anyhow!("saved operation is no longer registered; read its saved outcome before choosing how to continue"))?;
    ensure!(
        shape(operation) == plan.shape,
        "registered step boundaries changed; read the saved plan and outcome before continuing"
    );
    let mut selections = Vec::new();
    for b in operation
        .committed_boundaries()
        .iter()
        .filter(|b| b.may_repeat)
    {
        let keys = plan
            .steps
            .iter()
            .filter(|s| s.site == b.site.name())
            .map(|s| {
                s.key
                    .clone()
                    .ok_or_else(|| anyhow!("saved repeated step has no selected key"))
            })
            .collect::<Result<Vec<_>>>()?;
        selections.push((b.site, keys));
    }
    ensure!(*plan==build(operation,selections,plan.capture.clone().map(mimir_json::Document::into_value))?, "saved plan disagrees with the registered order; read its outcome and resolve the journal before continuing");
    Ok(())
}

#[cfg(test)]
mod capture_tests {
    use super::*;
    #[test]
    fn deep_json_saved_plan_rejection_keeps_capture_cleanup_safe() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let plan =
                    build(Operation::named("delete_project").unwrap(), vec![], None).unwrap();
                let mut source = mimir_json::Document::new(mimir_json::to_value(plan).unwrap());
                source["capture"] =
                    mimir_json::parse(&format!("{}null{}", "[".repeat(10000), "]".repeat(10000)))
                        .unwrap()
                        .into_value();
                let parsed: StoredPlan = mimir_json::decode_ref(&source).unwrap();
                assert!(validate(&parsed).is_err());
                drop(parsed.clone());
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn legacy_plans_keep_their_shape_and_reject_hidden_capture() -> Result<()> {
        let operation = Operation::named("delete_project").unwrap();
        let plan = build(operation, vec![], None)?;
        let original = mimir_json::to_value(&plan)?;
        assert!(original.get("capture").is_none());
        validate(&mimir_json::from_value(original.clone())?)?;
        for captured in [Value::Null, serde_json::json!({"beliefs":[]})] {
            let mut changed = original.clone();
            changed["capture"] = captured;
            let changed: StoredPlan = mimir_json::from_value(changed)?;
            assert!(validate(&changed).is_err());
        }
        assert!(build(
            Operation::Reembed,
            vec![(CommitSite::BeliefVectorPublication, vec![])],
            None
        )
        .is_err());
        Ok(())
    }
}

#[derive(Clone, Debug)]
struct Inner {
    binding: OperationBinding,
    stored: StoredPlan,
}
#[derive(Clone, Debug)]
pub struct OperationPlan {
    inner: Arc<Inner>,
}
#[derive(Clone, Debug)]
pub struct RegisteredStep {
    inner: Arc<Inner>,
    position: usize,
}
impl OperationPlan {
    pub(crate) fn captured(&self) -> Option<&Value> {
        self.inner.stored.capture.as_ref()
    }
    pub(crate) fn original_request(&self) -> &OperationBindingRequest {
        &self.inner.binding.request
    }
    pub fn operation_token(&self) -> Uuid {
        self.inner.binding.operation_token
    }
    pub fn steps(&self) -> Vec<RegisteredStep> {
        (0..self.inner.stored.steps.len())
            .map(|position| RegisteredStep {
                inner: self.inner.clone(),
                position,
            })
            .collect()
    }
}
impl RegisteredStep {
    pub(super) fn plan(&self) -> OperationPlan {
        OperationPlan {
            inner: self.inner.clone(),
        }
    }
    pub(super) fn is_final(&self) -> bool {
        self.position + 1 == self.inner.stored.steps.len()
    }
    pub fn description(&self) -> &PlannedStep {
        &self.inner.stored.steps[self.position]
    }
    pub(super) fn token(&self) -> Uuid {
        self.inner.binding.operation_token
    }
    pub(super) fn expected(&self) -> &OperationBindingRequest {
        &self.inner.binding.request
    }
    pub fn id(&self) -> &str {
        &self.description().id
    }
    pub(super) async fn admission(&self, tx: &Transaction<'_>) -> Result<Option<PlannedStep>> {
        validate(&self.inner.stored)?;
        let (rows, _, next) = progress(tx, self.token(), &self.inner.stored).await?;
        if rows.contains_key(self.id()) || next == self.position {
            return Ok(None);
        }
        Ok(self.inner.stored.steps.get(next).cloned())
    }
}

#[derive(Clone, Debug)]
pub enum PlanDecision {
    Ready(OperationPlan),
    UnknownBinding,
    ChangedRequest(OperationBinding),
    NeedsRecovery(String),
    Cancelled(super::CancellationReceipt),
}
#[derive(Clone, Debug, Serialize)]
pub struct CompletedOperation {
    operation_token: Uuid,
    reply: mimir_json::Document,
}
impl CompletedOperation {
    pub fn reply(&self) -> &Value {
        &self.reply
    }
    pub fn operation_token(&self) -> Uuid {
        self.operation_token
    }
}
#[derive(Clone, Debug)]
pub enum CompletionDecision {
    Done(CompletedOperation),
    Incomplete(PlannedStep),
    UnknownBinding,
    ChangedRequest(OperationBinding),
    FinalStepRequired(PlannedStep),
    Cancelled(super::CancellationReceipt),
}

#[derive(Clone, Debug, Serialize)]
pub enum OperationOutcome {
    UnknownToken,
    Reserved,
    AwaitingPlan(OperationBinding),
    AwaitingCompletion(OperationBinding),
    ChangedRequest(OperationBinding),
    Pending {
        binding: OperationBinding,
        next_step: PlannedStep,
        saved_replies: Vec<super::StepReceipt>,
    },
    Completed {
        binding: OperationBinding,
        outcome: CompletedOperation,
    },
    NeedsRecovery {
        binding: OperationBinding,
        reason: String,
    },
    Cancelled {
        cancellation: super::CancellationReceipt,
        binding: Option<OperationBinding>,
        saved_replies: Vec<super::StepReceipt>,
    },
}

async fn binding<C: GenericClient + Sync>(
    client: &C,
    token: Uuid,
    expected: &OperationBindingRequest,
    lock: bool,
) -> Result<Option<(OperationBinding, bool)>> {
    let args = mimir_json::to_string(expected.arguments())?;
    let settings = mimir_json::to_string(expected.settings())?;
    let mut sql="SELECT operation_token,bound_at,operation,arguments::text AS arguments,settings::text AS settings,operation=$2 AND arguments=$3::text::jsonb AND settings=$4::text::jsonb AS matches FROM mimir_operation_bindings WHERE operation_token=$1".to_owned();
    if lock {
        sql.push_str(" FOR UPDATE");
    }
    client
        .query_opt(&sql, &[&token, &expected.operation(), &args, &settings])
        .await?
        .map(|row| Ok((decode_binding(&row)?, row.try_get("matches")?)))
        .transpose()
}
async fn load<C: GenericClient + Sync>(client: &C, token: Uuid) -> Result<Option<StoredPlan>> {
    client
        .query_opt(
            "SELECT plan::text FROM mimir_operation_plans WHERE operation_token=$1",
            &[&token],
        )
        .await?
        .map(|row| {
            let plan: StoredPlan = mimir_json::from_str(row.try_get::<_, &str>(0)?)?;
            validate(&plan)?;
            Ok(plan)
        })
        .transpose()
}
async fn progress<C: GenericClient + Sync>(
    client: &C,
    token: Uuid,
    plan: &StoredPlan,
) -> Result<(
    BTreeMap<String, mimir_json::Document>,
    Option<mimir_json::Document>,
    usize,
)> {
    let mut rows = BTreeMap::new();
    let mut result = None;
    for row in client
        .query(
            "SELECT step,reply::text FROM mimir_operation_step_replies WHERE operation_token=$1",
            &[&token],
        )
        .await?
    {
        let key: String = row.try_get(0)?;
        let reply = mimir_json::parse(row.try_get::<_, &str>(1)?)?;
        if key == RESULT_KEY {
            result = Some(reply);
        } else {
            ensure!(
                plan.steps.iter().any(|s| s.id == key),
                "journal contains an undeclared step; read the saved outcome before continuing"
            );
            rows.insert(key, reply);
        }
    }
    let next = plan
        .steps
        .iter()
        .take_while(|s| rows.contains_key(&s.id))
        .count();
    ensure!(
        rows.len() == next,
        "saved steps are not a completed prefix; read the saved outcome before continuing"
    );
    ensure!(
        result.is_none() || next == plan.steps.len(),
        "completion was saved before all planned steps"
    );
    Ok((rows, result, next))
}

impl AgeStore {
    /// One consistent read, without writes, reselection or inferred success.
    /// A database error is an unavailable read, never a completed operation.
    pub async fn read_operation_outcome(
        &self,
        token: Uuid,
        expected: Option<&OperationBindingRequest>,
    ) -> Result<OperationOutcome> {
        let mut client = self.client.lock().await;
        let tx = client
            .build_transaction()
            .read_only(true)
            .isolation_level(tokio_postgres::IsolationLevel::RepeatableRead)
            .start()
            .await?;
        let row = tx.query_opt("SELECT operation_token,bound_at,operation,arguments::text AS arguments,settings::text AS settings FROM mimir_operation_bindings WHERE operation_token=$1", &[&token]).await?;
        let Some(row) = row else {
            let reserved = tx
                .query_opt(
                    "SELECT 1 FROM mimir_operation_reservations WHERE operation_token=$1",
                    &[&token],
                )
                .await?
                .is_some();
            let cancellation = super::cancellations::lookup(&tx, token).await?;
            tx.rollback().await?;
            if let Some(cancellation) = cancellation {
                return Ok(OperationOutcome::Cancelled {
                    cancellation,
                    binding: None,
                    saved_replies: vec![],
                });
            }
            return Ok(if reserved {
                OperationOutcome::Reserved
            } else {
                OperationOutcome::UnknownToken
            });
        };
        let original = decode_binding(&row)?;
        if let Some(expected) = expected {
            let (_, matches) = binding(&tx, token, expected, false).await?.ok_or_else(|| anyhow!("The binding could not be read consistently. Keep this token and read its outcome again."))?;
            if !matches {
                tx.rollback().await?;
                return Ok(OperationOutcome::ChangedRequest(original));
            }
        }
        if let Some(cancellation) = super::cancellations::lookup(&tx, token).await? {
            let saved_replies = super::cancellations::saved_replies(&tx, token).await?;
            tx.rollback().await?;
            return Ok(OperationOutcome::Cancelled {
                cancellation,
                binding: Some(original),
                saved_replies,
            });
        }
        let Some(plan) = load(&tx, token).await? else {
            if tx
                .query_opt(
                    "SELECT 1 FROM mimir_operation_step_replies WHERE operation_token=$1",
                    &[&token],
                )
                .await?
                .is_some()
            {
                tx.rollback().await?;
                return Ok(OperationOutcome::NeedsRecovery { binding: original, reason: "Saved step answers exist without a registered plan. Read those answers and resolve this older operation before continuing.".into() });
            }
            tx.rollback().await?;
            return Ok(OperationOutcome::AwaitingPlan(original));
        };
        if plan.operation.as_str() != original.request.operation() {
            tx.rollback().await?;
            return Ok(OperationOutcome::NeedsRecovery {
                binding: original,
                reason: PLAN_BINDING_MISMATCH.into(),
            });
        }
        let (rows, result, next) = progress(&tx, token, &plan).await?;
        let outcome = if let Some(reply) = result {
            OperationOutcome::Completed {
                binding: original,
                outcome: CompletedOperation {
                    operation_token: token,
                    reply,
                },
            }
        } else if let Some(step) = plan.steps.get(next) {
            let saved_replies = plan
                .steps
                .iter()
                .filter_map(|step| {
                    rows.get(&step.id).map(|reply| super::StepReceipt {
                        operation_token: token,
                        step: step.id.clone(),
                        reply: reply.clone(),
                    })
                })
                .collect();
            OperationOutcome::Pending {
                binding: original,
                next_step: step.clone(),
                saved_replies,
            }
        } else if plan.steps.is_empty() {
            OperationOutcome::AwaitingCompletion(original)
        } else {
            OperationOutcome::NeedsRecovery { binding: original, reason: "Every step has a saved answer but the operation result is absent. Read the saved answers and resolve this older operation; do not repeat its data changes or invent a result.".into() }
        };
        tx.rollback().await?;
        Ok(outcome)
    }

    /// Capture reads cannot write permanent business tables. Retrying an
    /// existing plan never calls the selector, even if the database changed.
    pub async fn prepare_operation<F>(
        &self,
        token: Uuid,
        expected: &OperationBindingRequest,
        select: F,
    ) -> Result<PlanDecision>
    where
        F: for<'a, 'client> FnOnce(
            &'a Transaction<'client>,
            &'a OperationBinding,
        ) -> SelectionWork<'a>,
    {
        self.prepare_operation_captured(token, expected, move |tx, binding| {
            let selected = select(tx, binding);
            Box::pin(async move {
                Ok(CapturedSelection {
                    selections: selected.await?,
                    capture: None,
                })
            })
        })
        .await
    }

    pub(super) async fn prepare_operation_captured<F>(
        &self,
        token: Uuid,
        expected: &OperationBindingRequest,
        select: F,
    ) -> Result<PlanDecision>
    where
        F: for<'a, 'client> FnOnce(
            &'a Transaction<'client>,
            &'a OperationBinding,
        ) -> CaptureWork<'a>,
    {
        let mut client = self.client.lock().await;
        let Some((original, matches)) = binding(&*client, token, expected, false).await? else {
            return Ok(PlanDecision::UnknownBinding);
        };
        if !matches {
            return Ok(PlanDecision::ChangedRequest(original));
        }
        if let Some(cancelled) = super::cancellations::lookup(&*client, token).await? {
            return Ok(PlanDecision::Cancelled(cancelled));
        }
        if let Some(stored) = load(&*client, token).await? {
            if stored.operation.as_str() != original.request.operation() {
                return Ok(PlanDecision::NeedsRecovery(PLAN_BINDING_MISMATCH.into()));
            }
            return Ok(PlanDecision::Ready(OperationPlan {
                inner: Arc::new(Inner {
                    binding: original,
                    stored,
                }),
            }));
        }
        let operation = Operation::named(original.request.operation()).ok_or_else(|| {
            anyhow!(
                "operation is not registered; read its binding and select a registered operation"
            )
        })?;
        let read = client
            .build_transaction()
            .read_only(true)
            .isolation_level(tokio_postgres::IsolationLevel::RepeatableRead)
            .start()
            .await?;
        let captured = select(&read, &original).await;
        read.rollback().await?;
        let tx = super::learning_transaction(&mut client).await?;
        if !super::cancellations::lock_token(&tx, token).await? {
            tx.rollback().await?;
            return Ok(PlanDecision::UnknownBinding);
        }
        let Some((original, matches)) = binding(&tx, token, expected, true).await? else {
            tx.rollback().await?;
            return Ok(PlanDecision::UnknownBinding);
        };
        if !matches {
            tx.rollback().await?;
            return Ok(PlanDecision::ChangedRequest(original));
        }
        if let Some(cancelled) = super::cancellations::lookup(&tx, token).await? {
            tx.rollback().await?;
            return Ok(PlanDecision::Cancelled(cancelled));
        }
        // Another caller may have published the original plan during capture.
        if let Some(stored) = load(&tx, token).await? {
            if stored.operation.as_str() != original.request.operation() {
                tx.rollback().await?;
                return Ok(PlanDecision::NeedsRecovery(PLAN_BINDING_MISMATCH.into()));
            }
            tx.commit().await?;
            return Ok(PlanDecision::Ready(OperationPlan {
                inner: Arc::new(Inner {
                    binding: original,
                    stored,
                }),
            }));
        }
        if tx
            .query_opt(
                "SELECT 1 FROM mimir_operation_step_replies WHERE operation_token=$1",
                &[&token],
            )
            .await?
            .is_some()
        {
            tx.rollback().await?;
            return Ok(PlanDecision::NeedsRecovery("This token already has saved steps but no registered plan. Read those answers and resolve the old operation; do not start it again under a newly guessed plan.".into()));
        }
        let captured = captured?;
        let stored = build(operation, captured.selections, captured.capture)?;
        let encoded = mimir_json::to_string(&stored)?;
        tx.execute(
            "INSERT INTO mimir_operation_plans (operation_token,plan) VALUES ($1,$2::text::jsonb)",
            &[&token, &encoded],
        )
        .await?;
        tx.commit().await?;
        Ok(PlanDecision::Ready(OperationPlan {
            inner: Arc::new(Inner {
                binding: original,
                stored,
            }),
        }))
    }

    pub fn complete_operation<'a>(
        &'a self,
        plan: &'a OperationPlan,
        reply: Value,
    ) -> impl Future<Output = Result<CompletionDecision>> + Send + 'a {
        let reply = mimir_json::Document::new(reply);
        self.complete_operation_checked(plan, move |_| {
            Box::pin(async move { Ok(reply.into_value()) })
        })
    }

    pub(super) async fn complete_operation_checked<F>(
        &self,
        plan: &OperationPlan,
        verify: F,
    ) -> Result<CompletionDecision>
    where
        F: for<'a, 'client> FnOnce(
            &'a Transaction<'client>,
        ) -> super::operation_steps::StepWork<'a>,
    {
        let mut client = self.client.lock().await;
        let tx = super::learning_transaction(&mut client).await?;
        let token = plan.operation_token();
        if !super::cancellations::lock_token(&tx, token).await? {
            tx.rollback().await?;
            return Ok(CompletionDecision::UnknownBinding);
        }
        let Some((original, matches)) =
            binding(&tx, token, &plan.inner.binding.request, true).await?
        else {
            tx.rollback().await?;
            return Ok(CompletionDecision::UnknownBinding);
        };
        if !matches {
            tx.rollback().await?;
            return Ok(CompletionDecision::ChangedRequest(original));
        }
        if let Some(cancelled) = super::cancellations::lookup(&tx, token).await? {
            tx.rollback().await?;
            return Ok(CompletionDecision::Cancelled(cancelled));
        }
        validate(&plan.inner.stored)?;
        let (_, saved, next) = progress(&tx, token, &plan.inner.stored).await?;
        if let Some(step) = plan.inner.stored.steps.get(next) {
            let next = step.clone();
            tx.rollback().await?;
            return Ok(CompletionDecision::Incomplete(next));
        }
        let reply = match saved {
            Some(reply) => reply,
            None => {
                if let Some(last) = plan.inner.stored.steps.last() {
                    let last = last.clone();
                    tx.rollback().await?;
                    return Ok(CompletionDecision::FinalStepRequired(last));
                }
                let reply = match verify(&tx).await {
                    Ok(reply) => mimir_json::Document::new(reply),
                    Err(original) => {
                        if let Err(rollback) = tx.rollback().await {
                            return Err(anyhow!("Completion check failed but rollback could not be confirmed: {rollback:#}. Keep token {token} and read its outcome. Original cause: {original:#}"));
                        }
                        return Err(original);
                    }
                };
                let encoded = mimir_json::to_string(&reply)?;
                let row=tx.query_one("INSERT INTO mimir_operation_step_replies (operation_token,step,reply) VALUES ($1,$2,$3::text::jsonb) RETURNING reply::text",&[&token,&RESULT_KEY,&encoded]).await?;
                mimir_json::from_str(row.try_get::<_, &str>(0)?)?
            }
        };
        tx.commit().await?;
        Ok(CompletionDecision::Done(CompletedOperation {
            operation_token: token,
            reply,
        }))
    }
}
