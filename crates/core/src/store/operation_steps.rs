//! A named business change and its original answer share one transaction.
use super::{
    reservations::decode_binding, AgeStore, OperationBinding, OperationBindingRequest, PlannedStep,
    RegisteredStep,
};
use anyhow::{ensure, Result};
use serde::Serialize;
use serde_json::Value;
use std::{future::Future, pin::Pin};
use tokio_postgres::{Row, Transaction};
use uuid::Uuid;

pub type StepWork<'a> = Pin<Box<dyn Future<Output = Result<Value>> + Send + 'a>>;
pub type FinalStepWork<'a> = Pin<Box<dyn Future<Output = Result<(Value, Value)>> + Send + 'a>>;
pub(super) type PublicationWork<'a> =
    Pin<Box<dyn Future<Output = Result<(Value, Option<Value>)>> + Send + 'a>>;

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct StepReceipt {
    pub operation_token: Uuid,
    pub step: String,
    pub reply: mimir_json::Document,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StepDecision {
    Done(StepReceipt),
    UnknownBinding,
    ChangedRequest(OperationBinding),
    OutOfOrder(PlannedStep),
    WrongCompletion {
        step: PlannedStep,
        requires_final_result: bool,
    },
    NeedsRecovery(String),
    Cancelled(super::CancellationReceipt),
}

fn step_name(name: &str) -> Result<()> {
    ensure!(
        !name.is_empty() && name == name.trim() && !name.chars().any(char::is_control),
        "step must be its exact registered name"
    );
    Ok(())
}

pub(super) fn receipt(row: &Row) -> Result<StepReceipt> {
    Ok(StepReceipt {
        operation_token: row.try_get("operation_token")?,
        step: row.try_get("step")?,
        reply: mimir_json::from_str(row.try_get::<_, &str>("reply")?)?,
    })
}

impl AgeStore {
    /// The callback receives the stored request and a borrowed transaction;
    /// this helper owns publication. A retry never invokes the callback again.
    /// A checked plan handle and the next-step guard are required before work.
    pub async fn commit_operation_step<F>(
        &self,
        registered: &RegisteredStep,
        apply: F,
    ) -> Result<StepDecision>
    where
        F: for<'a, 'client> FnOnce(
            &'a Transaction<'client>,
            &'a OperationBindingRequest,
        ) -> StepWork<'a>,
    {
        self.publish_operation_step(registered, false, move |tx, request| {
            let work = apply(tx, request);
            Box::pin(async move { Ok((work.await?, None)) })
        })
        .await
    }

    /// The final change, step answer and operation answer commit together.
    pub async fn commit_final_operation_step<F>(
        &self,
        registered: &RegisteredStep,
        apply: F,
    ) -> Result<StepDecision>
    where
        F: for<'a, 'client> FnOnce(
            &'a Transaction<'client>,
            &'a OperationBindingRequest,
        ) -> FinalStepWork<'a>,
    {
        self.publish_operation_step(registered, true, move |tx, request| {
            let work = apply(tx, request);
            Box::pin(async move {
                let (step, result) = work.await?;
                Ok((step, Some(result)))
            })
        })
        .await
    }

    pub(super) async fn publish_operation_step<F>(
        &self,
        registered: &RegisteredStep,
        final_step: bool,
        apply: F,
    ) -> Result<StepDecision>
    where
        F: for<'a, 'client> FnOnce(
            &'a Transaction<'client>,
            &'a OperationBindingRequest,
        ) -> PublicationWork<'a>,
    {
        let token = registered.token();
        let expected = registered.expected();
        let step = registered.id();
        step_name(step)?;
        let arguments = mimir_json::to_string(expected.arguments())?;
        let settings = mimir_json::to_string(expected.settings())?;
        let mut client = self.client.lock().await;
        let tx = super::learning_transaction(&mut client).await?;
        if !super::cancellations::lock_token(&tx, token).await? {
            tx.rollback().await?;
            return Ok(StepDecision::UnknownBinding);
        }
        // Check the original request BEFORE consulting a saved answer.
        let row = tx.query_opt(
            "SELECT operation_token,bound_at,operation,arguments::text AS arguments,settings::text AS settings,operation=$2 AND arguments=$3::text::jsonb AND settings=$4::text::jsonb AS matches FROM mimir_operation_bindings WHERE operation_token=$1 FOR UPDATE",
            &[&token, &expected.operation(), &arguments, &settings],
        ).await?;
        let Some(row) = row else {
            tx.rollback().await?;
            return Ok(StepDecision::UnknownBinding);
        };
        let binding = decode_binding(&row)?;
        if !row.try_get::<_, bool>("matches")? {
            tx.rollback().await?;
            return Ok(StepDecision::ChangedRequest(binding));
        }
        if let Some(cancelled) = super::cancellations::lookup(&tx, token).await? {
            tx.rollback().await?;
            return Ok(StepDecision::Cancelled(cancelled));
        }
        // Inspect this impossible pair before progress() rejects an old
        // completed-but-incomplete journal. It must open recovery, not invoke
        // the business callback or fabricate the missing immutable answer.
        if final_step
            && tx
                .query_opt(
                    "SELECT 1 FROM mimir_operation_step_replies WHERE operation_token=$1 AND step=$2",
                    &[&token, &super::operation_plans::RESULT_KEY],
                )
                .await?
                .is_some()
            && tx
                .query_opt(
                    "SELECT 1 FROM mimir_operation_step_replies WHERE operation_token=$1 AND step=$2",
                    &[&token, &step],
                )
                .await?
                .is_none()
        {
            tx.rollback().await?;
            return Ok(StepDecision::NeedsRecovery("The operation has a saved result but its last step answer is absent. Read the saved answers and resolve this older operation; do not repeat its data change or invent a step answer.".into()));
        }
        if let Some(next) = registered.admission(&tx).await? {
            tx.rollback().await?;
            return Ok(StepDecision::OutOfOrder(next));
        }
        if final_step != registered.is_final() {
            tx.rollback().await?;
            return Ok(StepDecision::WrongCompletion {
                step: registered.description().clone(),
                requires_final_result: registered.is_final(),
            });
        }
        if let Some(saved) = tx.query_opt(
            "SELECT operation_token,step,reply::text AS reply FROM mimir_operation_step_replies WHERE operation_token=$1 AND step=$2",
            &[&token, &step],
        ).await? {
            let saved = receipt(&saved)?;
            if final_step && tx.query_opt("SELECT 1 FROM mimir_operation_step_replies WHERE operation_token=$1 AND step=$2", &[&token, &super::operation_plans::RESULT_KEY]).await?.is_none() {
                tx.rollback().await?;
                return Ok(StepDecision::NeedsRecovery("The last step has a saved answer but the operation result is absent. Read the saved answers and resolve this older operation; do not repeat its data change or invent a result.".into()));
            }
            tx.commit().await?;
            return Ok(StepDecision::Done(saved));
        }
        let (reply, operation_result) = match apply(&tx, &binding.request).await {
            Ok(publication) => publication,
            Err(original) => {
                if let Err(rollback) = tx.rollback().await {
                    // Do not retain a numerical-decision error in the source
                    // chain: a caller must not turn an unconfirmed rollback
                    // into a response certifying that nothing changed.
                    return Err(anyhow::anyhow!(
                        "Operation {token} failed before commit, but rollback could not be confirmed: {rollback:#}. Keep this token and read its saved steps and operation outcome before deciding how to continue. Original cause: {original:#}"
                    ));
                }
                return Err(original);
            }
        };
        let reply = mimir_json::Document::new(reply);
        let operation_result = operation_result.map(mimir_json::Document::new);
        let reply = mimir_json::to_string(&reply)?;
        let saved = receipt(&tx.query_one(
            "INSERT INTO mimir_operation_step_replies (operation_token,step,reply) VALUES ($1,$2,$3::text::jsonb) RETURNING operation_token,step,reply::text AS reply",
            &[&token, &step, &reply],
        ).await?)?;
        if let Some(result) = operation_result {
            let result = mimir_json::to_string(&result)?;
            tx.execute("INSERT INTO mimir_operation_step_replies (operation_token,step,reply) VALUES ($1,$2,$3::text::jsonb)", &[&token, &super::operation_plans::RESULT_KEY, &result]).await?;
        }
        // A failed acknowledgement requires readback, not an invented success
        // or a second application of the business change.
        tx.commit().await?;
        Ok(StepDecision::Done(saved))
    }

    pub async fn read_operation_step(
        &self,
        token: Uuid,
        step: &str,
    ) -> Result<Option<StepReceipt>> {
        step_name(step)?;
        let client = self.client.lock().await;
        client.query_opt(
            "SELECT operation_token,step,reply::text AS reply FROM mimir_operation_step_replies WHERE operation_token=$1 AND step=$2",
            &[&token, &step],
        ).await?.as_ref().map(receipt).transpose()
    }
}
