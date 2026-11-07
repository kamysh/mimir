//! A named business change and its original answer share one transaction.
use super::{reservations::decode_binding, AgeStore, OperationBinding, OperationBindingRequest};
use anyhow::{ensure, Result};
use serde::Serialize;
use serde_json::Value;
use std::{future::Future, pin::Pin};
use tokio_postgres::{Row, Transaction};
use uuid::Uuid;

pub type StepWork<'a> = Pin<Box<dyn Future<Output = Result<Value>> + Send + 'a>>;

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct StepReceipt {
    pub operation_token: Uuid,
    pub step: String,
    pub reply: Value,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StepDecision {
    Done(StepReceipt),
    UnknownBinding,
    ChangedRequest(OperationBinding),
}

fn step_name(name: &str) -> Result<()> {
    ensure!(
        !name.is_empty() && name == name.trim() && !name.chars().any(char::is_control),
        "step must be its exact registered name"
    );
    Ok(())
}

fn receipt(row: &Row) -> Result<StepReceipt> {
    Ok(StepReceipt {
        operation_token: row.try_get("operation_token")?,
        step: row.try_get("step")?,
        reply: serde_json::from_str(row.try_get::<_, &str>("reply")?)?,
    })
}

impl AgeStore {
    /// The callback receives the stored request and a borrowed transaction;
    /// this helper owns publication. A retry never invokes the callback again.
    /// Named-plan/order admission is added by #123 before public dispatch.
    pub async fn commit_operation_step<F>(
        &self,
        token: Uuid,
        expected: &OperationBindingRequest,
        step: &str,
        apply: F,
    ) -> Result<StepDecision>
    where
        F: for<'a, 'client> FnOnce(
            &'a Transaction<'client>,
            &'a OperationBindingRequest,
        ) -> StepWork<'a>,
    {
        step_name(step)?;
        let arguments = serde_json::to_string(expected.arguments())?;
        let settings = serde_json::to_string(expected.settings())?;
        let mut client = self.client.lock().await;
        let tx = super::learning_transaction(&mut client).await?;
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
        if let Some(saved) = tx.query_opt(
            "SELECT operation_token,step,reply::text AS reply FROM mimir_operation_step_replies WHERE operation_token=$1 AND step=$2",
            &[&token, &step],
        ).await? {
            let saved = receipt(&saved)?;
            tx.commit().await?;
            return Ok(StepDecision::Done(saved));
        }
        let reply = apply(&tx, &binding.request).await?;
        let reply = serde_json::to_string(&reply)?;
        let saved = receipt(&tx.query_one(
            "INSERT INTO mimir_operation_step_replies (operation_token,step,reply) VALUES ($1,$2,$3::text::jsonb) RETURNING operation_token,step,reply::text AS reply",
            &[&token, &step, &reply],
        ).await?)?;
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
