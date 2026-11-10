//! Durable cancellation is metadata, not proof that every worker has joined.
use super::{AgeStore, StepReceipt};
use anyhow::Result;
use chrono::{DateTime, Utc};
use serde::Serialize;
use tokio_postgres::{GenericClient, Row, Transaction};
use uuid::Uuid;

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct CancellationReceipt {
    pub operation_token: Uuid,
    pub cancelled_at: DateTime<Utc>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CancellationDecision {
    UnknownToken,
    /// This is the original stored fact; outcome readback validates completion.
    SavedResult(StepReceipt),
    /// Publication is revoked. The calling owner must separately await cleanup.
    Recorded(CancellationReceipt),
}

fn decode(row: &Row) -> Result<CancellationReceipt> {
    Ok(CancellationReceipt {
        operation_token: row.try_get("operation_token")?,
        cancelled_at: row.try_get("cancelled_at")?,
    })
}

pub(super) async fn lookup<C: GenericClient + Sync>(
    client: &C,
    token: Uuid,
) -> Result<Option<CancellationReceipt>> {
    client.query_opt(
        "SELECT operation_token,cancelled_at FROM mimir_operation_cancellations WHERE operation_token=$1",
        &[&token],
    ).await?.as_ref().map(decode).transpose()
}

/// Acquire before any binding, learning advisory or owner-row lock.
pub(super) async fn lock_token(tx: &Transaction<'_>, token: Uuid) -> Result<bool> {
    Ok(tx
        .query_opt(
            "SELECT 1 FROM mimir_operation_reservations WHERE operation_token=$1 FOR UPDATE",
            &[&token],
        )
        .await?
        .is_some())
}

pub(super) async fn saved_replies<C: GenericClient + Sync>(
    client: &C,
    token: Uuid,
) -> Result<Vec<StepReceipt>> {
    client.query(
        "SELECT operation_token,step,reply::text AS reply FROM mimir_operation_step_replies WHERE operation_token=$1 ORDER BY step",
        &[&token],
    ).await?.iter().map(super::operation_steps::receipt).collect()
}

impl AgeStore {
    /// Only an explicit caller decision invokes this method. It changes no
    /// business row or saved answer, and creates no replacement operation.
    pub async fn record_operation_cancellation(&self, token: Uuid) -> Result<CancellationDecision> {
        let mut client = self.client.lock().await;
        let tx = super::learning_transaction(&mut client).await?;
        if !lock_token(&tx, token).await? {
            tx.rollback().await?;
            return Ok(CancellationDecision::UnknownToken);
        }
        if let Some(row) = tx.query_opt(
            "SELECT operation_token,step,reply::text AS reply FROM mimir_operation_step_replies WHERE operation_token=$1 AND step=$2",
            &[&token, &super::operation_plans::RESULT_KEY],
        ).await? {
            let saved = super::operation_steps::receipt(&row)?;
            // The business result wins unchanged, but duplicate preparation
            // for this same action must still stop on an explicit user cancel.
            tx.execute("SELECT pg_notify('mimir_operation_cancelled', $1)", &[&token.to_string()]).await?;
            tx.commit().await?;
            return Ok(CancellationDecision::SavedResult(saved));
        }
        let receipt = match lookup(&tx, token).await? {
            Some(original) => original,
            None => decode(&tx.query_one(
                "INSERT INTO mimir_operation_cancellations(operation_token) VALUES($1) RETURNING operation_token,cancelled_at",
                &[&token],
            ).await?)?,
        };
        // Existing DELETE notifications wake owned preparation. Do not take a
        // learning lock while holding this reservation: publication follows
        // reservation -> learning -> owner order and may already be finishing.
        tx.execute(
            "DELETE FROM mimir_embedding_owners WHERE operation_token=$1",
            &[&token],
        )
        .await?;
        // Existing-belief backfills have no preparation-owner row. Notify on
        // cancellation itself as well, so their owned subscriptions can read
        // the token's durable cancellation without waiting for another event.
        tx.execute(
            "SELECT pg_notify('mimir_embedding_owners_changed', '')",
            &[],
        )
        .await?;
        tx.commit().await?;
        Ok(CancellationDecision::Recorded(receipt))
    }

    pub async fn read_operation_cancellation(
        &self,
        token: Uuid,
    ) -> Result<Option<CancellationReceipt>> {
        lookup(&*self.client.lock().await, token).await
    }
}
