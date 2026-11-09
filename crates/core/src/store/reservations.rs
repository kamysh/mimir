//! Durable PostgreSQL-issued handles. Reservation alone changes no business row.
use super::AgeStore;
use anyhow::{ensure, Result};
use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use tokio_postgres::Row;
use uuid::Uuid;

/// Captured request data supplied after admission by the calling interface.
/// This type checks storage shape; it does not replace tool-schema validation.
#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct OperationBindingRequest {
    operation: String,
    arguments: mimir_json::Document,
    settings: mimir_json::Document,
}

impl OperationBindingRequest {
    pub fn new(operation: String, arguments: Value, settings: Value) -> Result<Self> {
        let arguments = mimir_json::Document::new(arguments);
        let settings = mimir_json::Document::new(settings);
        ensure!(
            !operation.is_empty()
                && operation == operation.trim()
                && !operation.chars().any(char::is_control),
            "operation must be the admitted operation's exact name"
        );
        ensure!(
            arguments.is_object(),
            "operation arguments must be an admitted object"
        );
        ensure!(
            settings.is_object(),
            "operation settings must be a captured object"
        );
        Ok(Self {
            operation,
            arguments,
            settings,
        })
    }

    pub fn operation(&self) -> &str {
        &self.operation
    }
    pub fn arguments(&self) -> &Value {
        &self.arguments
    }
    pub fn settings(&self) -> &Value {
        &self.settings
    }
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct OperationBinding {
    pub operation_token: Uuid,
    pub bound_at: DateTime<Utc>,
    pub request: OperationBindingRequest,
}

/// These are metadata decisions, never receipts of successful business work.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OperationBindingDecision {
    Bound(OperationBinding),
    ChangedRequest(OperationBinding),
    UnknownToken,
    Cancelled(super::CancellationReceipt),
}

pub(super) fn decode_binding(row: &Row) -> Result<OperationBinding> {
    let arguments = mimir_json::parse(row.try_get::<_, &str>("arguments")?)?;
    let settings = mimir_json::parse(row.try_get::<_, &str>("settings")?)?;
    Ok(OperationBinding {
        operation_token: row.try_get("operation_token")?,
        bound_at: row.try_get("bound_at")?,
        request: OperationBindingRequest::new(
            row.try_get("operation")?,
            arguments.into_value(),
            settings.into_value(),
        )?,
    })
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct OperationReservation {
    pub operation_token: Uuid,
    pub reserved_at: DateTime<Utc>,
}

fn decode(row: Row) -> Result<OperationReservation> {
    Ok(OperationReservation {
        operation_token: row.try_get("operation_token")?,
        reserved_at: row.try_get("reserved_at")?,
    })
}

#[cfg(test)]
mod json_ownership_tests {
    use super::*;
    #[test]
    fn deep_json_binding_copy_format_and_rejection_keep_owned_values_safe() {
        std::thread::Builder::new()
            .stack_size(256 * 1024)
            .spawn(|| {
                let text = format!(
                    r#"{{"nested":{}null{}}}"#,
                    "[".repeat(10000),
                    "]".repeat(10000)
                );
                let request = OperationBindingRequest::new(
                    "operation".into(),
                    mimir_json::parse(&text).unwrap().into_value(),
                    serde_json::json!({}),
                )
                .unwrap();
                let copy = request.clone();
                assert_eq!(request, copy);
                assert!(format!("{request:?}").contains("nested"));
                assert!(mimir_json::to_string(&request).unwrap().contains("nested"));
                assert!(OperationBindingRequest::new(
                    " ".into(),
                    mimir_json::parse(&text).unwrap().into_value(),
                    serde_json::json!({})
                )
                .is_err());
            })
            .unwrap()
            .join()
            .unwrap();
    }
}

impl AgeStore {
    /// A lost acknowledgement must be read back with the same token. Never
    /// allocate a replacement token or overwrite the earlier request here.
    pub async fn bind_operation_request(
        &self,
        token: Uuid,
        request: &OperationBindingRequest,
    ) -> Result<OperationBindingDecision> {
        let arguments = mimir_json::to_string(&request.arguments)?;
        let settings = mimir_json::to_string(&request.settings)?;
        let mut client = self.client.lock().await;
        let tx = super::learning_transaction(&mut client).await?;
        if !super::cancellations::lock_token(&tx, token).await? {
            tx.rollback().await?;
            return Ok(OperationBindingDecision::UnknownToken);
        }
        if let Some(cancelled) = super::cancellations::lookup(&tx, token).await? {
            tx.rollback().await?;
            return Ok(OperationBindingDecision::Cancelled(cancelled));
        }
        tx.execute(
            "INSERT INTO mimir_operation_bindings (operation_token,operation,arguments,settings) SELECT operation_token,$2,$3::text::jsonb,$4::text::jsonb FROM mimir_operation_reservations WHERE operation_token=$1 ON CONFLICT (operation_token) DO NOTHING",
            &[&token, &request.operation, &arguments, &settings],
        ).await?;
        let row = tx.query_opt(
            "SELECT operation_token,bound_at,operation,arguments::text AS arguments,settings::text AS settings,operation=$2 AND arguments=$3::text::jsonb AND settings=$4::text::jsonb AS matches FROM mimir_operation_bindings WHERE operation_token=$1",
            &[&token, &request.operation, &arguments, &settings],
        ).await?;
        let Some(row) = row else {
            tx.rollback().await?;
            return Ok(OperationBindingDecision::UnknownToken);
        };
        let binding = decode_binding(&row)?;
        let decision = if row.try_get("matches")? {
            OperationBindingDecision::Bound(binding)
        } else {
            OperationBindingDecision::ChangedRequest(binding)
        };
        tx.commit().await?;
        Ok(decision)
    }

    pub async fn read_operation_binding(&self, token: Uuid) -> Result<Option<OperationBinding>> {
        let client = self.client.lock().await;
        client.query_opt(
            "SELECT operation_token,bound_at,operation,arguments::text AS arguments,settings::text AS settings FROM mimir_operation_bindings WHERE operation_token=$1",
            &[&token],
        ).await?.as_ref().map(decode_binding).transpose()
    }

    /// Reuse the exact key for one logical action, including after a lost reply.
    /// PostgreSQL supplies the token and time. A competing allocation rolls back
    /// completely before reading the winner; it leaves no extra reservation.
    pub async fn reserve_operation(&self, request_key: &str) -> Result<OperationReservation> {
        ensure!(
            !request_key.trim().is_empty(),
            "request_key is required and must not be blank; supply a stable name for this action and reuse that exact key on every retry"
        );
        let mut client = self.client.lock().await;
        const READ: &str = "SELECT r.operation_token,r.reserved_at FROM mimir_operation_request_keys k JOIN mimir_operation_reservations r USING (operation_token) WHERE k.request_key=$1";
        if let Some(row) = client.query_opt(READ, &[&request_key]).await? {
            return decode(row);
        }
        let tx = client.transaction().await?;
        let allocated = decode(tx.query_one(
            "INSERT INTO mimir_operation_reservations DEFAULT VALUES RETURNING operation_token, reserved_at",
            &[],
        ).await?)?;
        let inserted = tx.execute(
            "INSERT INTO mimir_operation_request_keys (request_key,operation_token) VALUES ($1,$2) ON CONFLICT (request_key) DO NOTHING",
            &[&request_key,&allocated.operation_token],
        ).await?;
        if inserted == 1 {
            tx.commit().await?;
            return Ok(allocated);
        }
        tx.rollback().await?;
        decode(client.query_one(READ, &[&request_key]).await?)
    }

    pub async fn read_operation_reservation(
        &self,
        token: Uuid,
    ) -> Result<Option<OperationReservation>> {
        let client = self.client.lock().await;
        client.query_opt(
            "SELECT operation_token, reserved_at FROM mimir_operation_reservations WHERE operation_token=$1",
            &[&token],
        ).await?.map(decode).transpose()
    }
}
