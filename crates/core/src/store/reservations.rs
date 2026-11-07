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
    arguments: Value,
    settings: Value,
}

impl OperationBindingRequest {
    pub fn new(operation: String, arguments: Value, settings: Value) -> Result<Self> {
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
}

fn decode_binding(row: &Row) -> Result<OperationBinding> {
    Ok(OperationBinding {
        operation_token: row.try_get("operation_token")?,
        bound_at: row.try_get("bound_at")?,
        request: OperationBindingRequest::new(
            row.try_get("operation")?,
            serde_json::from_str(row.try_get::<_, &str>("arguments")?)?,
            serde_json::from_str(row.try_get::<_, &str>("settings")?)?,
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

impl AgeStore {
    /// A lost acknowledgement must be read back with the same token. Never
    /// allocate a replacement token or overwrite the earlier request here.
    pub async fn bind_operation_request(
        &self,
        token: Uuid,
        request: &OperationBindingRequest,
    ) -> Result<OperationBindingDecision> {
        let arguments = serde_json::to_string(&request.arguments)?;
        let settings = serde_json::to_string(&request.settings)?;
        let client = self.client.lock().await;
        client.execute(
            "INSERT INTO mimir_operation_bindings (operation_token,operation,arguments,settings) SELECT operation_token,$2,$3::text::jsonb,$4::text::jsonb FROM mimir_operation_reservations WHERE operation_token=$1 ON CONFLICT (operation_token) DO NOTHING",
            &[&token, &request.operation, &arguments, &settings],
        ).await?;
        let row = client.query_opt(
            "SELECT operation_token,bound_at,operation,arguments::text AS arguments,settings::text AS settings,operation=$2 AND arguments=$3::text::jsonb AND settings=$4::text::jsonb AS matches FROM mimir_operation_bindings WHERE operation_token=$1",
            &[&token, &request.operation, &arguments, &settings],
        ).await?;
        let Some(row) = row else {
            return Ok(OperationBindingDecision::UnknownToken);
        };
        let binding = decode_binding(&row)?;
        Ok(if row.try_get("matches")? {
            OperationBindingDecision::Bound(binding)
        } else {
            OperationBindingDecision::ChangedRequest(binding)
        })
    }

    pub async fn read_operation_binding(&self, token: Uuid) -> Result<Option<OperationBinding>> {
        let client = self.client.lock().await;
        client.query_opt(
            "SELECT operation_token,bound_at,operation,arguments::text AS arguments,settings::text AS settings FROM mimir_operation_bindings WHERE operation_token=$1",
            &[&token],
        ).await?.as_ref().map(decode_binding).transpose()
    }

    /// PostgreSQL supplies both values. No business handler, automatic retry,
    /// expiry, cleanup policy or application UUID generator runs here.
    pub async fn reserve_operation(&self) -> Result<OperationReservation> {
        let client = self.client.lock().await;
        decode(client.query_one(
            "INSERT INTO mimir_operation_reservations DEFAULT VALUES RETURNING operation_token, reserved_at",
            &[],
        ).await?)
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
