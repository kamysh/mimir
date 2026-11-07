//! Durable PostgreSQL-issued handles. Reservation alone changes no business row.
use super::AgeStore;
use anyhow::Result;
use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};
use tokio_postgres::Row;
use uuid::Uuid;

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
