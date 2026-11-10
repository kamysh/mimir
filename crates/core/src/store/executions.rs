//! Durable ownership is registered before work and acknowledged after physical
//! cleanup. No connection lifetime, lease or elapsed time acknowledges a copy.
use super::{cancellations, operation_plans::RESULT_KEY};
use anyhow::{Context, Result};
use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};
use tokio_postgres::{Client, GenericClient, Row};
use uuid::Uuid;

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct ExecutionReceipt {
    pub execution_id: Uuid,
    pub operation_token: Uuid,
    pub registered_at: DateTime<Utc>,
    pub stopped_at: Option<DateTime<Utc>>,
    pub owner_program: String,
    pub owner_pid: i64,
    pub owner_host: Option<String>,
    pub owner_host_source: Option<String>,
    pub client_address: Option<String>,
}

fn receipt(row: &Row) -> Result<ExecutionReceipt> {
    Ok(ExecutionReceipt {
        execution_id: row.try_get("execution_id")?,
        operation_token: row.try_get("operation_token")?,
        registered_at: row.try_get("registered_at")?,
        stopped_at: row.try_get("stopped_at")?,
        owner_program: row.try_get("owner_program")?,
        owner_pid: row.try_get("owner_pid")?,
        owner_host: row.try_get("owner_host")?,
        owner_host_source: row.try_get("owner_host_source")?,
        client_address: row.try_get("client_address")?,
    })
}

const COLUMNS: &str = "execution_id,operation_token,registered_at,stopped_at,owner_program,owner_pid,owner_host,owner_host_source,client_address";

fn owner_identity() -> Result<(String, i64, Option<String>, Option<String>)> {
    let program = std::env::current_exe()?.display().to_string();
    let pid = i64::from(std::process::id());
    // Read the complete kernel value; no hostname buffer, ASCII filter or
    // application length quota. Other platforms can supply a labelled hint.
    if cfg!(target_os = "linux") {
        if let Ok(host) = std::fs::read_to_string("/proc/sys/kernel/hostname") {
            let host = host.trim_end_matches('\n');
            if !host.is_empty() {
                return Ok((
                    program,
                    pid,
                    Some(host.to_owned()),
                    Some("kernel_hostname".into()),
                ));
            }
        }
    }
    for key in ["HOSTNAME", "COMPUTERNAME"] {
        if let Ok(host) = std::env::var(key) {
            if !host.is_empty() {
                return Ok((
                    program,
                    pid,
                    Some(host),
                    Some(format!("environment_hint:{key}")),
                ));
            }
        }
    }
    Ok((program, pid, None, None))
}

/// RETURNING was read before COMMIT was attempted. The owner retains this ID
/// and stops without beginning its body; a lost reply never allocates a second
/// execution or turns an uncertain registration into permission to start.
#[derive(Debug)]
pub(crate) struct RegistrationUnconfirmed {
    pub execution: ExecutionReceipt,
    pub cause: tokio_postgres::Error,
}
impl std::fmt::Display for RegistrationUnconfirmed {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Execution {} registration is uncertain: {}. No work started. Keep this execution ID and read its stop state; do not allocate replacement work.", self.execution.execution_id, self.cause)
    }
}
impl std::error::Error for RegistrationUnconfirmed {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.cause)
    }
}

pub(crate) async fn register<F, Guard>(
    client: &mut Client,
    token: Uuid,
    own: F,
) -> Result<Option<(ExecutionReceipt, Guard)>>
where
    F: FnOnce(&ExecutionReceipt) -> Guard,
{
    let (program, pid, host, source) = owner_identity()?;
    let tx = client.transaction().await?;
    if !active_token(&tx, token).await? {
        tx.rollback().await?;
        return Ok(None);
    }
    let execution = receipt(&tx.query_one(
        &format!("INSERT INTO mimir_operation_executions(operation_token,owner_program,owner_pid,owner_host,owner_host_source) VALUES($1,$2,$3,$4,$5) RETURNING {COLUMNS}"), &[&token,&program,&pid,&host,&source],
    ).await?)?;
    // Retain the identity in the request's owner before COMMIT is sent. If
    // this future itself is dropped during commit, its guard still records
    // that no body started and owns the eventual acknowledgement attempt.
    let guard = own(&execution);
    if let Err(cause) = tx.commit().await {
        return Err(RegistrationUnconfirmed { execution, cause }.into());
    }
    Ok(Some((execution, guard)))
}

async fn active_token(tx: &tokio_postgres::Transaction<'_>, token: Uuid) -> Result<bool> {
    Ok(cancellations::lock_token(tx, token).await?
        && cancellations::lookup(tx, token).await?.is_none()
        && tx
            .query_opt(
                "SELECT 1 FROM mimir_operation_step_replies WHERE operation_token=$1 AND step=$2",
                &[&token, &RESULT_KEY],
            )
            .await?
            .is_none())
}

/// A child borrows its actual enclosing execution, but still checks the same
/// durable publication fence before starting. This transaction writes no row.
pub(crate) async fn permits_child(client: &mut Client, token: Uuid) -> Result<bool> {
    let tx = client.transaction().await?;
    let permitted = active_token(&tx, token).await?;
    tx.rollback().await?;
    Ok(permitted)
}

pub(crate) async fn acknowledge(
    client: &mut Client,
    execution: &ExecutionReceipt,
) -> Result<Option<ExecutionReceipt>> {
    // This row is immutable after its first acknowledgement. The guard is
    // deliberately independent of cancellation: a stopped owner must still ACK.
    let tx = client.transaction().await?;
    // In particular this settles an interrupted registration COMMIT before
    // treating an absent row as rolled back rather than still in flight.
    if !cancellations::lock_token(&tx, execution.operation_token).await? {
        tx.rollback().await?;
        return Ok(None);
    }
    let updated = tx.query_opt(
        &format!("UPDATE mimir_operation_executions SET stopped_at=clock_timestamp() WHERE execution_id=$1 AND operation_token=$2 AND stopped_at IS NULL RETURNING {COLUMNS}"),
        &[&execution.execution_id, &execution.operation_token],
    ).await?;
    let saved = if let Some(row) = updated {
        Some(receipt(&row)?)
    } else {
        tx.query_opt(
        &format!("SELECT {COLUMNS} FROM mimir_operation_executions WHERE execution_id=$1 AND operation_token=$2"),
        &[&execution.execution_id, &execution.operation_token],
    ).await?.as_ref().map(receipt).transpose()?
    };
    tx.commit().await?;
    Ok(saved)
}

pub(crate) async fn pending<C: GenericClient + Sync>(
    client: &C,
    token: Uuid,
) -> Result<Vec<ExecutionReceipt>> {
    client.query(
        &format!("SELECT {COLUMNS} FROM mimir_operation_executions WHERE operation_token=$1 AND stopped_at IS NULL ORDER BY execution_id"), &[&token],
    ).await?.iter().map(receipt).collect::<Result<Vec<_>>>()
        .context("Read every outstanding physical execution; do not infer cleanup from publication revocation")
}

impl super::AgeStore {
    pub(crate) async fn pending_execution_stops(
        &self,
        token: Uuid,
    ) -> Result<Vec<ExecutionReceipt>> {
        pending(&*self.client.lock().await, token).await
    }
}
