//! Read the actual saved operation and physical execution records.
use chrono::{DateTime, Utc};
use tokio_postgres::{Error, Transaction};
use uuid::Uuid;

#[derive(Debug, PartialEq)]
pub struct Reservation {
    pub token: Uuid,
    pub reserved_at: DateTime<Utc>,
}
#[derive(Debug, PartialEq)]
pub struct RequestKey {
    pub key: String,
    pub token: Uuid,
}
#[derive(Debug, PartialEq)]
pub struct Binding {
    pub token: Uuid,
    pub operation: String,
    pub arguments_json: String,
    pub settings_json: String,
    pub bound_at: DateTime<Utc>,
}
#[derive(Debug, PartialEq)]
pub struct Plan {
    pub token: Uuid,
    pub plan_json: String,
}
#[derive(Debug, PartialEq)]
pub struct Reply {
    pub token: Uuid,
    pub step: String,
    pub reply_json: String,
}
#[derive(Debug, PartialEq)]
pub struct Cancellation {
    pub token: Uuid,
    pub cancelled_at: DateTime<Utc>,
}
#[derive(Debug, PartialEq)]
pub struct Execution {
    pub identity: Uuid,
    pub token: Uuid,
    pub program: String,
    pub pid: i64,
    pub host: Option<String>,
    pub host_source: Option<String>,
    pub client_address: Option<String>,
    pub registered_at: DateTime<Utc>,
    pub stopped_at: Option<DateTime<Utc>>,
}
#[derive(Debug, PartialEq)]
pub struct EmbeddingOwner {
    pub token: Uuid,
    pub project: Option<String>,
    pub reserved_at: DateTime<Utc>,
    pub operation_token: Option<Uuid>,
}
#[derive(Debug, PartialEq)]
pub struct Operations {
    pub reservations: Vec<Reservation>,
    pub request_keys: Vec<RequestKey>,
    pub bindings: Vec<Binding>,
    pub plans: Vec<Plan>,
    pub replies: Vec<Reply>,
    pub cancellations: Vec<Cancellation>,
    pub executions: Vec<Execution>,
    pub embedding_owners: Vec<EmbeddingOwner>,
}

pub async fn observe(tx: &Transaction<'_>) -> Result<Operations, Error> {
    let reservations = tx.query("SELECT operation_token,reserved_at FROM public.mimir_operation_reservations ORDER BY operation_token", &[]).await?.into_iter().map(|r| Ok(Reservation { token:r.try_get(0)?,reserved_at:r.try_get(1)? })).collect::<Result<_, Error>>()?;
    let request_keys = tx.query("SELECT request_key,operation_token FROM public.mimir_operation_request_keys ORDER BY request_key", &[]).await?.into_iter().map(|r| Ok(RequestKey { key:r.try_get(0)?,token:r.try_get(1)? })).collect::<Result<_, Error>>()?;
    let bindings = tx.query("SELECT operation_token,operation,arguments::text,settings::text,bound_at FROM public.mimir_operation_bindings ORDER BY operation_token", &[]).await?.into_iter().map(|r| Ok(Binding { token:r.try_get(0)?,operation:r.try_get(1)?,arguments_json:r.try_get(2)?,settings_json:r.try_get(3)?,bound_at:r.try_get(4)? })).collect::<Result<_, Error>>()?;
    let plans = tx.query("SELECT operation_token,plan::text FROM public.mimir_operation_plans ORDER BY operation_token", &[]).await?.into_iter().map(|r| Ok(Plan { token:r.try_get(0)?,plan_json:r.try_get(1)? })).collect::<Result<_, Error>>()?;
    let replies = tx.query("SELECT operation_token,step,reply::text FROM public.mimir_operation_step_replies ORDER BY operation_token,step", &[]).await?.into_iter().map(|r| Ok(Reply { token:r.try_get(0)?,step:r.try_get(1)?,reply_json:r.try_get(2)? })).collect::<Result<_, Error>>()?;
    let cancellations = tx.query("SELECT operation_token,cancelled_at FROM public.mimir_operation_cancellations ORDER BY operation_token", &[]).await?.into_iter().map(|r| Ok(Cancellation { token:r.try_get(0)?,cancelled_at:r.try_get(1)? })).collect::<Result<_, Error>>()?;
    let executions = tx.query("SELECT execution_id,operation_token,owner_program,owner_pid,owner_host,owner_host_source,client_address,registered_at,stopped_at FROM public.mimir_operation_executions ORDER BY execution_id", &[]).await?.into_iter().map(|r| Ok(Execution { identity:r.try_get(0)?,token:r.try_get(1)?,program:r.try_get(2)?,pid:r.try_get(3)?,host:r.try_get(4)?,host_source:r.try_get(5)?,client_address:r.try_get(6)?,registered_at:r.try_get(7)?,stopped_at:r.try_get(8)? })).collect::<Result<_, Error>>()?;
    let embedding_owners = tx.query("SELECT owner_token,project,reserved_at,operation_token FROM public.mimir_embedding_owners ORDER BY owner_token", &[]).await?.into_iter().map(|r| Ok(EmbeddingOwner { token:r.try_get(0)?,project:r.try_get(1)?,reserved_at:r.try_get(2)?,operation_token:r.try_get(3)? })).collect::<Result<_, Error>>()?;
    Ok(Operations {
        reservations,
        request_keys,
        bindings,
        plans,
        replies,
        cancellations,
        executions,
        embedding_owners,
    })
}
