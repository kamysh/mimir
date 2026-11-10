//! Public operation controls and explicit saved-outcome responses.
//! A reservation or cancellation receipt is not a business completion receipt.
use anyhow::{Context, Result};
pub use mimir_core::operation_reporting::{correction, outcome};
use mimir_core::{operation_catalogue::ControlOperation, validation::Code, MimirService};
use serde_json::{json, Value};
use uuid::Uuid;

pub fn descriptors() -> Vec<Value> {
    vec![
        json!({
            "name":"reserve_operation",
            "description":"Reserve a PostgreSQL-issued operation token before a write. Supply a stable request_key for this intended action and keep it until its outcome is known. If this reply is lost, repeat the same request_key to recover the same token and reservation time. Reservation does not execute or complete any business work. Use a different key only for a deliberately separate action, not to bypass an unfinished operation.",
            "inputSchema":{"type":"object","properties":{
                "request_key":{"type":"string","minLength":1,"description":"A stable nonblank key for this intended action; reuse it after a lost reply. Do not silently trim or replace it."}},"required":["request_key"]}
        }),
        json!({
            "name":"operation_outcome",
            "description":"Read the original operation request and saved outcome without rerunning its business changes. A completed response contains the original result. Terminal readback also lists executions still lacking physical-stop acknowledgements, with their automatic host/address, program and process identity; completed business data alone does not prove duplicate workers stopped. A pending or needs_input response explains which original work remains; keep the token and discuss an uncertain correction with the user. A cancellation record prevents further publication but does not by itself confirm worker cleanup.",
            "inputSchema":{"type":"object","properties":{
                "operation_token":{"type":"string","format":"uuid","description":"The exact PostgreSQL-issued token returned by reserve_operation."}},"required":["operation_token"]}
        }),
        json!({
            "name":"cancel_operation",
            "description":"Cancel only after the user explicitly decides to stop this action. Preserve committed changes and saved answers, revoke unfinished publication, and wait for every registered copy to confirm physical cleanup. A disconnected copy remains pending without a deadline; another request can inspect its owner using operation_outcome. A completed action stops any duplicate work and returns its exact original completed answer without a cancellation row. Never cancel automatically to bypass a problem. A durable cancellation record alone is not physical-stop confirmation.",
            "inputSchema":{"type":"object","properties":{
                "operation_token":{"type":"string","format":"uuid","description":"The exact token whose unfinished work the user explicitly decided to cancel."}},"required":["operation_token"]}
        }),
    ]
}

pub fn token(input: &Value) -> Result<Uuid> {
    let text = input
        .get("operation_token")
        .and_then(Value::as_str)
        .context("operation_token must be supplied using the advertised UUID field")?;
    Uuid::parse_str(text)
        .context("operation_token must be the PostgreSQL-issued UUID returned by reserve_operation")
}

pub async fn call(
    operation: ControlOperation,
    service: &MimirService,
    input: &Value,
) -> Result<Value> {
    match operation {
        ControlOperation::ReserveOperation => {
            let key = input
                .get("request_key")
                .and_then(Value::as_str)
                .context("Supply the original stable request_key")?;
            if key.trim().is_empty() {
                return correction("request_key",Code::EmptyText,
                    "The reservation key is blank; no reservation was created.".into(),
                    "A stable nonblank key for this intended action.".into(),
                    "Supply the original key when recovering an action. Choose a new key only for deliberately separate work; ask the user if the intended action is uncertain.");
            }
            let reserved = service.reserve_operation(key).await?;
            Ok(
                json!({"status":"reserved","operation_token":reserved.operation_token,
                "reserved_at":reserved.reserved_at,"request_key":key,
                "message":"No business work has run. Use this token with the complete intended write and keep the same request_key to recover this reservation after a lost reply."}),
            )
        }
        ControlOperation::OperationOutcome => {
            let token = token(input)?;
            mimir_core::operation_reporting::readback(
                token,
                service.read_operation_outcome(token, None).await?,
            )
        }
        ControlOperation::CancelOperation => {
            let token = token(input)?;
            let cancelled = service.cancel_operation(token).await?;
            mimir_core::operation_reporting::cancellation(token, cancelled)
        }
    }
}
