//! Public operation controls and explicit saved-outcome responses.
//! A reservation or cancellation receipt is not a business completion receipt.
use anyhow::{Context, Result};
use mimir_core::{
    interaction::{CorrectionItem, Location, NeedsInput},
    operation_catalogue::ControlOperation,
    store::OperationOutcome,
    validation::{Code, Fault, Segment},
    MimirService,
};
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
            "description":"Read the original operation request and saved outcome without rerunning its business changes. A completed response contains the original result. A pending or needs_input response explains which original work remains; keep the token and discuss an uncertain correction with the user. A cancellation record prevents further publication but does not by itself confirm worker cleanup.",
            "inputSchema":{"type":"object","properties":{
                "operation_token":{"type":"string","format":"uuid","description":"The exact PostgreSQL-issued token returned by reserve_operation."}},"required":["operation_token"]}
        }),
        json!({
            "name":"cancel_operation",
            "description":"Explicitly request cancellation of an unfinished operation only after the user decides to cancel it. Preserve committed changes and saved answers, revoke preparation ownership and block further publication under this token. A completed operation keeps its original result. Never cancel automatically to bypass a problem. A durable cancellation receipt does not confirm that every worker has finished cleanup; the response states that distinction.",
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

pub fn correction(
    field: &str,
    code: Code,
    message: String,
    expected: String,
    suggested: &str,
) -> Result<Value> {
    let issue = CorrectionItem::new(
        Location::Arguments,
        Fault {
            path: vec![Segment::Key(field.into())],
            code,
            message,
        },
        expected,
        suggested.into(),
    )?;
    Ok(mimir_json::to_value(NeedsInput::new(issue, vec![])?)?)
}

pub fn outcome(token: Uuid, result: OperationOutcome) -> Result<Value> {
    // Own the growing response even when a later conversion returns an error.
    // Deep stored arguments/results use the common nonrecursive JSON lifetime.
    let mut response = mimir_json::Document::new(json!({"operation_token":token}));
    match result {
        OperationOutcome::UnknownToken => return correction("operation_token",Code::MissingReference,
            format!("Token {token} has no reservation in the selected database."),
            "The original PostgreSQL-issued token for this intended action.".into(),
            "If the reservation reply was lost, call reserve_operation with its original request_key. Check the selected configuration and database. Ask the user if the intended action is uncertain; do not invent a replacement token."),
        OperationOutcome::Reserved => {
            response["status"] = json!("reserved");
            response["suggested_fix"] = json!("Call the intended write with this operation_token and its complete arguments. Keep exactly those arguments on retries.");
        }
        OperationOutcome::AwaitingPlan(binding) | OperationOutcome::AwaitingCompletion(binding) => {
            response["status"] = json!("pending");
            response["original_request"] = mimir_json::to_value(binding)?;
            response["suggested_fix"] = json!("Repeat the original write with the same token and arguments. Keep its saved answers; do not infer completion from one answer. Discuss an unresolved prerequisite with the user.");
        }
        OperationOutcome::ChangedRequest(binding) => return correction("operation_token",Code::WrongIdentity,
            format!("Token {token} is already bound to different work. This call did not replace its original request."),
            format!("The unchanged original request: {}",mimir_json::to_string(&binding)?),
            "Read the original request and result with operation_outcome. Retry the exact original request, or ask the user whether to cancel unfinished work before reserving deliberately separate corrected work. Do not replace stored arguments."),
        OperationOutcome::Pending { binding, next_step, saved_replies } => {
            response["status"] = json!("pending");
            response["original_request"] = mimir_json::to_value(binding)?;
            response["next_step"] = mimir_json::to_value(next_step)?;
            response["saved_replies"] = mimir_json::to_value(saved_replies)?;
            response["suggested_fix"] = json!("Repeat the original write with the same token and arguments to resume its saved next step. Discuss an unresolved prerequisite with the user; do not skip steps or silently cancel.");
        }
        OperationOutcome::Completed { binding, outcome } => {
            response["status"] = json!("completed");
            response["original_request"] = mimir_json::to_value(binding)?;
            response["result"] = mimir_json::clone_value(outcome.reply());
        }
        OperationOutcome::NeedsRecovery { binding, reason } => return correction("operation_token",Code::MalformedInput,
            format!("Token {token} needs its saved records reconciled: {reason}"),
            format!("The original request and its complete saved plan/answers: {}",mimir_json::to_string(&binding)?),
            "Keep the original token, request, plan and saved answers. Explain the inconsistency to the user and resolve those records before executing more work. Do not invent a success result, change the saved plan or repeat committed changes."),
        OperationOutcome::Cancelled { cancellation, binding, saved_replies } => {
            response["status"] = json!("cancelled");
            response["cancellation"] = mimir_json::to_value(cancellation)?;
            response["original_request"] = mimir_json::to_value(binding)?;
            response["saved_replies"] = mimir_json::to_value(saved_replies)?;
            response["worker_cleanup"] = json!("not_confirmed_by_this_receipt");
            response["message"] = json!("Cancellation is durable and further business publication under this token is blocked. Committed changes and saved answers remain. This database receipt does not establish that every worker has finished stopping.");
        }
    }
    Ok(response.into_value())
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
            outcome(token, service.read_operation_outcome(token, None).await?)
        }
        ControlOperation::CancelOperation => {
            let token = token(input)?;
            service.record_operation_cancellation(token).await?;
            outcome(token, service.read_operation_outcome(token, None).await?)
        }
    }
}
