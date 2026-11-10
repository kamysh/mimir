//! Shared saved-operation reports for MCP and CLI. Database facts and worker
//! cleanup receipts have deliberately separate meanings.
use crate::{
    interaction::{CorrectionItem, Location, NeedsInput},
    store::OperationOutcome,
    validation::{Code, Fault, Segment},
};
use anyhow::Result;
use serde_json::{json, Value};
use uuid::Uuid;

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

/// Report database revocation and physical cleanup separately. A dropped
/// future cannot replace the operating system's missing child-exit receipt.
pub fn cancellation(token: Uuid, result: crate::OperationCancellation) -> Result<Value> {
    let confirmed = result.local_cleanup_confirmed();
    let issues = result.cleanup_issues().to_vec();
    let mut response = mimir_json::Document::new(outcome(token, result.into_outcome())?);
    if !issues.is_empty() {
        response["worker_cleanup"] = json!("unconfirmed_for_this_server");
        response["next_action"] = json!("open_user_dialog");
        response["cleanup_issues"] = mimir_json::to_value(issues)?;
        response["message"] = json!("The saved operation state and earlier committed replies are retained. This Mimir process could not confirm that the listed local workers exited. Explain the operating-system error and private diagnostic location to the user before starting replacement work. Retry cancel_operation with the same token to retry cleanup; do not infer that a dropped request or a database cancellation receipt means the workers stopped.");
    } else if confirmed {
        response["worker_cleanup"] = json!("confirmed_for_this_server");
        response["message"] = json!("Cancellation is durable and further publication under this token is blocked. This Mimir process stopped its owned execution before replying. Cleanup in other processes is not confirmed by this receipt. Earlier committed changes and saved answers remain.");
    }
    Ok(response.into_value())
}
