//! CLI writers use the same closed registered handlers and saved answers as MCP.
use super::{Cli, Command as Application, DeleteCmd, DocCmd, EvidenceCmd};
use anyhow::{Context, Result};
use mimir_core::{
    interaction::{CorrectionItem, Location, NeedsInput},
    operation_catalogue::{GraphOperation as G, Operation, RegisteredWrite},
    operation_reporting,
    store::OperationOutcome,
    validation::{Code, Fault, Segment},
    MimirService,
};
use serde_json::{json, Value};
use uuid::Uuid;

#[derive(clap::Subcommand)]
pub(super) enum Command {
    /// Reserve a PostgreSQL-issued token. Repeat the same key after a lost reply.
    Reserve { request_key: String },
    /// Read saved work without repeating changes. Supply --operation-token.
    Outcome,
    /// Cancel unfinished work only after an explicit user decision.
    Cancel,
}

enum Route {
    Write(RegisteredWrite, mimir_json::Document),
    Backfill,
    Control,
}
fn write(operation: G, mut arguments: Value, project: Option<&String>) -> Route {
    if let Some(project) = project {
        arguments["project"] = json!(project);
    }
    Route::Write(
        Operation::Graph(operation)
            .registered_write()
            .expect("only declared business writers enter CLI execution"),
        mimir_json::Document::new(arguments),
    )
}
// Exhaustive classification makes a new CLI leaf an explicit routing decision.
fn route(command: &Application) -> Option<Route> {
    Some(match command {
        Application::Operation(_) => Route::Control,
        Application::Delete(DeleteCmd::Belief { id }) => {
            write(G::DeleteBelief, json!({"id":id}), None)
        }
        Application::Delete(DeleteCmd::Pattern { id }) => {
            write(G::DeletePattern, json!({"id":id}), None)
        }
        Application::Forget { project } => {
            write(G::DeleteProject, json!({"project":project}), None)
        }
        Application::Decay { factor, project } => write(
            G::DecayAll,
            json!({"decay_factor":factor}),
            project.as_ref(),
        ),
        Application::SweepDefeated { threshold, project } => write(
            G::SweepExpiredDefeated,
            json!({"prob_threshold":threshold}),
            project.as_ref(),
        ),
        Application::Evidence(EvidenceCmd::Add {
            chunk_id,
            belief_id,
            weight,
        }) => write(
            G::AddEvidence,
            json!({"chunk_id":chunk_id,"belief_id":belief_id,"weight":weight}),
            None,
        ),
        Application::Doc(DocCmd::Load { path, project }) => {
            write(G::LoadDocument, json!({"path":path}), project.as_ref())
        }
        Application::Doc(DocCmd::Clear { path }) => {
            write(G::ClearDocument, json!({"path":path}), None)
        }
        Application::Reembed => Route::Backfill,
        Application::Config(_)
        | Application::Judge(_)
        | Application::Init { .. }
        | Application::Stats
        | Application::List { .. }
        | Application::Patterns { .. }
        | Application::Query { .. }
        | Application::Evidence(EvidenceCmd::List { .. })
        | Application::Contradictions { .. }
        | Application::Doc(DocCmd::Query { .. })
        | Application::Intervene { .. }
        | Application::Hook { .. } => return None,
    })
}
fn issue(code: Code, message: &str, expected: &str, suggested: &str) -> NeedsInput {
    NeedsInput::new(
        CorrectionItem::new(
            Location::Arguments,
            Fault {
                path: vec![Segment::Key("operation_token".into())],
                code,
                message: message.into(),
            },
            expected.into(),
            suggested.into(),
        )
        .expect("CLI operation correction includes its repair"),
        vec![],
    )
    .expect("one correction")
}
pub(super) fn admit(cli: &Cli) -> Option<NeedsInput> {
    let needs_token = match &cli.command {
        Application::Operation(Command::Reserve { request_key }) => {
            if request_key.trim().is_empty() {
                return Some(NeedsInput::new(CorrectionItem::new(Location::Arguments,Fault{path:vec![Segment::Key("request_key".into())],code:Code::EmptyText,message:"The reservation key is blank; no action was reserved.".into()},"A stable nonblank key identifying this intended action.".into(),"Repeat the original key after a lost reply. Ask the user if the intended action is uncertain; do not reserve replacement work to bypass a problem.".into()).expect("complete reservation guidance"),vec![]).expect("one correction"));
            }
            false
        }
        _ => route(&cli.command).is_some(),
    };
    match (needs_token,cli.operation_token) {
        (true,None)=>Some(issue(Code::MissingField,"This command requires the original PostgreSQL-issued operation token before any business work starts.","--operation-token UUID returned by mimir operation reserve REQUEST_KEY.","Reserve this intended action first and keep its key and token. After a lost reply, repeat the original reservation key, then retry this exact command with its original token. Do not invent a UUID.")),
        (false,Some(_))=>Some(issue(Code::UnsupportedCombination,"This command does not use an operation token.","Omit --operation-token for this command.","Use operation outcome to inspect a token, or supply it to the intended business write. Check the command help; do not silently change the requested action.")),
        _=>None,
    }
}
fn print(value: Value) -> Result<()> {
    println!(
        "{}",
        mimir_json::to_string(&mimir_json::Document::new(value))?
    );
    Ok(())
}

pub(super) async fn dispatch(cli: &Cli) -> Result<bool> {
    let Some(route) = route(&cli.command) else {
        return Ok(false);
    };
    let service = super::connect().await?;
    let expected = match &route {
        Route::Write(writer, arguments) => Some((writer.operation().name(), arguments.clone())),
        Route::Backfill => Some(("reembed", mimir_json::Document::new(json!({})))),
        Route::Control => None,
    };
    let result = match route {
        Route::Control => {
            match &cli.command {
                Application::Operation(Command::Reserve { request_key }) => {
                    let reserved = service.reserve_operation(request_key).await?;
                    print(
                        json!({"status":"reserved","operation_token":reserved.operation_token,"reserved_at":reserved.reserved_at,"request_key":request_key,"message":"No business work has run. Supply this token to the intended write; preserve the key and token after a lost reply."}),
                    )?;
                }
                Application::Operation(Command::Outcome) => {
                    let token = cli.operation_token.context("admitted operation token")?;
                    print(operation_reporting::outcome(
                        token,
                        service.read_operation_outcome(token, None).await?,
                    )?)?;
                }
                Application::Operation(Command::Cancel) => {
                    let token = cli.operation_token.context("admitted cancellation token")?;
                    let cancelled = service.cancel_operation(token).await?;
                    let confirmed = cancelled.local_cleanup_confirmed();
                    let mut response = mimir_json::Document::new(operation_reporting::outcome(
                        token,
                        cancelled.into_outcome(),
                    )?);
                    if confirmed {
                        response["worker_cleanup"] = json!("confirmed_for_this_server");
                        response["message"]=json!("Cancellation is durable. This CLI process stopped its own registered work before replying; cleanup in other processes is not confirmed. Earlier committed changes and saved answers remain.");
                    }
                    print(response.into_value())?;
                }
                _ => unreachable!("the exhaustive route selects only operation controls"),
            }
            return Ok(true);
        }
        Route::Write(writer, arguments) => {
            service
                .execute_registered_write(
                    writer,
                    cli.operation_token.context("admitted write token")?,
                    arguments,
                )
                .await
        }
        Route::Backfill => {
            service
                .reembed_operation(cli.operation_token.context("admitted backfill token")?)
                .await
        }
    };
    let token = cli.operation_token.context("admitted write token")?;
    match result {
        Ok(outcome) => print(operation_reporting::outcome(token, outcome)?)?,
        Err(error) => {
            report_error(
                &service,
                token,
                expected.context("business route has an original request")?,
                error,
            )
            .await?
        }
    }
    Ok(true)
}

async fn report_error(
    service: &MimirService,
    token: Uuid,
    (operation, arguments): (&str, mimir_json::Document),
    error: anyhow::Error,
) -> Result<()> {
    // A stopped call or lost reply must read the durable fact before reporting
    // its business outcome. This call cannot change a token's bound request.
    if !error.is::<mimir_core::WriteAdmissionIssue>() {
        if let Some(binding) = service.read_operation_binding(token).await? {
            let expected = mimir_core::store::OperationBindingRequest::new(
                operation.into(),
                arguments.into_value(),
                mimir_json::clone_value(binding.request.settings()),
            )?;
            if let Ok(
                outcome @ (OperationOutcome::Completed { .. } | OperationOutcome::Cancelled { .. }),
            ) = service.read_operation_outcome(token, Some(&expected)).await
            {
                return print(operation_reporting::outcome(token, outcome)?);
            }
        }
    }
    if operation == "sweep_expired_defeated" {
        if let Some(issue) = error.downcast_ref::<mimir_core::graph::StoredBeliefIssue>() {
            return print(mimir_json::to_value(NeedsInput::new(
                issue.issue().clone(),
                vec![],
            )?)?);
        }
    }
    let correction = if let Some(value) = error.downcast_ref::<mimir_core::WriteAdmissionIssue>() {
        Some(value.correction())
    } else if let Some(value) = error.downcast_ref::<mimir_core::preparation::PreparationRequired>()
    {
        Some(value.correction())
    } else if let Some(value) = error.downcast_ref::<mimir_core::interaction::RequestCorrection>() {
        Some(value.correction())
    } else {
        error
            .downcast_ref::<mimir_core::config::RetirementIssue>()
            .map(|value| value.correction())
    };
    if let Some(correction) = correction {
        return print(mimir_json::to_value(correction)?);
    }
    Err(error.context(format!("Keep operation token {token}; inspect it with mimir operation outcome --operation-token {token} before retrying the original command. Do not infer rollback or completion from this error.")))
}
