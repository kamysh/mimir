//! Storage metadata and original answers round-trip past the old JSON depth
//! guard. These tests use the maintained disposable fixture only.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;
use anyhow::Result;
use mimir_core::store::{
    OperationBindingDecision, OperationBindingRequest, OperationOutcome, PlanDecision, StepDecision,
};
use mimir_core::{config::Config, db, MimirService};
use serde_json::json;

#[tokio::test]
async fn deep_json_request_and_original_answers_survive_saved_step_and_reconnection() -> Result<()>
{
    let cfg = Config {
        database: isolation::fixture().database_config(),
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
        retirement: None,
    };
    let service = MimirService::connect(&cfg).await?;
    let audit = db::connect(&cfg.database).await?;
    let key: String = audit
        .query_one("SELECT gen_random_uuid()::text", &[])
        .await?
        .get(0);
    let reservation = service.reserve_operation(&key).await?;
    let token = reservation.operation_token;
    let text = format!(r#"{{"nested":{}null{}}}"#, "[".repeat(256), "]".repeat(256));
    let payload = mimir_json::parse(&text)?;
    let request = OperationBindingRequest::new(
        "insert_pattern".into(),
        payload.clone().into_value(),
        json!({}),
    )?;
    assert!(matches!(
        service.bind_operation_request(token, &request).await?,
        OperationBindingDecision::Bound(_)
    ));
    let PlanDecision::Ready(plan) = service
        .prepare_operation(token, &request, |_, _| Box::pin(async { Ok(vec![]) }))
        .await?
    else {
        panic!("plan missing")
    };
    let step = plan.steps().remove(0);
    let original = payload.clone();
    let StepDecision::Done(saved) = service
        .commit_final_operation_step(&step, move |_, _| {
            Box::pin(async move { Ok((original.clone().into_value(), original.into_value())) })
        })
        .await?
    else {
        panic!("answer missing")
    };
    assert!(mimir_json::equal(&saved.reply, &payload));
    drop(service);
    let reopened = MimirService::connect(&cfg).await?;
    assert_eq!(
        reopened
            .read_operation_binding(token)
            .await?
            .unwrap()
            .request,
        request
    );
    assert_eq!(
        reopened.read_operation_step(token, step.id()).await?,
        Some(saved)
    );
    // Dropping a call before its first poll must also own and release its input.
    drop(reopened.complete_operation(&plan, payload.clone().into_value()));
    let OperationOutcome::Completed { outcome, .. } = reopened
        .read_operation_outcome(token, Some(&request))
        .await?
    else {
        panic!("completed answer missing")
    };
    assert!(mimir_json::equal(outcome.reply(), &payload));
    Ok(())
}
