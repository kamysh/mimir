//! A no-change response requires an acknowledged rollback, not queued cleanup.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;
use anyhow::Result;
use mimir_core::{config::Config, db, graph::Pattern, store::*, MimirService};
use serde_json::json;
use uuid::Uuid;

#[derive(Debug)]
struct RequiresDecision(&'static str);
impl std::fmt::Display for RequiresDecision {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(self.0)
    }
}
impl std::error::Error for RequiresDecision {}

fn config() -> Config {
    Config {
        database: isolation::fixture().database_config(),
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
        retirement: None,
    }
}
async fn identity() -> Result<Uuid> {
    Ok(db::connect(&config().database)
        .await?
        .query_one("SELECT gen_random_uuid()", &[])
        .await?
        .get(0))
}
async fn prepared() -> Result<(AgeStore, MimirService, Uuid, Uuid, RegisteredStep, String)> {
    let cfg = config();
    let service = MimirService::connect(&cfg).await?;
    let store = AgeStore::new(
        db::connect(&cfg.database).await?,
        cfg.database.dbname.clone(),
    )?;
    let mut pattern = Pattern::new_in_project(
        "refusal fixture".into(),
        "require rollback before returning".into(),
        0.5,
        format!("refusal-{}", identity().await?),
    )?;
    pattern.id = identity().await?;
    store.insert_pattern(&pattern).await?;
    let token = service
        .reserve_operation(&identity().await?.to_string())
        .await?
        .operation_token;
    let request =
        OperationBindingRequest::new("delete_pattern".into(), json!({"id":pattern.id}), json!({}))?;
    service.bind_operation_request(token, &request).await?;
    let PlanDecision::Ready(plan) = service
        .prepare_operation(token, &request, |_, _| Box::pin(async { Ok(vec![]) }))
        .await?
    else {
        panic!("plan missing")
    };
    let step = plan.steps().remove(0);
    let sql=format!("SELECT * FROM ag_catalog.cypher('{}', $$ MATCH (p:Pattern {{id:'{}'}}) DETACH DELETE p RETURN 1 $$) AS (ok ag_catalog.agtype)",cfg.database.dbname,pattern.id);
    Ok((store, service, pattern.id, token, step, sql))
}
async fn remains_pending(service: &MimirService, token: Uuid, step: &RegisteredStep) -> Result<()> {
    assert!(service
        .read_operation_step(token, step.id())
        .await?
        .is_none());
    assert!(service
        .read_operation_step(token, "@operation-result")
        .await?
        .is_none());
    assert!(service.read_operation_cancellation(token).await?.is_none());
    assert!(
        matches!(service.read_operation_outcome(token,None).await?,OperationOutcome::Pending {saved_replies,..} if saved_replies.is_empty())
    );
    Ok(())
}

#[tokio::test]
async fn acknowledged_refusal_keeps_the_original_diagnostic_and_stores_no_completion() -> Result<()>
{
    let (store, service, id, token, step, sql) = prepared().await?;
    let before = serde_json::to_value(store.get_pattern(id).await?)?;
    let error = service
        .commit_final_operation_step(&step, move |tx, _| {
            Box::pin(async move {
                tx.query("SELECT pg_advisory_xact_lock(671942183)", &[])
                    .await?;
                tx.query(&sql, &[]).await?;
                Err(RequiresDecision(
                    "The supporting passage changed; ask the user before writing.",
                )
                .into())
            })
        })
        .await
        .unwrap_err();
    assert!(error.downcast_ref::<RequiresDecision>().is_some());
    assert_eq!(serde_json::to_value(store.get_pattern(id).await?)?, before);
    let audit = db::connect(&config().database).await?;
    assert!(
        audit
            .query_one("SELECT pg_try_advisory_xact_lock(671942183)", &[])
            .await?
            .get::<_, bool>(0),
        "rollback must release the transaction's lock before the no-change diagnostic returns"
    );
    remains_pending(&service, token, &step).await?;
    store.delete_pattern(id).await?;
    Ok(())
}

#[tokio::test]
async fn unconfirmed_rollback_preserves_both_causes_and_requires_readback() -> Result<()> {
    let (store, service, id, token, step, sql) = prepared().await?;
    let before = serde_json::to_value(store.get_pattern(id).await?)?;
    let audit = db::connect(&config().database).await?;
    let error = service
        .commit_final_operation_step(&step, move |tx, _| {
            Box::pin(async move {
                tx.query(&sql, &[]).await?;
                let pid: i32 = tx.query_one("SELECT pg_backend_pid()", &[]).await?.get(0);
                assert!(audit
                    .query_one("SELECT pg_terminate_backend($1)", &[&pid])
                    .await?
                    .get::<_, bool>(0));
                Err(RequiresDecision(
                    "Original cause: supporting passage α changed; a user decision is required.",
                )
                .into())
            })
        })
        .await
        .unwrap_err();
    assert!(
        error.downcast_ref::<RequiresDecision>().is_none(),
        "an unconfirmed rollback cannot be a certified no-change diagnostic"
    );
    let message = format!("{error:#}");
    assert!(
        message.contains("rollback could not be confirmed"),
        "{message}"
    );
    assert!(
        message.contains("supporting passage α changed"),
        "{message}"
    );
    assert!(
        message.contains(&token.to_string())
            && message.contains("read its saved steps and operation outcome"),
        "{message}"
    );
    let reopened = MimirService::connect(&config()).await?;
    remains_pending(&reopened, token, &step).await?;
    assert_eq!(serde_json::to_value(store.get_pattern(id).await?)?, before);
    store.delete_pattern(id).await?;
    Ok(())
}
