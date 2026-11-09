//! Registered pattern deletion and its original answers share a commit.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;

use anyhow::Result;
use mimir_core::{config::Config, db, graph::Pattern, learning::*, store::*, MimirService};
use serde_json::{json, Value};
use uuid::Uuid;

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

async fn setup() -> Result<(AgeStore, MimirService)> {
    let cfg = config();
    let service = MimirService::connect(&cfg).await?;
    let store = AgeStore::new(db::connect(&cfg.database).await?, cfg.database.dbname)?;
    Ok((store, service))
}

async fn pattern(store: &AgeStore, id: Uuid) -> Result<Pattern> {
    let mut value = Pattern::new_in_project(
        "owned deletion situation".into(),
        "owned deletion approach".into(),
        0.5,
        format!("pattern-deletion-{id}"),
    )?;
    value.id = id;
    store.insert_pattern(&value).await?;
    Ok(value)
}

async fn admitted(
    service: &MimirService,
    operation: &str,
    arguments: Value,
) -> Result<(Uuid, RegisteredStep)> {
    let token = service
        .reserve_operation(&identity().await?.to_string())
        .await?
        .operation_token;
    let request = OperationBindingRequest::new(operation.into(), arguments, json!({}))?;
    service.bind_operation_request(token, &request).await?;
    let PlanDecision::Ready(plan) = service
        .prepare_operation(token, &request, |_, _| Box::pin(async { Ok(vec![]) }))
        .await?
    else {
        panic!("registered plan missing")
    };
    let steps = plan.steps();
    assert_eq!(steps.len(), 1);
    Ok((token, steps[0].clone()))
}

async fn completed_reply(service: &MimirService, token: Uuid) -> Result<Value> {
    let OperationOutcome::Completed { outcome, .. } =
        service.read_operation_outcome(token, None).await?
    else {
        panic!("completed outcome missing")
    };
    Ok(outcome.reply().clone())
}

#[tokio::test]
async fn retry_after_reconnect_keeps_original_true_and_unrelated_records() -> Result<()> {
    let (store, service) = setup().await?;
    let removed = pattern(&store, identity().await?).await?;
    let retained = pattern(&store, identity().await?).await?;
    let retained_before = mimir_json::to_value(store.get_pattern(retained.id).await?)?;
    let (other_token, other_step) =
        admitted(&service, "delete_pattern", json!({"id": identity().await?})).await?;
    let StepDecision::Done(other_reply) = service.delete_pattern_operation(&other_step).await?
    else {
        panic!("unrelated original answer missing")
    };
    let (token, step) = admitted(&service, "delete_pattern", json!({"id": removed.id})).await?;
    let StepDecision::Done(first) = service.delete_pattern_operation(&step).await? else {
        panic!("deletion missing")
    };
    assert_eq!(first.reply, json!({"deleted": true}));
    assert!(store.get_pattern(removed.id).await?.is_none());
    drop(service);
    let reopened = MimirService::connect(&config()).await?;
    let StepDecision::Done(retried) = reopened.delete_pattern_operation(&step).await? else {
        panic!("saved answer missing")
    };
    assert_eq!(retried, first);
    assert_eq!(completed_reply(&reopened, token).await?, first.reply);
    assert_eq!(
        mimir_json::to_value(store.get_pattern(retained.id).await?)?,
        retained_before
    );
    assert_eq!(
        reopened
            .read_operation_step(other_token, other_step.id())
            .await?,
        Some(other_reply)
    );
    assert_eq!(
        completed_reply(&reopened, other_token).await?,
        json!({"deleted":false})
    );
    store.delete_pattern(retained.id).await?;
    Ok(())
}

#[tokio::test]
async fn saved_false_does_not_delete_a_pattern_created_after_completion() -> Result<()> {
    let (store, service) = setup().await?;
    let id = identity().await?;
    let (token, step) = admitted(&service, "delete_pattern", json!({"id":id})).await?;
    let StepDecision::Done(first) = service.delete_pattern_operation(&step).await? else {
        panic!("missing-pattern result absent")
    };
    assert_eq!(first.reply, json!({"deleted":false}));
    pattern(&store, id).await?;
    let before = mimir_json::to_value(store.get_pattern(id).await?)?;
    let StepDecision::Done(retried) = service.delete_pattern_operation(&step).await? else {
        panic!("saved missing-pattern result absent")
    };
    assert_eq!(retried, first);
    assert_eq!(completed_reply(&service, token).await?, first.reply);
    assert_eq!(mimir_json::to_value(store.get_pattern(id).await?)?, before);
    store.delete_pattern(id).await?;
    Ok(())
}

#[tokio::test]
async fn rejected_final_result_rolls_back_deletion_retirement_and_step_answer() -> Result<()> {
    let (store, service) = setup().await?;
    let value = pattern(&store, identity().await?).await?;
    let source_id = identity().await?;
    service
        .record_experience(
            &Experience {
                id: source_id,
                project: value.project.clone().unwrap(),
                context: "owned pattern deletion fixture".into(),
                action: "verify deletion and retirement commit together".into(),
                outcome: Outcome::Success,
                source: ObservationSource::ToolResult,
                evidence: vec!["private fixture".into()],
                belief_ids: vec![],
                pattern_id: Some(value.id),
                learning_items: vec![],
                source_records: vec![],
            },
            0,
        )
        .await?;
    let audit = db::connect(&config().database).await?;
    audit.execute(
        "INSERT INTO mimir_review_candidates(experience_id,candidate_key,kind,node_id,declaration) VALUES($1,'owned-pattern','pattern',$2,'{}'::jsonb)",
        &[&source_id, &value.id],
    ).await?;
    let (token, step) = admitted(&service, "delete_pattern", json!({"id":value.id})).await?;
    let constraint = format!("reject_pattern_result_{}", token.simple());
    audit.batch_execute(&format!("ALTER TABLE mimir_operation_step_replies ADD CONSTRAINT {constraint} CHECK (operation_token <> '{token}'::uuid OR step <> '@operation-result') NOT VALID")).await?;
    let attempted = service.delete_pattern_operation(&step).await;
    audit
        .batch_execute(&format!(
            "ALTER TABLE mimir_operation_step_replies DROP CONSTRAINT {constraint}"
        ))
        .await?;
    assert!(attempted.is_err());
    assert!(store.get_pattern(value.id).await?.is_some());
    assert!(!audit
        .query_one(
            "SELECT retired FROM mimir_review_candidates WHERE node_id=$1",
            &[&value.id]
        )
        .await?
        .get::<_, bool>(0));
    assert!(service
        .read_operation_step(token, step.id())
        .await?
        .is_none());
    assert!(service
        .read_operation_step(token, "@operation-result")
        .await?
        .is_none());
    assert!(matches!(
        service.read_operation_outcome(token, None).await?,
        OperationOutcome::Pending { .. }
    ));
    let source_before: String = audit
        .query_one(
            "SELECT to_jsonb(e)::text FROM mimir_experiences e WHERE id=$1",
            &[&source_id],
        )
        .await?
        .get(0);
    let StepDecision::Done(saved) = service.delete_pattern_operation(&step).await? else {
        panic!("retry did not finish")
    };
    assert_eq!(saved.reply, json!({"deleted":true}));
    assert_eq!(completed_reply(&service, token).await?, saved.reply);
    assert!(store.get_pattern(value.id).await?.is_none());
    assert!(audit
        .query_one(
            "SELECT retired FROM mimir_review_candidates WHERE node_id=$1",
            &[&value.id]
        )
        .await?
        .get::<_, bool>(0));
    assert_eq!(
        audit
            .query_one(
                "SELECT to_jsonb(e)::text FROM mimir_experiences e WHERE id=$1",
                &[&source_id]
            )
            .await?
            .get::<_, String>(0),
        source_before
    );
    Ok(())
}

#[tokio::test]
async fn another_registered_operation_cannot_enter_pattern_deletion() -> Result<()> {
    let (store, service) = setup().await?;
    let value = pattern(&store, identity().await?).await?;
    let before = mimir_json::to_value(store.get_pattern(value.id).await?)?;
    let (token, wrong_step) =
        admitted(&service, "delete_project", json!({"project":value.project})).await?;
    let error = service
        .delete_pattern_operation(&wrong_step)
        .await
        .unwrap_err();
    assert!(error.to_string().contains("registered delete_pattern step"));
    assert_eq!(
        mimir_json::to_value(store.get_pattern(value.id).await?)?,
        before
    );
    assert!(service
        .read_operation_step(token, wrong_step.id())
        .await?
        .is_none());
    assert!(matches!(
        service.read_operation_outcome(token, None).await?,
        OperationOutcome::Pending { .. }
    ));
    store.delete_pattern(value.id).await?;
    Ok(())
}

#[tokio::test]
async fn missing_final_answer_requires_recovery_without_reapplying_deletion() -> Result<()> {
    let (store, service) = setup().await?;
    let id = identity().await?;
    pattern(&store, id).await?;
    let (token, step) = admitted(&service, "delete_pattern", json!({"id":id})).await?;
    let audit = db::connect(&config().database).await?;
    let answer = json!({"deleted":true}).to_string();
    audit.execute(
        "INSERT INTO mimir_operation_step_replies(operation_token,step,reply) VALUES($1,$2,$3::text::jsonb)",
        &[&token, &step.id(), &answer],
    ).await?;
    // Deliberately inconsistent legacy journal, confined to this test's token.
    // Existing immutable receipts and their protection are left intact.
    let original = service.read_operation_step(token, step.id()).await?;
    let before = mimir_json::to_value(store.get_pattern(id).await?)?;
    assert!(matches!(
        service.delete_pattern_operation(&step).await?,
        StepDecision::NeedsRecovery(_)
    ));
    assert_eq!(mimir_json::to_value(store.get_pattern(id).await?)?, before);
    assert_eq!(
        service.read_operation_step(token, step.id()).await?,
        original
    );
    assert!(service
        .read_operation_step(token, "@operation-result")
        .await?
        .is_none());
    store.delete_pattern(id).await?;
    Ok(())
}

#[tokio::test]
async fn missing_step_answer_requires_recovery_before_any_business_change() -> Result<()> {
    let (store, service) = setup().await?;
    let id = identity().await?;
    pattern(&store, id).await?;
    let (token, step) = admitted(&service, "delete_pattern", json!({"id":id})).await?;
    let audit = db::connect(&config().database).await?;
    let answer = json!({"deleted":true}).to_string();
    audit
        .execute(
            "INSERT INTO mimir_operation_step_replies(operation_token,step,reply) VALUES($1,'@operation-result',$2::text::jsonb)",
            &[&token, &answer],
        )
        .await?;
    let before = mimir_json::to_value(store.get_pattern(id).await?)?;
    assert!(matches!(
        service.delete_pattern_operation(&step).await?,
        StepDecision::NeedsRecovery(_)
    ));
    assert_eq!(mimir_json::to_value(store.get_pattern(id).await?)?, before);
    assert!(service
        .read_operation_step(token, step.id())
        .await?
        .is_none());
    assert_eq!(
        service
            .read_operation_step(token, "@operation-result")
            .await?
            .unwrap()
            .reply,
        json!({"deleted":true})
    );
    store.delete_pattern(id).await?;
    Ok(())
}
