//! Replaying a direct graph token returns the original complete publication.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;
use anyhow::{ensure, Result};
use mimir_core::{
    config::Config, db, graph::Belief, interaction::RequestCorrection, store::*, MimirService,
};
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
    Ok((
        AgeStore::new(
            db::connect(&cfg.database).await?,
            cfg.database.dbname.clone(),
        )?,
        MimirService::connect(&cfg).await?,
    ))
}
struct Prepared {
    token: Uuid,
    step: RegisteredStep,
}
async fn plan(
    service: &MimirService,
    operation: &str,
    arguments: Value,
    settings: Value,
) -> Result<Prepared> {
    let token = service
        .reserve_operation(&identity().await?.to_string())
        .await?
        .operation_token;
    let binding = OperationBindingRequest::new(operation.into(), arguments, settings)?;
    service.bind_operation_request(token, &binding).await?;
    let PlanDecision::Ready(plan) = service
        .prepare_operation(token, &binding, |_, _| Box::pin(async { Ok(vec![]) }))
        .await?
    else {
        panic!("missing plan")
    };
    ensure!(plan.steps().len() == 1);
    Ok(Prepared {
        token,
        step: plan.steps()[0].clone(),
    })
}
async fn done(service: &MimirService, step: &Prepared, pattern: bool) -> Result<StepReceipt> {
    let result = if pattern {
        service.create_pattern_operation(&step.step).await?
    } else {
        service.direct_relationship_operation(&step.step).await?
    };
    let StepDecision::Done(receipt) = result else {
        panic!("operation did not complete")
    };
    ensure!(
        service
            .read_operation_step(step.token, step.step.id())
            .await?
            == Some(receipt.clone())
    );
    let final_reply = service
        .read_operation_step(step.token, "@operation-result")
        .await?
        .expect("final answer");
    ensure!(final_reply.reply == receipt.reply);
    Ok(receipt)
}
async fn pending(service: &MimirService, step: &Prepared) -> Result<()> {
    ensure!(service
        .read_operation_step(step.token, step.step.id())
        .await?
        .is_none());
    ensure!(service
        .read_operation_step(step.token, "@operation-result")
        .await?
        .is_none());
    ensure!(matches!(
        service.read_operation_outcome(step.token, None).await?,
        OperationOutcome::Pending { .. }
    ));
    Ok(())
}

#[tokio::test]
async fn pattern_replay_keeps_original_postgres_metadata_and_exact_saved_pattern() -> Result<()> {
    let (store, service) = setup().await?;
    let project = format!("pattern-replay-{}", identity().await?);
    let step = plan(&service, "insert_pattern", json!({"situation":"exact situation", "approach":"exact approach", "success_rate":0.6,"project":project}), json!({})).await?;
    let audit = db::connect(&config().database).await?;
    let suffix = identity().await?.simple().to_string();
    let function = format!("check_registered_pattern_time_{suffix}");
    let graph = config().database.dbname.replace('"', "\"\"");
    audit.batch_execute(&format!(r#"CREATE FUNCTION public.{function}() RETURNS trigger LANGUAGE plpgsql AS $body$
BEGIN
  IF NEW.properties::text::jsonb->>'project' = '{project}' AND
     (NEW.properties::text::jsonb->>'created_at')::timestamptz IS DISTINCT FROM transaction_timestamp()
  THEN RAISE EXCEPTION 'registered pattern did not consume its committing PostgreSQL time'; END IF;
  RETURN NEW;
END $body$;
CREATE TRIGGER {function} BEFORE INSERT ON "{graph}"."Pattern" FOR EACH ROW EXECUTE FUNCTION public.{function}();"#)).await?;
    let attempted = done(&service, &step, true).await;
    audit
        .batch_execute(&format!(
            r#"DROP TRIGGER {function} ON "{graph}"."Pattern"; DROP FUNCTION public.{function}();"#
        ))
        .await?;
    let first = attempted?;
    let pattern: mimir_core::graph::Pattern = serde_json::from_value(first.reply.clone())?;
    ensure!(pattern.project.as_deref() == Some(project.as_str()));
    ensure!(pattern.activation_count == 0);
    let before = serde_json::to_value(store.list_patterns_by_project(&project).await?)?;
    let reopened = MimirService::connect(&config()).await?;
    let replay = done(&reopened, &step, true).await?;
    ensure!(first == replay);
    ensure!(serde_json::to_value(store.list_patterns_by_project(&project).await?)? == before);
    ensure!(
        serde_json::to_value(store.get_pattern(pattern.id).await?)?
            == serde_json::to_value(Some(&pattern))?
    );
    store.delete_project(&project).await?;
    Ok(())
}

#[tokio::test]
async fn direct_relationship_replays_do_not_duplicate_either_contradiction_direction() -> Result<()>
{
    let (store, service) = setup().await?;
    let project = format!("direct-replay-{}", identity().await?);
    let mut a = Belief::new_in_project("first".into(), 0.5, 0.5, project.clone())?;
    let mut b = Belief::new_in_project("second".into(), 0.5, 0.5, project.clone())?;
    a.id = identity().await?;
    b.id = identity().await?;
    store.insert_belief(&a).await?;
    store.insert_belief(&b).await?;
    let beliefs_before = serde_json::to_value(store.list_beliefs_by_project(&project).await?)?;
    for (operation, arguments, expected_edges) in [
        (
            "record_support",
            json!({"from_id":a.id,"to_id":b.id,"weight":0.2}),
            1,
        ),
        (
            "record_cause",
            json!({"from_id":a.id,"to_id":b.id,"weight":0.7}),
            2,
        ),
        ("record_contradiction", json!({"id_a":a.id,"id_b":b.id}), 4),
    ] {
        let step = plan(&service, operation, arguments, json!({})).await?;
        let first = done(&service, &step, false).await?;
        ensure!(first.reply == json!({"ok":true}));
        let before = serde_json::to_value(store.get_edges_among(&[a.id, b.id]).await?)?;
        ensure!(before.as_array().unwrap().len() == expected_edges);
        let reopened = MimirService::connect(&config()).await?;
        ensure!(done(&reopened, &step, false).await? == first);
        ensure!(serde_json::to_value(store.get_edges_among(&[a.id, b.id]).await?)? == before);
        ensure!(
            serde_json::to_value(store.list_beliefs_by_project(&project).await?)? == beliefs_before
        );
    }
    store.delete_project(&project).await?;
    Ok(())
}

#[tokio::test]
async fn malformed_bound_requests_and_missing_endpoints_remain_pending_without_writes() -> Result<()>
{
    let (store, service) = setup().await?;
    let project = format!("direct-refusal-{}", identity().await?);
    let missing = identity().await?;
    let patterns = serde_json::to_value(store.list_patterns().await?)?;
    let edges = store.count_edges().await?;
    for (operation, arguments, settings, is_pattern) in [
        (
            "insert_pattern",
            json!({"situation":"s", "approach":"a", "success_rate":1.1,"project":project}),
            json!({}),
            true,
        ),
        (
            "insert_pattern",
            json!({"situation":"s", "approach":"a", "success_rate":0.5,"project":null}),
            json!({}),
            true,
        ),
        (
            "record_support",
            json!({"from_id":missing,"to_id":missing,"weight":0.5,"extra":true}),
            json!({}),
            false,
        ),
        (
            "record_cause",
            json!({"from_id":missing,"to_id":missing,"weight":0.5}),
            json!({"unknown":true}),
            false,
        ),
        (
            "record_contradiction",
            json!({"id_a":missing,"id_b":missing,"weight":-0.1}),
            json!({}),
            false,
        ),
        (
            "record_support",
            json!({"from_id":missing,"to_id":missing,"weight":0.5}),
            json!({}),
            false,
        ),
    ] {
        let step = plan(&service, operation, arguments, settings).await?;
        let error = if is_pattern {
            service
                .create_pattern_operation(&step.step)
                .await
                .unwrap_err()
        } else {
            service
                .direct_relationship_operation(&step.step)
                .await
                .unwrap_err()
        };
        let correction = error
            .downcast_ref::<RequestCorrection>()
            .expect("typed correction");
        ensure!(!correction.correction().issues().is_empty());
        pending(&service, &step).await?;
        ensure!(serde_json::to_value(store.list_patterns().await?)? == patterns);
        ensure!(store.count_edges().await? == edges);
    }
    Ok(())
}

#[tokio::test]
async fn failure_saving_pattern_reply_rolls_back_pattern_and_both_answers() -> Result<()> {
    let (store, service) = setup().await?;
    let audit = db::connect(&config().database).await?;
    let suffix = identity().await?.simple().to_string();
    let project = format!("pattern-rollback-{suffix}");
    let step = plan(
        &service,
        "insert_pattern",
        json!({"situation":"pending", "approach":"retry", "success_rate":0.5,"project":project}),
        json!({}),
    )
    .await?;
    let function = format!("reject_pattern_reply_{suffix}");
    audit.batch_execute(&format!("CREATE FUNCTION public.{function}() RETURNS trigger LANGUAGE plpgsql AS $body$ BEGIN IF NEW.operation_token = '{}'::uuid THEN RAISE EXCEPTION 'controlled reply failure'; END IF; RETURN NEW; END $body$; CREATE TRIGGER {function} BEFORE INSERT ON public.mimir_operation_step_replies FOR EACH ROW EXECUTE FUNCTION public.{function}();",step.token)).await?;
    let attempted = service.create_pattern_operation(&step.step).await;
    audit.batch_execute(&format!("DROP TRIGGER {function} ON public.mimir_operation_step_replies; DROP FUNCTION public.{function}();")).await?;
    ensure!(attempted.is_err());
    pending(&service, &step).await?;
    ensure!(store.list_patterns_by_project(&project).await?.is_empty());
    done(&service, &step, true).await?;
    ensure!(store.list_patterns_by_project(&project).await?.len() == 1);
    store.delete_project(&project).await?;
    Ok(())
}
