//! Admission and replay against the maintained owned PostgreSQL fixture.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;
use anyhow::Result;
use mimir_core::{config::Config, db, operation_catalogue::CommitSite, store::*, MimirService};
use serde_json::{json, Value};

async fn request_key() -> Result<String> {
    let client = db::connect(&config().database).await?;
    Ok(client
        .query_one("SELECT gen_random_uuid()::text", &[])
        .await?
        .get(0))
}

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

async fn bound(name: &str) -> Result<(MimirService, OperationBindingRequest, uuid::Uuid)> {
    let service = MimirService::connect(&config()).await?;
    let token = service
        .reserve_operation(&request_key().await?)
        .await?
        .operation_token;
    let request =
        OperationBindingRequest::new(name.into(), json!({"project":token.to_string()}), json!({}))?;
    assert!(matches!(
        service.bind_operation_request(token, &request).await?,
        OperationBindingDecision::Bound(_)
    ));
    Ok((service, request, token))
}

#[tokio::test]
async fn a_different_operations_plan_cannot_be_read_or_prepared_as_this_operation() -> Result<()> {
    let (service, request, token) = bound("get_belief").await?;
    let answer = json!({"original_read_result": true});
    let client = db::connect(&config().database).await?;
    // Model one pre-existing inconsistent journal with initial owned rows.
    // Plans remain immutable: neither setup nor checks disable that protection.
    let changed = json!({"operation":"list_beliefs","shape":[],"steps":[]}).to_string();
    assert_eq!(
        client
            .execute(
                "INSERT INTO mimir_operation_plans(operation_token,plan) VALUES($1,$2::text::jsonb)",
                &[&token, &changed],
            )
            .await?,
        1
    );
    client.execute(
        "INSERT INTO mimir_operation_step_replies(operation_token,step,reply) VALUES($1,'@operation-result',$2::text::jsonb)",
        &[&token, &answer.to_string()],
    ).await?;
    async fn journal(client: &tokio_postgres::Client, token: uuid::Uuid) -> Result<String> {
        Ok(client.query_one(
            "SELECT jsonb_build_object('reservation',(SELECT to_jsonb(r) FROM mimir_operation_reservations r WHERE operation_token=$1),'request_keys',(SELECT jsonb_agg(to_jsonb(k) ORDER BY request_key) FROM mimir_operation_request_keys k WHERE operation_token=$1),'binding',(SELECT to_jsonb(b) FROM mimir_operation_bindings b WHERE operation_token=$1),'plan',(SELECT to_jsonb(p) FROM mimir_operation_plans p WHERE operation_token=$1),'replies',(SELECT jsonb_agg(to_jsonb(s) ORDER BY step) FROM mimir_operation_step_replies s WHERE operation_token=$1),'cancellation',(SELECT to_jsonb(c) FROM mimir_operation_cancellations c WHERE operation_token=$1))::text",
            &[&token],
        ).await?.get(0))
    }
    let before = journal(&client, token).await?;
    let observed = service.read_operation_outcome(token, None).await?;
    let prepared = service
        .prepare_operation(token, &request, |_, _| {
            Box::pin(async { panic!("an existing inconsistent plan must never run selection") })
        })
        .await?;
    let after = journal(&client, token).await?;
    let OperationOutcome::NeedsRecovery { binding, reason } = observed else {
        panic!("a different operation's plan was accepted as a completed original")
    };
    assert_eq!(binding.request, request);
    assert!(!reason.is_empty());
    let PlanDecision::NeedsRecovery(reason) = prepared else {
        panic!("a different operation's saved plan was prepared for execution")
    };
    assert!(!reason.is_empty());
    assert_eq!(
        after, before,
        "inspection must preserve the complete journal"
    );
    assert_eq!(
        service
            .read_operation_step(token, "@operation-result")
            .await?
            .expect("the original saved answer must remain inspectable")
            .reply,
        answer
    );
    Ok(())
}

#[tokio::test]
async fn wrong_order_never_runs_work_and_completion_requires_all_steps() -> Result<()> {
    let (service, request, token) = bound("record_defeat").await?;
    let PlanDecision::Ready(plan) = service
        .prepare_operation(token, &request, |_, _| Box::pin(async { Ok(vec![]) }))
        .await?
    else {
        panic!("plan missing")
    };
    let steps = plan.steps();
    assert!(steps.len() > 1);
    let StepDecision::OutOfOrder(next) = service
        .commit_operation_step(&steps[1], |_, _| {
            Box::pin(async { panic!("wrong step executed") })
        })
        .await?
    else {
        panic!("wrong order admitted")
    };
    assert_eq!(next, steps[0].description().clone());
    assert!(matches!(
        service
            .complete_operation(&plan, json!({"done":true}))
            .await?,
        CompletionDecision::Incomplete(_)
    ));
    for step in &steps[..steps.len() - 1] {
        assert!(matches!(
            service
                .commit_operation_step(step, |_, _| Box::pin(async { Ok(Value::Null) }))
                .await?,
            StepDecision::Done(_)
        ));
    }
    assert!(matches!(
        service
            .commit_final_operation_step(steps.last().unwrap(), |_, _| Box::pin(async {
                Ok((Value::Null, json!({"done":true})))
            }))
            .await?,
        StepDecision::Done(_)
    ));
    let CompletionDecision::Done(first) = service
        .complete_operation(&plan, json!({"done":true}))
        .await?
    else {
        panic!("completion missing")
    };
    let CompletionDecision::Done(again) = service
        .complete_operation(&plan, json!({"done":false}))
        .await?
    else {
        panic!("completion missing")
    };
    assert_eq!(first.reply(), again.reply());
    assert_eq!(first.reply(), &json!({"done":true}));
    let StepDecision::Done(saved) = service
        .commit_operation_step(&steps[0], |_, _| {
            Box::pin(async { panic!("completed step repeated") })
        })
        .await?
    else {
        panic!("saved answer missing")
    };
    assert_eq!(saved.reply, Value::Null);
    Ok(())
}

#[tokio::test]
async fn a_saved_selection_is_reused_after_database_changes_and_reconnect() -> Result<()> {
    let (service, request, token) = bound("sweep_expired_defeated").await?;
    // Select actual reserved rows as logical item keys. This test exercises
    // selection stability; it does not invoke the sweep's business deletion.
    let own = token;
    let PlanDecision::Ready(plan)=service.prepare_operation(token,&request,move|tx,_|Box::pin(async move {
        let row=tx.query_one("SELECT operation_token::text FROM mimir_operation_reservations WHERE operation_token=$1",&[&own]).await?;
        Ok(vec![(CommitSite::BeliefDeletion,vec![row.get(0)])])
    })).await? else {panic!("plan missing")};
    service.reserve_operation(&request_key().await?).await?;
    drop(service);
    let reopened = MimirService::connect(&config()).await?;
    let PlanDecision::Ready(again) = reopened
        .prepare_operation(token, &request, |_, _| {
            Box::pin(async { panic!("saved selection was recalculated") })
        })
        .await?
    else {
        panic!("plan missing")
    };
    let descriptions = |p: &OperationPlan| {
        p.steps()
            .iter()
            .map(|s| s.description().clone())
            .collect::<Vec<_>>()
    };
    assert_eq!(descriptions(&plan), descriptions(&again));
    assert_eq!(
        again.steps()[0].description().key.as_deref(),
        Some(token.to_string().as_str())
    );
    let audit = db::connect(&config().database).await?;
    assert!(audit
        .execute(
            "UPDATE mimir_operation_plans SET plan=plan WHERE operation_token=$1",
            &[&token]
        )
        .await
        .is_err());
    assert!(audit
        .execute(
            "DELETE FROM mimir_operation_plans WHERE operation_token=$1",
            &[&token]
        )
        .await
        .is_err());
    Ok(())
}

#[tokio::test]
async fn selection_cannot_write_and_invalid_selection_cannot_publish_a_plan() -> Result<()> {
    let (service, request, token) = bound("sweep_expired_defeated").await?;
    let result = service
        .prepare_operation(token, &request, |tx, _| {
            Box::pin(async move {
                tx.execute("DELETE FROM mimir_operation_reservations WHERE false", &[])
                    .await?;
                Ok(vec![(CommitSite::BeliefDeletion, vec![])])
            })
        })
        .await;
    assert!(result.is_err());
    assert!(service
        .prepare_operation(token, &request, |_, _| Box::pin(async { Ok(vec![]) }))
        .await
        .is_err());
    assert!(service
        .prepare_operation(token, &request, |_, _| Box::pin(async {
            Ok(vec![(
                CommitSite::BeliefDeletion,
                vec!["same".into(), "same".into()],
            )])
        }))
        .await
        .is_err());
    let audit = db::connect(&config().database).await?;
    assert!(audit
        .query_opt(
            "SELECT 1 FROM mimir_operation_plans WHERE operation_token=$1",
            &[&token]
        )
        .await?
        .is_none());
    let PlanDecision::Ready(empty) = service
        .prepare_operation(token, &request, |_, _| {
            Box::pin(async { Ok(vec![(CommitSite::BeliefDeletion, vec![])]) })
        })
        .await?
    else {
        panic!("explicit empty selection rejected")
    };
    assert!(empty.steps().is_empty());
    assert!(matches!(
        service
            .complete_operation(&empty, json!({"removed":[]}))
            .await?,
        CompletionDecision::Done(_)
    ));
    Ok(())
}
