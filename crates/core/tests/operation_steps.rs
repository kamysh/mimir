//! Real business changes and saved answers in the maintained disposable fixture.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;
use anyhow::{Context, Result};
use mimir_core::{config::Config, db, learning::*, store::*, MimirService};
use serde_json::{json, Value};
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Arc,
};
use tokio_postgres::Transaction;
use uuid::Uuid;

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

async fn prepared() -> Result<(
    MimirService,
    Config,
    Uuid,
    Uuid,
    OperationBindingRequest,
    OperationPlan,
    RegisteredStep,
)> {
    let cfg = config();
    let service = MimirService::connect(&cfg).await?;
    let client = db::connect(&cfg.database).await?;
    let id: Uuid = client
        .query_one("SELECT gen_random_uuid()", &[])
        .await?
        .get(0);
    let project = format!("atomic-step-{id}");
    service
        .record_experience(
            &Experience {
                id,
                project: project.clone(),
                context: "private saved-step fixture".into(),
                action: "verify atomic publication".into(),
                outcome: Outcome::Success,
                source: ObservationSource::ToolResult,
                evidence: vec!["owned PostgreSQL fixture receipt".into()],
                belief_ids: vec![],
                pattern_id: None,
                learning_items: vec![],
                source_records: vec![],
            },
            0,
        )
        .await?;
    let token = service
        .reserve_operation(&request_key().await?)
        .await?
        .operation_token;
    let request = OperationBindingRequest::new(
        "delete_project".into(),
        json!({"project":project}),
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
    let mut steps = plan.steps();
    let last = steps.pop().context("deletion plan is empty")?;
    // This fixture has only a learning row. Earlier graph tables are empty.
    for step in steps {
        assert!(matches!(
            service
                .commit_operation_step(&step, |_, _| Box::pin(async { Ok(Value::Null) }))
                .await?,
            StepDecision::Done(_)
        ));
    }
    Ok((service, cfg, token, id, request, plan, last))
}

fn erase<'a, 'client>(
    tx: &'a Transaction<'client>,
    original: &'a OperationBindingRequest,
) -> FinalStepWork<'a> {
    Box::pin(async move {
        let project = original
            .arguments()
            .get("project")
            .and_then(Value::as_str)
            .context("missing admitted project")?;
        let rows = tx
            .query(
                "DELETE FROM mimir_experiences WHERE project=$1 RETURNING id",
                &[&project],
            )
            .await?;
        let removed = rows
            .iter()
            .map(|row| row.get::<_, Uuid>(0).to_string())
            .collect::<Vec<_>>();
        let reply = json!({"removed":removed});
        Ok((reply.clone(), reply))
    })
}

#[tokio::test]
async fn competing_callers_publish_once_and_keep_the_original_answer() -> Result<()> {
    let (first, cfg, token, id, request, _plan, step) = prepared().await?;
    let second = MimirService::connect(&cfg).await?;
    let unbound = first
        .reserve_operation(&request_key().await?)
        .await?
        .operation_token;
    assert!(matches!(
        first
            .prepare_operation(unbound, &request, |_, _| Box::pin(async {
                panic!("unbound request executed")
            }))
            .await?,
        PlanDecision::UnknownBinding
    ));
    let calls = Arc::new(AtomicUsize::new(0));
    let a = calls.clone();
    let b = calls.clone();
    let (one, two) = tokio::join!(
        first.commit_final_operation_step(&step, move |tx, original| {
            a.fetch_add(1, Ordering::SeqCst);
            erase(tx, original)
        }),
        second.commit_final_operation_step(&step, move |tx, original| {
            b.fetch_add(1, Ordering::SeqCst);
            erase(tx, original)
        }),
    );
    assert_eq!(one.as_ref().unwrap(), two.as_ref().unwrap());
    let StepDecision::Done(saved) = one? else {
        panic!("expected a saved answer");
    };
    assert_eq!(saved.reply, json!({"removed":[id.to_string()]}));
    assert_eq!(calls.load(Ordering::SeqCst), 1);
    assert_eq!(
        second.read_operation_step(token, step.id()).await?,
        Some(saved.clone())
    );
    drop(first);
    let reopened = MimirService::connect(&cfg).await?;
    assert_eq!(
        reopened
            .commit_final_operation_step(&step, |_, _| Box::pin(async {
                panic!("saved step ran again")
            }))
            .await?,
        StepDecision::Done(saved)
    );
    // Even a saved answer cannot make a changed request look successful.
    let changed = OperationBindingRequest::new(
        "delete_project".into(),
        json!({"project":"different"}),
        json!({}),
    )?;
    assert!(matches!(
        reopened
            .prepare_operation(token, &changed, |_, _| Box::pin(async {
                panic!("changed request executed")
            }))
            .await?,
        PlanDecision::ChangedRequest(_)
    ));
    Ok(())
}

#[tokio::test]
async fn failing_to_save_an_answer_rolls_back_the_real_business_change() -> Result<()> {
    let (service, cfg, token, id, _request, _plan, step) = prepared().await?;
    let result = service.commit_final_operation_step(&step, move |tx, original| Box::pin(async move {
        let reply = erase(tx, original).await?;
        // The injected constraint and deletion belong to the SAME transaction.
        // A failed reply insert rolls both back, leaving no fixture-wide guard.
        tx.batch_execute(&format!("ALTER TABLE mimir_operation_step_replies ADD CONSTRAINT mimir_test_reject_reply CHECK (operation_token <> '{token}'::uuid) NOT VALID")).await?;
        Ok(reply)
    })).await;
    assert!(result.is_err());
    assert!(service
        .read_operation_step(token, step.id())
        .await?
        .is_none());
    let audit = db::connect(&cfg.database).await?;
    assert!(audit
        .query_opt("SELECT id FROM mimir_experiences WHERE id=$1", &[&id])
        .await?
        .is_some());
    assert!(audit
        .query_opt(
            "SELECT 1 FROM pg_constraint WHERE conname='mimir_test_reject_reply'",
            &[]
        )
        .await?
        .is_none());
    let retried = service.commit_final_operation_step(&step, erase).await?;
    let StepDecision::Done(saved) = retried else {
        panic!("corrected step did not complete");
    };
    assert_eq!(saved.reply, json!({"removed":[id.to_string()]}));
    assert!(audit
        .query_opt("SELECT id FROM mimir_experiences WHERE id=$1", &[&id])
        .await?
        .is_none());
    Ok(())
}

#[tokio::test]
async fn interrupted_connection_before_publication_leaves_no_partial_step() -> Result<()> {
    let (service, cfg, token, id, _request, _plan, step) = prepared().await?;
    let service = Arc::new(service);
    let owner = service.clone();
    let owned_step = step.clone();
    let (reached, at_boundary) = tokio::sync::oneshot::channel();
    let (resume, released) = tokio::sync::oneshot::channel();
    let work = tokio::spawn(async move {
        owner
            .commit_final_operation_step(&owned_step, move |tx, original| {
                Box::pin(async move {
                    let reply = erase(tx, original).await?;
                    let pid: i32 = tx.query_one("SELECT pg_backend_pid()", &[]).await?.get(0);
                    reached
                        .send(pid)
                        .map_err(|_| anyhow::anyhow!("boundary receiver closed"))?;
                    released.await?;
                    Ok(reply)
                })
            })
            .await
    });
    let pid = at_boundary.await?;
    let audit = db::connect(&cfg.database).await?;
    let stopped: bool = audit
        .query_one("SELECT pg_terminate_backend($1)", &[&pid])
        .await?
        .get(0);
    assert!(stopped);
    resume
        .send(())
        .map_err(|_| anyhow::anyhow!("step task already stopped"))?;
    assert!(work.await?.is_err());
    let reopened = MimirService::connect(&cfg).await?;
    assert!(reopened
        .read_operation_step(token, step.id())
        .await?
        .is_none());
    assert!(audit
        .query_opt("SELECT id FROM mimir_experiences WHERE id=$1", &[&id])
        .await?
        .is_some());
    let StepDecision::Done(saved) = reopened.commit_final_operation_step(&step, erase).await?
    else {
        panic!("retry failed");
    };
    assert_eq!(saved.reply, json!({"removed":[id.to_string()]}));
    Ok(())
}

#[tokio::test]
async fn final_answer_failure_rolls_back_business_and_both_answers() -> Result<()> {
    let (service, cfg, token, id, request, _plan, step) = prepared().await?;
    assert!(matches!(
        service
            .read_operation_outcome(token, Some(&request))
            .await?,
        OperationOutcome::Pending { .. }
    ));
    let result=service.commit_final_operation_step(&step,move|tx,original|Box::pin(async move {
        let replies=erase(tx,original).await?;
        // Reject ONLY the operation answer: its step answer was already saved
        // in this transaction. All three publications must still roll back.
        tx.batch_execute(&format!("ALTER TABLE mimir_operation_step_replies ADD CONSTRAINT mimir_test_reject_final CHECK (operation_token <> '{token}'::uuid OR step <> '@operation-result') NOT VALID")).await?;
        Ok(replies)
    })).await;
    assert!(result.is_err());
    assert!(service
        .read_operation_step(token, step.id())
        .await?
        .is_none());
    let audit = db::connect(&cfg.database).await?;
    assert!(audit
        .query_opt("SELECT 1 FROM mimir_experiences WHERE id=$1", &[&id])
        .await?
        .is_some());
    assert!(matches!(
        service.read_operation_outcome(token, None).await?,
        OperationOutcome::Pending { .. }
    ));
    service.commit_final_operation_step(&step, erase).await?;
    drop(service);
    let reopened = MimirService::connect(&cfg).await?;
    let OperationOutcome::Completed { outcome, .. } = reopened
        .read_operation_outcome(token, Some(&request))
        .await?
    else {
        panic!("completed outcome missing")
    };
    assert_eq!(outcome.reply(), &json!({"removed":[id.to_string()]}));
    assert!(audit
        .query_opt("SELECT 1 FROM mimir_experiences WHERE id=$1", &[&id])
        .await?
        .is_none());
    Ok(())
}

#[tokio::test]
async fn readback_distinguishes_reserved_pending_correction_and_completion() -> Result<()> {
    let (service, cfg, token, _id, request, plan, step) = prepared().await?;
    let audit = db::connect(&cfg.database).await?;
    let unknown: Uuid = audit
        .query_one("SELECT gen_random_uuid()", &[])
        .await?
        .get(0);
    assert!(matches!(
        service.read_operation_outcome(unknown, None).await?,
        OperationOutcome::UnknownToken
    ));
    let reserved = service
        .reserve_operation(&request_key().await?)
        .await?
        .operation_token;
    assert!(matches!(
        service.read_operation_outcome(reserved, None).await?,
        OperationOutcome::Reserved
    ));
    service.bind_operation_request(reserved, &request).await?;
    assert!(matches!(
        service.read_operation_outcome(reserved, None).await?,
        OperationOutcome::AwaitingPlan(_)
    ));
    let OperationOutcome::Pending {
        next_step,
        saved_replies,
        ..
    } = service.read_operation_outcome(token, None).await?
    else {
        panic!("pending work missing")
    };
    assert_eq!(&next_step, step.description());
    assert_eq!(saved_replies.len() + 1, plan.steps().len());
    assert!(matches!(
        service
            .commit_operation_step(&step, |_, _| Box::pin(async {
                panic!("final change ran without its result")
            }))
            .await?,
        StepDecision::WrongCompletion {
            requires_final_result: true,
            ..
        }
    ));
    let changed = OperationBindingRequest::new(
        "delete_project".into(),
        json!({"project":"different"}),
        json!({}),
    )?;
    assert!(matches!(
        service
            .read_operation_outcome(token, Some(&changed))
            .await?,
        OperationOutcome::ChangedRequest(_)
    ));
    service.commit_final_operation_step(&step, erase).await?;
    assert!(matches!(
        service
            .read_operation_outcome(token, Some(&changed))
            .await?,
        OperationOutcome::ChangedRequest(_)
    ));
    assert!(matches!(
        service
            .read_operation_outcome(token, Some(&request))
            .await?,
        OperationOutcome::Completed { .. }
    ));
    Ok(())
}
