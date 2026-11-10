#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;
#[path = "../../../tests/support/operation_observation.rs"]
mod operation_observation;

use anyhow::Result;
use mimir_core::db;
use tokio_postgres::IsolationLevel;
use uuid::Uuid;

#[tokio::test]
async fn observes_pending_finished_and_cancelled_records() -> Result<()> {
    let database = isolation::fixture().database_config();
    let mut client = db::connect(&database).await?;
    let tx = client
        .build_transaction()
        .isolation_level(IsolationLevel::RepeatableRead)
        .start()
        .await?;
    let mut tokens = Vec::<Uuid>::new();
    for _ in 0..3 {
        tokens.push(tx.query_one("INSERT INTO public.mimir_operation_reservations DEFAULT VALUES RETURNING operation_token", &[]).await?.get(0));
    }
    let [pending, finished, cancelled]: [Uuid; 3] = tokens.try_into().unwrap();
    let key = format!("observation-{pending}");
    tx.execute("INSERT INTO public.mimir_operation_request_keys(request_key,operation_token) VALUES($1,$2)", &[&key,&pending]).await?;
    for token in [pending, finished] {
        tx.execute("INSERT INTO public.mimir_operation_bindings(operation_token,operation,arguments,settings) VALUES($1,'observation','{}'::jsonb,'{}'::jsonb)", &[&token]).await?;
    }
    tx.execute("INSERT INTO public.mimir_operation_plans(operation_token,plan) VALUES($1,'{\"step\":\"original\"}'::jsonb)", &[&pending]).await?;
    tx.execute("INSERT INTO public.mimir_operation_step_replies(operation_token,step,reply) VALUES ($1,'@operation-result','{\"result\":\"finished\"}'::jsonb)", &[&finished]).await?;
    let execution: Uuid = tx.query_one("INSERT INTO public.mimir_operation_executions(operation_token,owner_program,owner_pid,owner_host,owner_host_source) VALUES($1,'test-worker',123,'test-host','fixture') RETURNING execution_id", &[&cancelled]).await?.get(0);
    let owner: Uuid = tx.query_one("INSERT INTO public.mimir_embedding_owners(project,operation_token) VALUES ('test-project',$1) RETURNING owner_token", &[&pending]).await?.get(0);
    tx.execute(
        "INSERT INTO public.mimir_operation_cancellations(operation_token) VALUES($1)",
        &[&cancelled],
    )
    .await?;
    let observed = operation_observation::observe(&tx).await?;
    for token in [pending, finished, cancelled] {
        assert!(observed.reservations.iter().any(|row| row.token == token));
    }
    assert!(observed
        .request_keys
        .iter()
        .any(|row| row.key == key && row.token == pending));
    assert!(observed
        .bindings
        .iter()
        .any(|row| row.token == pending && row.operation == "observation"));
    assert!(observed
        .plans
        .iter()
        .any(|row| row.token == pending && row.plan_json.contains("original")));
    assert!(observed
        .replies
        .iter()
        .any(|row| row.token == finished && row.reply_json.contains("finished")));
    assert!(!observed.replies.iter().any(|row| row.token == pending));
    assert!(observed
        .cancellations
        .iter()
        .any(|row| row.token == cancelled));
    assert!(observed
        .executions
        .iter()
        .any(|row| row.identity == execution
            && row.token == cancelled
            && row.stopped_at.is_none()
            && row.host.as_deref() == Some("test-host")));
    assert!(observed
        .embedding_owners
        .iter()
        .any(|row| row.token == owner && row.operation_token == Some(pending)));
    tx.rollback().await?;
    Ok(())
}
