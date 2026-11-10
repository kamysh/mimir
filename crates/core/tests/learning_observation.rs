#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;
#[allow(dead_code)]
#[path = "../../../tests/support/learning_observation.rs"]
mod learning_observation;

use anyhow::Result;
use mimir_core::db;
use tokio_postgres::IsolationLevel;
use uuid::Uuid;

#[tokio::test]
async fn combines_learning_records_from_one_view() -> Result<()> {
    let database = isolation::fixture().database_config();
    let mut client = db::connect(&database).await?;
    let weak = client.transaction().await?;
    assert!(learning_observation::observe(&weak).await.is_err());
    weak.rollback().await?;
    let tx = client
        .build_transaction()
        .isolation_level(IsolationLevel::RepeatableRead)
        .start()
        .await?;
    let ids = tx
        .query_one(
            "SELECT gen_random_uuid(), gen_random_uuid(), gen_random_uuid()",
            &[],
        )
        .await?;
    let experience: Uuid = ids.get(0);
    let item: Uuid = ids.get(1);
    let belief: Uuid = ids.get(2);
    tx.execute("INSERT INTO public.mimir_experiences (id,project,revision,review_revision,reviewed_revision) VALUES ($1,'learning-test',1,1,1)", &[&experience]).await?;
    tx.execute("INSERT INTO public.mimir_experience_versions (experience_id,revision,payload) VALUES ($1,1,'{\"source\":true}'::jsonb)", &[&experience]).await?;
    tx.execute("INSERT INTO public.mimir_review_versions (experience_id,revision,experience_revision,payload,request) VALUES ($1,1,1,'{\"review\":true}'::jsonb,'{\"original\":true}'::jsonb)", &[&experience]).await?;
    tx.execute("INSERT INTO public.mimir_learning_item_owners (item_id,experience_id,source_ref,actor,item_key) VALUES ($1,$2,'source','agent','key')", &[&item,&experience]).await?;
    tx.execute("INSERT INTO public.mimir_review_candidates (experience_id,candidate_key,kind,node_id,declaration,retired) VALUES ($1,'candidate','belief',$2,'{\"content\":\"candidate\"}'::jsonb,false)", &[&experience,&belief]).await?;
    tx.execute("INSERT INTO public.mimir_assessment_contributions (experience_id,review_revision,belief_id,scope,rubric,positive,negative,benefit,benefit_weight,payload) VALUES ($1,1,$2,'scope','rubric',0.5,0.25,0.0,0.5,'{}'::jsonb)", &[&experience,&belief]).await?;
    let observed = learning_observation::observe(&tx).await?;
    assert!(observed
        .history
        .heads
        .iter()
        .any(|row| row.identity == experience));
    assert!(observed
        .history
        .source_rows
        .iter()
        .any(|row| row.experience == experience));
    assert!(observed
        .history
        .review_rows
        .iter()
        .any(|row| row.experience == experience));
    assert!(observed
        .owners
        .iter()
        .any(|row| row.identity == item && row.experience == experience));
    assert!(observed
        .candidates
        .iter()
        .any(|row| row.node == belief && row.experience == experience));
    assert!(observed
        .assessments
        .iter()
        .any(|row| row.belief == belief && row.experience == experience));
    assert!(observed
        .requests
        .iter()
        .any(|row| row.experience == experience && row.request_json.is_some()));
    tx.rollback().await?;
    Ok(())
}
