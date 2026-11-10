#[path = "../../../tests/support/assessment_observation.rs"]
mod assessment_observation;
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;

use anyhow::Result;
use mimir_core::db;
use tokio_postgres::IsolationLevel;
use uuid::Uuid;

#[tokio::test]
async fn observes_assessment_payload_and_stored_numbers_separately() -> Result<()> {
    let database = isolation::fixture().database_config();
    let mut client = db::connect(&database).await?;
    let tx = client
        .build_transaction()
        .isolation_level(IsolationLevel::RepeatableRead)
        .start()
        .await?;
    let ids = tx
        .query_one("SELECT gen_random_uuid(), gen_random_uuid()", &[])
        .await?;
    let experience: Uuid = ids.get(0);
    let belief: Uuid = ids.get(1);
    tx.execute("INSERT INTO public.mimir_experiences (id, project, revision) VALUES ($1, 'assessment-test', 1)", &[&experience]).await?;
    tx.execute("INSERT INTO public.mimir_experience_versions (experience_id, revision, payload) VALUES ($1,1,'{}'::jsonb)", &[&experience]).await?;
    tx.execute("INSERT INTO public.mimir_review_versions (experience_id, revision, experience_revision, payload) VALUES ($1,1,1,'{}'::jsonb)", &[&experience]).await?;
    let payload = r#"{"positive":0.125,"extra":"keep"}"#;
    tx.execute("INSERT INTO public.mimir_assessment_contributions (experience_id,review_revision,belief_id,scope,rubric,positive,negative,benefit,benefit_weight,payload) VALUES ($1,1,$2,'scope','rubric',0.75,0.125,-0.25,0.5,$3::text::jsonb)", &[&experience,&belief,&payload]).await?;
    let assessments = assessment_observation::observe(&tx).await?;
    let item = assessments
        .iter()
        .find(|row| row.experience == experience && row.belief == belief)
        .expect("assessment missing");
    assert_eq!(
        (
            item.review_revision,
            item.scope.as_str(),
            item.rubric.as_str()
        ),
        (1, "scope", "rubric")
    );
    assert_eq!(
        (
            item.positive,
            item.negative,
            item.benefit,
            item.benefit_weight
        ),
        (0.75, 0.125, -0.25, 0.5)
    );
    assert!(item.payload_json.contains("0.125"));
    assert!(item.payload_json.contains("keep"));
    tx.rollback().await?;
    Ok(())
}
