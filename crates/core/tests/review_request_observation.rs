#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;
#[path = "../../../tests/support/review_request_observation.rs"]
mod review_request_observation;

use anyhow::Result;
use mimir_core::db;
use tokio_postgres::IsolationLevel;
use uuid::Uuid;

#[tokio::test]
async fn observes_original_requests_and_older_missing_requests() -> Result<()> {
    let database = isolation::fixture().database_config();
    let mut client = db::connect(&database).await?;
    let tx = client
        .build_transaction()
        .isolation_level(IsolationLevel::RepeatableRead)
        .start()
        .await?;
    let id: Uuid = tx.query_one("SELECT gen_random_uuid()", &[]).await?.get(0);
    tx.execute("INSERT INTO public.mimir_experiences (id, project, revision, review_revision, reviewed_revision) VALUES ($1, 'request-test', 1, 2, 1)", &[&id]).await?;
    tx.execute("INSERT INTO public.mimir_experience_versions (experience_id, revision, payload) VALUES ($1,1,'{}'::jsonb)", &[&id]).await?;
    let request = r#"{"original":"retain this", "number":123456789012345678901234567890123456789}"#;
    tx.execute("INSERT INTO public.mimir_review_versions (experience_id,revision,experience_revision,payload,request) VALUES ($1,1,1,'{}'::jsonb,NULL), ($1,2,1,'{}'::jsonb,$2::text::jsonb)", &[&id,&request]).await?;
    let rows = review_request_observation::observe(&tx).await?;
    let selected: Vec<_> = rows.iter().filter(|row| row.experience == id).collect();
    assert_eq!(selected.len(), 2);
    assert_eq!(selected[0].revision, 1);
    assert_eq!(selected[0].request_json, None);
    assert_eq!(selected[1].revision, 2);
    let saved = selected[1]
        .request_json
        .as_deref()
        .expect("saved request missing");
    assert!(saved.contains("retain this"));
    assert!(saved.contains("123456789012345678901234567890123456789"));
    tx.rollback().await?;
    Ok(())
}
