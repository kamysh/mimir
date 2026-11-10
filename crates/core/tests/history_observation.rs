#[path = "../../../tests/support/history_observation.rs"]
mod history_observation;
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;

use anyhow::Result;
use mimir_core::db;
use tokio_postgres::IsolationLevel;
use uuid::Uuid;

#[tokio::test]
async fn observes_old_history_and_exact_stored_numbers() -> Result<()> {
    let database = isolation::fixture().database_config();
    let mut client = db::connect(&database).await?;
    let tx = client
        .build_transaction()
        .isolation_level(IsolationLevel::RepeatableRead)
        .start()
        .await?;
    let id: Uuid = tx.query_one("SELECT gen_random_uuid()", &[]).await?.get(0);
    tx.execute("INSERT INTO public.mimir_experiences (id, project, revision, review_revision, reviewed_revision, updated_at) VALUES ($1, 'history-test', 2, 1, 1, '2026-01-04T00:00:00Z')", &[&id]).await?;
    let legacy =
        r#"{"legacy_only": ["old", null], "large": 123456789012345678901234567890123456789}"#;
    let latest = r#"{"current": true}"#;
    let review = r#"{"old_review_shape": {"note": "preserve me"}}"#;
    tx.execute("INSERT INTO public.mimir_experience_versions (experience_id, revision, payload) VALUES ($1, 1, $2::text::jsonb), ($1, 2, $3::text::jsonb)", &[&id, &legacy, &latest]).await?;
    tx.execute("INSERT INTO public.mimir_review_versions (experience_id, revision, experience_revision, payload) VALUES ($1, 1, 1, $2::text::jsonb)", &[&id, &review]).await?;
    let history = history_observation::observe(&tx).await?;
    let head = history
        .heads
        .iter()
        .find(|row| row.identity == id)
        .expect("head missing");
    assert_eq!(
        (
            head.project.as_str(),
            head.revision,
            head.review_revision,
            head.reviewed_revision
        ),
        ("history-test", 2, 1, 1)
    );
    assert_eq!(head.updated_at.to_rfc3339(), "2026-01-04T00:00:00+00:00");
    let sources: Vec<_> = history
        .source_rows
        .iter()
        .filter(|row| row.experience == id)
        .collect();
    assert_eq!(sources.len(), 2);
    assert_eq!((sources[0].revision, sources[0].source_revision), (1, 1));
    assert!(sources[0]
        .payload_json
        .contains("123456789012345678901234567890123456789"));
    assert!(sources[0].payload_json.contains("legacy_only"));
    assert_eq!((sources[1].revision, sources[1].source_revision), (2, 2));
    let reviews: Vec<_> = history
        .review_rows
        .iter()
        .filter(|row| row.experience == id)
        .collect();
    assert_eq!(reviews.len(), 1);
    assert_eq!((reviews[0].revision, reviews[0].source_revision), (1, 1));
    assert!(reviews[0].payload_json.contains("old_review_shape"));
    tx.rollback().await?;
    Ok(())
}
