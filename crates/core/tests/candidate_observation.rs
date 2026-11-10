#[path = "../../../tests/support/candidate_observation.rs"]
mod candidate_observation;
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;

use anyhow::Result;
use mimir_core::db;
use tokio_postgres::IsolationLevel;
use uuid::Uuid;

#[tokio::test]
async fn observes_active_and_retired_candidates_with_no_nodes() -> Result<()> {
    let database = isolation::fixture().database_config();
    let mut client = db::connect(&database).await?;
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
    let active: Uuid = ids.get(1);
    let retired: Uuid = ids.get(2);
    tx.execute("INSERT INTO public.mimir_experiences (id, project, revision) VALUES ($1, 'candidate-test', 1)", &[&experience]).await?;
    let active_json = r#"{"kind":"belief","content":"original candidate"}"#;
    let retired_json = r#"{"kind":"pattern","extra":"keep original"}"#;
    tx.execute("INSERT INTO public.mimir_review_candidates (experience_id,candidate_key,kind,node_id,declaration,retired) VALUES ($1,'active','belief',$2,$4::text::jsonb,false), ($1,'retired','pattern',$3,$5::text::jsonb,true)", &[&experience, &active, &retired, &active_json, &retired_json]).await?;
    let rows = candidate_observation::observe(&tx).await?;
    let first = rows
        .iter()
        .find(|row| row.node == active)
        .expect("active candidate missing");
    assert_eq!(
        (
            first.experience,
            first.key.as_str(),
            first.kind.as_str(),
            first.retired
        ),
        (experience, "active", "belief", false)
    );
    assert!(first.declaration_json.contains("original candidate"));
    let second = rows
        .iter()
        .find(|row| row.node == retired)
        .expect("retired candidate missing");
    assert_eq!(
        (
            second.experience,
            second.key.as_str(),
            second.kind.as_str(),
            second.retired
        ),
        (experience, "retired", "pattern", true)
    );
    assert!(second.declaration_json.contains("keep original"));
    tx.rollback().await?;
    Ok(())
}
