//! A result prepared before deletion must not recreate an orphaned vector.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;

use anyhow::Result;
use mimir_core::{
    config::Config,
    db,
    graph::Belief,
    store::{AgeStore, BeliefEmbeddingTargetMissing},
    MimirService,
};
use tokio::sync::oneshot;
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

async fn store(cfg: &Config) -> Result<AgeStore> {
    AgeStore::new(
        db::connect(&cfg.database).await?,
        cfg.database.dbname.clone(),
    )
}

async fn belief(cfg: &Config, store: &AgeStore, purpose: &str) -> Result<Belief> {
    let id: Uuid = db::connect(&cfg.database)
        .await?
        .query_one("SELECT gen_random_uuid()", &[])
        .await?
        .get(0);
    let mut belief = Belief::new_in_project(
        purpose.into(),
        0.7,
        0.5,
        format!("embedding-publication-{id}"),
    )?;
    belief.id = id;
    store.insert_belief(&belief).await?;
    Ok(belief)
}

#[tokio::test]
async fn late_vectors_cannot_outlive_belief_or_project_deletion() -> Result<()> {
    let cfg = config();
    let _service = MimirService::connect(&cfg).await?;
    let writer = store(&cfg).await?;
    let observer = db::connect(&cfg.database).await?;
    let survivor = belief(&cfg, &writer, "unrelated owner remains valid").await?;
    writer
        .insert_belief_embedding(survivor.id, &[0.2, 0.3, 0.4])
        .await?;

    let mut outcomes = Vec::new();
    for delete_project in [false, true] {
        let target = belief(&cfg, &writer, "embedding completed after deletion").await?;
        let late_writer = store(&cfg).await?;
        let (ready, after_deletion) = oneshot::channel();
        let id = target.id;
        let late = tokio::spawn(async move {
            after_deletion.await?;
            late_writer
                .insert_belief_embedding(id, &[0.8, 0.1, 0.1])
                .await
        });
        if delete_project {
            assert_eq!(
                writer
                    .delete_project(target.project.as_deref().unwrap())
                    .await?,
                1
            );
        } else {
            assert!(writer.delete_belief(target.id).await?);
        }
        ready.send(()).unwrap();
        let result = late.await?;
        let count: i64 = observer
            .query_one(
                "SELECT count(*) FROM public.belief_embeddings WHERE belief_id=$1",
                &[&target.id],
            )
            .await?
            .get(0);
        // Also clean the original buggy result when running the regression
        // against the old implementation in this owned disposable database.
        writer.delete_belief_embeddings(&[target.id]).await?;
        assert!(writer.get_belief(target.id).await?.is_none());
        outcomes.push((
            result
                .as_ref()
                .err()
                .is_some_and(|error| error.is::<BeliefEmbeddingTargetMissing>()),
            count,
        ));
    }

    writer
        .insert_belief_embedding(survivor.id, &[0.4, 0.3, 0.2])
        .await?;
    let vector: pgvector::Vector = observer
        .query_one(
            "SELECT embedding FROM public.belief_embeddings WHERE belief_id=$1",
            &[&survivor.id],
        )
        .await?
        .get(0);
    writer
        .delete_project(survivor.project.as_deref().unwrap())
        .await?;
    assert_eq!(vector.to_vec(), vec![0.4, 0.3, 0.2]);
    for (refused, count) in outcomes {
        assert!(refused, "a deleted target must reject the late result");
        assert_eq!(
            count, 0,
            "deletion must remain complete after the late result"
        );
    }
    Ok(())
}
