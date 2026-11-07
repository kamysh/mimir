//! Actual service retrieval with a deterministic provider and owned PostgreSQL.
#[allow(dead_code)]
#[path = "../../../../tests/support/isolation.rs"]
mod isolation;
use super::{EmbedFuture, EmbeddingCancellation, EmbeddingProvider, OwnedEmbeddingBackend};
use crate::{
    config::Config,
    db,
    documents::DocumentChunk,
    graph::{Belief, Pattern},
    store::AgeStore,
    MimirService,
};
use anyhow::Result;
use std::num::NonZeroUsize;
use uuid::Uuid;

struct ConstantProvider;
impl EmbeddingProvider for ConstantProvider {
    fn embed<'a>(
        &'a self,
        texts: &'a [String],
        cancellation: EmbeddingCancellation,
    ) -> EmbedFuture<'a> {
        Box::pin(async move {
            cancellation.check()?;
            Ok(texts.iter().map(|_| vec![1.0, 0.0, 0.0]).collect())
        })
    }
}

#[tokio::test]
async fn all_matches_survive_former_vector_pools_and_only_explicit_counts_cut_results() -> Result<()>
{
    let database = isolation::fixture().database_config();
    let cfg = Config {
        database: database.clone(),
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
    };
    let service = MimirService::connect_with_embeddings(
        &cfg,
        Some(OwnedEmbeddingBackend {
            provider: Box::new(ConstantProvider),
        }),
    )
    .await?;
    let client = db::connect(&database).await?;
    let store = AgeStore::new(db::connect(&database).await?, database.dbname.clone())?;
    let project_id: Uuid = client
        .query_one("SELECT gen_random_uuid()", &[])
        .await?
        .get(0);
    let project = format!("selection-{project_id}");
    let mut belief_ids = Vec::new();
    let mut chunks = Vec::new();
    // One more than the former unlimited-query vector pool of fifty. The
    // query token does not occur in beliefs, so lexical retrieval cannot hide
    // a truncated vector pool.
    for n in 0..51 {
        let row = client
            .query_one("SELECT gen_random_uuid(),gen_random_uuid()", &[])
            .await?;
        let belief_id: Uuid = row.get(0);
        let chunk_id: Uuid = row.get(1);
        let mut belief = Belief::new_in_project(
            format!("unrelated indexed record {n}"),
            0.7,
            0.5,
            project.clone(),
        )?;
        belief.id = belief_id;
        store.insert_belief(&belief).await?;
        store
            .insert_belief_embedding(belief_id, &[1.0, 0.0, 0.0])
            .await?;
        store
            .insert_document_chunk(&DocumentChunk::with_id(
                chunk_id,
                format!("/{project}/{n}.md"),
                vec![],
                format!("supporting passage {n}"),
                None,
                Some(project.clone()),
            ))
            .await?;
        store
            .insert_chunk_embedding(chunk_id, &[1.0, 0.0, 0.0])
            .await?;
        belief_ids.push(belief_id);
        chunks.push(chunk_id);
    }
    for n in 0..7 {
        let id: Uuid = client
            .query_one("SELECT gen_random_uuid()", &[])
            .await?
            .get(0);
        let mut pattern = Pattern::new_in_project(
            format!("vectorneedle situation {n}"),
            "observed procedure".into(),
            0.5,
            project.clone(),
        )?;
        pattern.id = id;
        store.insert_pattern(&pattern).await?;
    }
    for (n, chunk) in chunks.iter().enumerate().take(5) {
        service
            .add_evidence(belief_ids[0], *chunk, 0.5 + n as f64 / 10.0)
            .await?;
    }
    let all = service
        .query_relevant("vectorneedle", None, Some(&project), None)
        .await?;
    assert!(belief_ids.iter().all(|id| all.iter().any(|b| b.id == *id)));
    assert_eq!(
        service
            .query_relevant("vectorneedle", NonZeroUsize::new(12), Some(&project), None)
            .await?
            .len(),
        12
    );
    let huge = service
        .query_relevant(
            "vectorneedle",
            NonZeroUsize::new(usize::MAX),
            Some(&project),
            None,
        )
        .await?;
    assert!(belief_ids.iter().all(|id| huge.iter().any(|b| b.id == *id)));
    assert_eq!(
        service
            .query_document("vectorneedle", Some(&project), None)
            .await?
            .len(),
        51
    );
    assert_eq!(
        service
            .query_document("vectorneedle", Some(&project), NonZeroUsize::new(12))
            .await?
            .len(),
        12
    );
    assert_eq!(
        service
            .query_document(
                "vectorneedle",
                Some(&project),
                NonZeroUsize::new(usize::MAX)
            )
            .await?
            .len(),
        51
    );
    let context = service
        .query_learning_context("vectorneedle", &project, None)
        .await?;
    assert_eq!(context.patterns.len(), 7);
    assert!(belief_ids
        .iter()
        .all(|id| context.beliefs.iter().any(|b| b.id == *id)));
    let selected = service
        .query_learning_context("vectorneedle", &project, NonZeroUsize::new(3))
        .await?;
    assert_eq!(selected.beliefs.len(), 3);
    assert_eq!(selected.patterns.len(), 3);
    let grounded = service
        .query_relevant_grounded("vectorneedle", None, None, Some(&project))
        .await?;
    assert_eq!(
        grounded
            .iter()
            .find(|g| g.belief.id == belief_ids[0])
            .unwrap()
            .evidence
            .len(),
        5
    );
    let grounded = service
        .query_relevant_grounded("vectorneedle", None, NonZeroUsize::new(2), Some(&project))
        .await?;
    assert_eq!(
        grounded
            .iter()
            .find(|g| g.belief.id == belief_ids[0])
            .unwrap()
            .evidence
            .len(),
        2
    );
    assert_eq!(
        service
            .evidence_for_belief(belief_ids[0], None)
            .await?
            .len(),
        5
    );
    service.delete_project(&project).await?;
    Ok(())
}
