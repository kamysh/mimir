//! Actual service retrieval with a deterministic provider and owned PostgreSQL.
use super::{EmbedFuture, EmbeddingCancellation, EmbeddingProvider, OwnedEmbeddingBackend};
use crate::test_isolation as isolation;
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

enum QueryAnswer {
    Vectors(Vec<Vec<f32>>),
    Failed(String),
}
struct QueryProvider {
    answer: QueryAnswer,
    seen: std::sync::Arc<std::sync::Mutex<Vec<Vec<String>>>>,
}
impl EmbeddingProvider for QueryProvider {
    fn embed<'a>(
        &'a self,
        texts: &'a [String],
        cancellation: EmbeddingCancellation,
    ) -> EmbedFuture<'a> {
        Box::pin(async move {
            cancellation.check()?;
            self.seen.lock().unwrap().push(texts.to_vec());
            match &self.answer {
                QueryAnswer::Vectors(vectors) => Ok(vectors.clone()),
                QueryAnswer::Failed(cause) => anyhow::bail!("{cause}"),
            }
        })
    }
}

#[tokio::test]
async fn semantic_availability_preserves_literal_results_and_explains_each_actual_outcome(
) -> Result<()> {
    let database = isolation::fixture().database_config();
    let cfg = Config {
        database: database.clone(),
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
        retirement: None,
    };
    let client = db::connect(&database).await?;
    let store = AgeStore::new(db::connect(&database).await?, database.dbname.clone())?;
    let id: Uuid = client
        .query_one("SELECT gen_random_uuid()", &[])
        .await?
        .get(0);
    let project = format!("semantic-availability-{id}");
    let query = "E0412 literal identifier";
    let mut belief = Belief::new_in_project(query.into(), 0.7, 0.5, project.clone())?;
    belief.id = id;
    store.insert_belief(&belief).await?;
    store.insert_belief_embedding(id, &[1.0, 0.0, 0.0]).await?;
    let before = mimir_json::to_value(store.get_belief(id).await?)?;
    let complete_cause = format!(
        "The complete input has 513 positions; this backend accepts 512. {}",
        "Complete provider detail. ".repeat(400)
    );
    let cases = vec![
        (None, "unavailable", "not_configured", None),
        (
            Some(QueryAnswer::Failed(complete_cause.clone())),
            "unavailable",
            "embedding_failed",
            Some(complete_cause.clone()),
        ),
        (
            Some(QueryAnswer::Vectors(vec![])),
            "unavailable",
            "unusable_query_vector",
            Some("The backend returned no query embedding.".into()),
        ),
        (
            Some(QueryAnswer::Vectors(vec![vec![]])),
            "unavailable",
            "unusable_query_vector",
            Some("The query embedding is empty.".into()),
        ),
        (
            Some(QueryAnswer::Vectors(vec![vec![1.0], vec![2.0]])),
            "unavailable",
            "unusable_query_vector",
            Some("The backend returned multiple embeddings for one submitted context.".into()),
        ),
        (
            Some(QueryAnswer::Vectors(vec![vec![f32::NAN]])),
            "unavailable",
            "unusable_query_vector",
            Some("The query embedding contains a non-finite value.".into()),
        ),
        (
            Some(QueryAnswer::Vectors(vec![vec![0.0, -0.0, 0.0]])),
            "unavailable",
            "unusable_query_vector",
            Some("The query embedding has zero norm, so cosine similarity is undefined.".into()),
        ),
        (
            Some(QueryAnswer::Vectors(vec![vec![1.0, 0.0, 0.0]])),
            "available",
            "evaluated",
            None,
        ),
    ];
    let checked = async {
        for (answer, status, reason, cause) in cases {
            let seen = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
            let configured = answer.is_some();
            let backend = answer.map(|answer| OwnedEmbeddingBackend {
                provider: Box::new(QueryProvider {
                    answer,
                    seen: seen.clone(),
                }),
            });
            let service = MimirService::connect_with_embeddings(&cfg, backend).await?;
            let report = service
                .query_relevant(query, None, Some(&project), None)
                .await?;
            assert_eq!(
                report.beliefs.iter().map(|b| b.id).collect::<Vec<_>>(),
                vec![id]
            );
            assert_eq!(report.retrieval.context, query);
            assert_eq!(report.retrieval.semantic_search.status, status);
            assert_eq!(report.retrieval.semantic_search.reason, reason);
            assert_eq!(report.retrieval.semantic_search.cause, cause);
            assert!(
                !report.retrieval.message.is_empty()
                    && !report.retrieval.coverage.is_empty()
                    && !report.retrieval.next_step.is_empty()
            );
            if status == "unavailable" {
                assert_eq!(report.retrieval.matching_performed, "keyword");
                assert!(report
                    .retrieval
                    .message
                    .contains("semantic similarity was not evaluated"));
                assert!(report.retrieval.coverage.contains("may be missing"));
            } else {
                assert_eq!(report.retrieval.matching_performed, "keyword_and_semantic");
            }
            if let Some(cause) = cause {
                assert!(report.retrieval.message.contains(&cause));
            }
            let grounded = service
                .query_relevant_grounded(query, None, None, Some(&project))
                .await?;
            assert_eq!(grounded.retrieval, report.retrieval);
            assert_eq!(grounded.beliefs[0].belief.id, id);
            let context = service
                .query_learning_context(query, &project, None)
                .await?;
            assert_eq!(context.retrieval, report.retrieval);
            assert_eq!(context.beliefs[0].id, id);
            assert_eq!(mimir_json::to_value(store.get_belief(id).await?)?, before);
            assert_eq!(seen.lock().unwrap().len(), if configured { 3 } else { 0 });
            assert!(seen
                .lock()
                .unwrap()
                .iter()
                .all(|request| request == &vec![query.to_string()]));
        }
        Ok::<_, anyhow::Error>(())
    }
    .await;
    store.delete_project(&project).await?;
    checked
}

#[tokio::test]
async fn semantic_availability_does_not_claim_a_backend_failure_when_no_beliefs_are_searchable(
) -> Result<()> {
    let database = isolation::fixture().database_config();
    let cfg = Config {
        database: database.clone(),
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
        retirement: None,
    };
    let client = db::connect(&database).await?;
    let id: Uuid = client
        .query_one("SELECT gen_random_uuid()", &[])
        .await?
        .get(0);
    let seen = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
    let service = MimirService::connect_with_embeddings(
        &cfg,
        Some(OwnedEmbeddingBackend {
            provider: Box::new(QueryProvider {
                answer: QueryAnswer::Failed("must not be called".into()),
                seen: seen.clone(),
            }),
        }),
    )
    .await?;
    let report = service
        .query_relevant(
            "literal_identifier",
            None,
            Some(&format!("empty-semantic-{id}")),
            None,
        )
        .await?;
    assert!(report.beliefs.is_empty());
    assert_eq!(report.retrieval.semantic_search.status, "not_performed");
    assert_eq!(
        report.retrieval.semantic_search.reason,
        "no_eligible_beliefs"
    );
    assert_eq!(report.retrieval.matching_performed, "none");
    assert!(seen.lock().unwrap().is_empty());
    Ok(())
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
        retirement: None,
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
        .await?
        .beliefs;
    assert!(belief_ids.iter().all(|id| all.iter().any(|b| b.id == *id)));
    assert_eq!(
        service
            .query_relevant("vectorneedle", NonZeroUsize::new(12), Some(&project), None)
            .await?
            .beliefs
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
        .await?
        .beliefs;
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
        .await?
        .beliefs;
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
        .await?
        .beliefs;
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
