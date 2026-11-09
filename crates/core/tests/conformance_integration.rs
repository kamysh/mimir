//! Requires an explicitly selected disposable AGE/pgvector database.
#[allow(dead_code)] // Shared guard exposes helpers for several test targets.
#[path = "../../../tests/support/isolation.rs"]
mod isolation;

use mimir_core::{
    config::Config,
    db,
    documents::DocumentChunk,
    graph::{Belief, Edge, EdgeType, MemoryType},
    store::AgeStore,
    MimirService,
};
use std::collections::HashSet;
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

async fn store() -> AgeStore {
    let cfg = config();
    db::migrate(&cfg.database).await.unwrap();
    AgeStore::new(
        db::connect(&cfg.database).await.unwrap(),
        cfg.database.dbname,
    )
    .unwrap()
}

#[tokio::test]
async fn closure_mixes_relations_crosses_depth_ten_and_deduplicates_cycles() {
    let store = store().await;
    let project = format!("closure-{}", Uuid::new_v4());
    let mut beliefs = Vec::new();
    for n in 0..17 {
        let b = Belief::new_in_project(format!("node {n}"), 0.5, 0.0, project.clone()).unwrap();
        store.insert_belief(&b).await.unwrap();
        beliefs.push(b);
    }
    for n in 0..13 {
        store
            .insert_edge(
                &Edge::new(beliefs[n].id, beliefs[n + 1].id, EdgeType::Causes, 0.2).unwrap(),
            )
            .await
            .unwrap();
    }
    for (from, to, kind) in [
        (13, 14, EdgeType::Supports),
        (14, 15, EdgeType::Defeats),
        (15, 0, EdgeType::Supports),
        (0, 1, EdgeType::Causes),
        (15, 16, EdgeType::Contradicts),
    ] {
        store
            .insert_edge(&Edge::new(beliefs[from].id, beliefs[to].id, kind, 0.2).unwrap())
            .await
            .unwrap();
    }
    let all = store.get_downstream_beliefs(beliefs[0].id).await.unwrap();
    let ids: HashSet<_> = all.iter().map(|b| b.id).collect();
    assert_eq!(ids, beliefs[..16].iter().map(|b| b.id).collect());
    assert_eq!(all.len(), ids.len());
    let causal = store
        .get_causal_downstream_beliefs(beliefs[0].id)
        .await
        .unwrap();
    assert_eq!(causal.len(), 13);
    assert_eq!(
        causal.iter().map(|b| b.id).collect::<HashSet<_>>(),
        beliefs[1..14].iter().map(|b| b.id).collect()
    );
    store.delete_project(&project).await.unwrap();
}

#[tokio::test]
async fn replacement_rejects_bad_preparation_and_rolls_back_late_vector_failure() {
    let store = store().await;
    let cfg = config();
    let observer = db::connect(&cfg.database).await.unwrap();
    let path = format!("/fixture/{}", Uuid::new_v4());
    let old = DocumentChunk::new(path.clone(), vec![], "old".into(), None, None);
    store
        .replace_document(&path, std::slice::from_ref(&old), &[vec![1.0, 0.0]])
        .await
        .unwrap();
    let new = DocumentChunk::new(path.clone(), vec![], "new".into(), None, None);
    assert!(store
        .replace_document(&path, std::slice::from_ref(&new), &[])
        .await
        .is_err());
    assert!(store
        .replace_document(&path, &[new.clone(), new.clone()], &[vec![1.0], vec![1.0]])
        .await
        .is_err());
    // pgvector rejects NaN after the old graph/vector pair has been removed
    // inside the still-uncommitted transaction. The old pair must survive.
    assert!(store
        .replace_document(&path, std::slice::from_ref(&new), &[vec![f32::NAN, 0.0]])
        .await
        .is_err());
    assert_eq!(
        store.get_chunk_ids_for_document(&path).await.unwrap(),
        vec![old.id]
    );
    assert!(store.get_chunk_by_id(new.id).await.unwrap().is_none());
    let count: i64 = observer
        .query_one(
            "SELECT count(*) FROM public.chunk_embeddings WHERE chunk_id=$1",
            &[&old.id],
        )
        .await
        .unwrap()
        .get(0);
    assert_eq!(count, 1);
    let other = DocumentChunk::new(
        format!("{path}-other"),
        vec![],
        "unrelated".into(),
        None,
        None,
    );
    store
        .replace_document(
            &other.document_path,
            std::slice::from_ref(&other),
            &[vec![0.0, 1.0]],
        )
        .await
        .unwrap();
    let mut collision = new.clone();
    collision.id = other.id;
    assert!(store
        .replace_document(&path, &[collision], &[vec![1.0, 0.0]])
        .await
        .is_err());
    store
        .replace_document(&path, std::slice::from_ref(&new), &[vec![0.5, 0.5]])
        .await
        .unwrap();
    assert!(store.get_chunk_by_id(old.id).await.unwrap().is_none());
    assert!(store.get_chunk_by_id(other.id).await.unwrap().is_some());
    assert_eq!(store.clear_document(&path).await.unwrap(), 1);
    assert_eq!(store.clear_document(&path).await.unwrap(), 0);
    let count: i64 = observer
        .query_one(
            "SELECT count(*) FROM public.chunk_embeddings WHERE chunk_id=ANY($1)",
            &[&vec![old.id, new.id]],
        )
        .await
        .unwrap()
        .get(0);
    assert_eq!(count, 0);
    store.clear_document(&other.document_path).await.unwrap();
}

#[tokio::test]
async fn stored_defeat_survives_a_later_propagation_failure() {
    let cfg = config();
    let service = MimirService::connect(&cfg).await.unwrap();
    let store = AgeStore::new(
        db::connect(&cfg.database).await.unwrap(),
        cfg.database.dbname.clone(),
    )
    .unwrap();
    let project = format!("edge-prefix-{}", Uuid::new_v4());
    let result: anyhow::Result<()> = async {
        let seed = isolation::seed_belief_in_project("seed", 0.8, 0.0, &project, MemoryType::Fact).await?;
        let target = isolation::seed_belief_in_project("target", 0.5, 0.0, &project, MemoryType::Fact).await?;
        let downstream = isolation::seed_belief_in_project("downstream", 0.5, 0.0, &project, MemoryType::Fact).await?;
        store.insert_edge(&Edge::new(target.id, downstream.id, EdgeType::Supports, 0.2)?).await?;
        let target_before = serde_json::to_value(store.get_belief(target.id).await?)?;
        let observer = db::connect(&cfg.database).await?;
        let g = &cfg.database.dbname;
        let id = downstream.id;
        // Keep the new edge's endpoints valid so admission succeeds. Corrupt a
        // later descendant to exercise propagation after the edge commits.
        observer.query(&format!("SELECT * FROM ag_catalog.cypher('{g}', $$ MATCH (b:Belief {{id:'{id}'}}) SET b.probability='invalid fixture numeric input' RETURN b.id $$) AS (id ag_catalog.agtype)"), &[]).await?;
        anyhow::ensure!(service.add_edge(seed.id, target.id, EdgeType::Defeats, 0.2).await.is_err(), "corrupt descendant must refuse propagation");
        let edges = store.get_edges_among(&[seed.id, target.id]).await?;
        anyhow::ensure!(edges.len() == 1, "expected exactly the committed defeat edge: {edges:?}");
        let (from, to, kind, weight) = edges[0];
        anyhow::ensure!(from == seed.id && to == target.id && kind == EdgeType::Defeats && weight.value() == 0.2, "stored defeat edge changed: {edges:?}");
        anyhow::ensure!(serde_json::to_value(store.get_belief(target.id).await?)? == target_before, "failed propagation changed the target belief");
        Ok(())
    }.await;
    let cleanup = store.delete_project(&project).await;
    result.unwrap();
    cleanup.unwrap();
}
