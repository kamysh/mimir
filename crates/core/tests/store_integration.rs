use mimir_core::{
    config::{Config, DatabaseConfig},
    db,
    documents::DocumentChunk,
    graph::{Belief, Edge, EdgeType, Pattern, Probability},
    store::AgeStore,
    MimirService,
};
use uuid::Uuid;

fn test_db_config() -> DatabaseConfig {
    DatabaseConfig {
        host: std::env::var("MIMIR_HOST").expect("MIMIR_HOST must be set to run integration tests"),
        port: std::env::var("MIMIR_PORT")
            .expect("MIMIR_PORT must be set to run integration tests")
            .parse()
            .expect("MIMIR_PORT must be a valid port number"),
        dbname: std::env::var("MIMIR_DBNAME")
            .expect("MIMIR_DBNAME must be set to run integration tests"),
        user: std::env::var("MIMIR_USER").expect("MIMIR_USER must be set to run integration tests"),
        ssl_mode: mimir_core::config::SslMode::default(),
        ssl_root_cert: None,
        ssl_client_cert: None,
        ssl_client_key: None,
    }
}

// ---------------------------------------------------------------------------
// Per-test isolated project context.
//
// Each test gets a unique project tag ("_test-<uuid>") so parallel tests never
// interfere with each other's data or cleanup. `TestCtx::cleanup()` deletes
// only the beliefs and patterns created by that specific test run.
// ---------------------------------------------------------------------------

struct TestCtx {
    store: AgeStore,
    project: String,
}

impl TestCtx {
    async fn new() -> Self {
        let cfg = test_db_config();
        let graph_name = cfg.dbname.clone();
        let client = db::connect(&cfg).await.expect("connect");
        let store = AgeStore::new(client, graph_name).expect("valid graph_name");
        let project = format!("_test-{}", Uuid::new_v4().simple());
        Self { store, project }
    }

    fn belief(&self, content: String, p: f64, c: f64) -> Belief {
        Belief::new_in_project(content, p, c, self.project.clone()).unwrap()
    }

    fn pattern(&self, situation: String, approach: String, success_rate: f64) -> Pattern {
        Pattern::new_in_project(situation, approach, success_rate, self.project.clone()).unwrap()
    }

    fn chunk(&self, source_path: &str, content: &str) -> DocumentChunk {
        DocumentChunk::new(
            source_path.to_string(),
            vec![],
            content.to_string(),
            None,
            Some(self.project.clone()),
        )
    }

    async fn cleanup(&self) {
        // BUG FIX (2026-08-13): this previously called only self.store.delete_project,
        // the store-layer method that deletes Belief/Pattern vertices ONLY — it has no
        // knowledge of DocumentChunk. MimirService::delete_project (lib.rs) is the
        // service-layer wrapper that additionally clears DocumentChunk vertices and
        // their pgvector rows; tests must mirror that, or every chunk a test creates
        // leaks into the live graph permanently, on every successful run (not just
        // crashes — confirmed live: 296 DocumentChunk vertices in production, the
        // overwhelming majority from `_test-*` projects never cleaned up).
        let _ = self.store.delete_project(&self.project).await;
        if let Ok(chunk_ids) = self.store.get_chunk_ids_by_project(&self.project).await {
            let _ = self.store.delete_document_chunks(&chunk_ids).await;
            let _ = self.store.delete_chunk_embeddings(&chunk_ids).await;
        }
    }
}

async fn service() -> MimirService {
    let cfg = Config {
        database: test_db_config(),
        embeddings: None,
    };
    MimirService::connect(&cfg).await.expect("connect service")
}

// ---------------------------------------------------------------------------
// Belief CRUD
// ---------------------------------------------------------------------------

#[tokio::test]
async fn test_insert_and_get_belief() {
    let ctx = TestCtx::new().await;
    let b = ctx.belief(format!("belief-{}", Uuid::new_v4()), 0.75, 0.85);
    ctx.store.insert_belief(&b).await.expect("insert_belief");
    let got = ctx
        .store
        .get_belief(b.id)
        .await
        .expect("get_belief")
        .expect("should exist");
    assert_eq!(got.id, b.id);
    assert_eq!(got.content, b.content);
    assert!((got.probability.value() - 0.75).abs() < 1e-9);
    assert!((got.confidence.value() - 0.85).abs() < 1e-9);
    ctx.cleanup().await;
}

#[tokio::test]
async fn test_get_nonexistent_belief_returns_none() {
    let ctx = TestCtx::new().await;
    let result = ctx
        .store
        .get_belief(Uuid::new_v4())
        .await
        .expect("get_belief");
    assert!(result.is_none());
    ctx.cleanup().await;
}

#[tokio::test]
async fn test_list_beliefs_contains_inserted() {
    let ctx = TestCtx::new().await;
    let b = ctx.belief(format!("list-{}", Uuid::new_v4()), 0.5, 0.5);
    ctx.store.insert_belief(&b).await.unwrap();
    let all = ctx.store.list_beliefs().await.unwrap();
    assert!(all.iter().any(|x| x.id == b.id));
    ctx.cleanup().await;
}

#[tokio::test]
async fn test_list_beliefs_multiple() {
    let ctx = TestCtx::new().await;
    let mut inserted = Vec::new();
    for i in 0..5 {
        let b = ctx.belief(format!("multi-{}-{}", i, Uuid::new_v4()), 0.5, 0.5);
        ctx.store.insert_belief(&b).await.unwrap();
        inserted.push(b.id);
    }
    let all = ctx.store.list_beliefs().await.unwrap();
    for id in &inserted {
        assert!(all.iter().any(|x| x.id == *id), "missing {}", id);
    }
    ctx.cleanup().await;
}

#[tokio::test]
async fn test_list_beliefs_by_project_scopes_correctly() {
    let ctx = TestCtx::new().await;
    let other_project = format!("_test-other-{}", Uuid::new_v4().simple());

    let mine = ctx.belief(format!("scope-mine-{}", Uuid::new_v4()), 0.5, 0.5);
    ctx.store.insert_belief(&mine).await.unwrap();

    let other = Belief::new_in_project(
        format!("scope-other-{}", Uuid::new_v4()),
        0.5,
        0.5,
        other_project.clone(),
    )
    .unwrap();
    ctx.store.insert_belief(&other).await.unwrap();

    let untagged = Belief::new(format!("scope-untagged-{}", Uuid::new_v4()), 0.5, 0.5).unwrap();
    ctx.store.insert_belief(&untagged).await.unwrap();

    let scoped = ctx
        .store
        .list_beliefs_by_project(&ctx.project)
        .await
        .unwrap();
    assert!(scoped.iter().any(|b| b.id == mine.id), "own belief missing");
    assert!(
        scoped.iter().any(|b| b.id == untagged.id),
        "untagged belief should be visible from every project scope"
    );
    assert!(
        !scoped.iter().any(|b| b.id == other.id),
        "another project's belief leaked into scope"
    );

    ctx.cleanup().await;
    let _ = ctx.store.delete_project(&other_project).await;
    ctx.store.delete_belief(untagged.id).await.unwrap();
}

// Phase 3 (spec Mimir.Graph: RETIRED SCALAR SETTERS): the old field-independent
// setters update_belief_probability / update_belief_confidence are retired —
// belief state is written only via the Beta posterior (update_belief_beta), so
// the tests that asserted the old scalar contract are removed.

#[tokio::test]
async fn test_update_belief_beta_round_trips_mean_and_strength() {
    let ctx = TestCtx::new().await;
    let b = ctx.belief(format!("upd-beta-{}", Uuid::new_v4()), 0.5, 0.5);
    ctx.store.insert_belief(&b).await.unwrap();
    // A strong support posterior: mean 0.9 at strength 100 ⇒ (α,β)=(90,10).
    ctx.store
        .update_belief_beta(b.id, 90.0, 10.0)
        .await
        .unwrap();
    let got = ctx.store.get_belief(b.id).await.unwrap().unwrap();
    // Durable (α,β) persisted (spec store-load-round-trip); mean derived = 0.9.
    assert!(
        (got.alpha - 90.0).abs() < 1e-6,
        "α persisted: {}",
        got.alpha
    );
    assert!((got.beta - 10.0).abs() < 1e-6, "β persisted: {}", got.beta);
    assert!((got.probability.value() - 0.9).abs() < 1e-9);
    ctx.cleanup().await;
}

#[tokio::test]
async fn test_memory_type_round_trips_through_store() {
    use mimir_core::graph::MemoryType;

    let ctx = TestCtx::new().await;
    let fact = ctx.belief(format!("mt-fact-{}", Uuid::new_v4()), 0.5, 0.5);
    let experiential = ctx
        .belief(format!("mt-exp-{}", Uuid::new_v4()), 0.5, 0.5)
        .with_memory_type(MemoryType::Experiential);
    let working = ctx
        .belief(format!("mt-work-{}", Uuid::new_v4()), 0.5, 0.5)
        .with_memory_type(MemoryType::Working);

    ctx.store.insert_belief(&fact).await.unwrap();
    ctx.store.insert_belief(&experiential).await.unwrap();
    ctx.store.insert_belief(&working).await.unwrap();

    let got_fact = ctx.store.get_belief(fact.id).await.unwrap().unwrap();
    let got_exp = ctx
        .store
        .get_belief(experiential.id)
        .await
        .unwrap()
        .unwrap();
    let got_work = ctx.store.get_belief(working.id).await.unwrap().unwrap();

    assert_eq!(got_fact.memory_type, MemoryType::Fact);
    assert_eq!(got_exp.memory_type, MemoryType::Experiential);
    assert_eq!(got_work.memory_type, MemoryType::Working);

    // list_beliefs_by_project must also carry the type through.
    let scoped = ctx
        .store
        .list_beliefs_by_project(&ctx.project)
        .await
        .unwrap();
    let scoped_exp = scoped
        .iter()
        .find(|b| b.id == experiential.id)
        .expect("experiential belief missing from scoped list");
    assert_eq!(scoped_exp.memory_type, MemoryType::Experiential);

    ctx.cleanup().await;
}

#[tokio::test]
async fn test_belief_boundary_probabilities() {
    let ctx = TestCtx::new().await;
    let b = ctx.belief(format!("bound-{}", Uuid::new_v4()), 0.0, 1.0);
    ctx.store.insert_belief(&b).await.unwrap();
    let got = ctx.store.get_belief(b.id).await.unwrap().unwrap();
    assert!((got.probability.value() - 0.0).abs() < 1e-9);
    assert!((got.confidence.value() - 1.0).abs() < 1e-9);
    ctx.cleanup().await;
}

#[tokio::test]
async fn test_belief_content_with_special_chars() {
    let ctx = TestCtx::new().await;
    // Single quotes: exercises sql_esc ('' doubling in EXECUTE argument)
    let b = ctx.belief(
        format!("it's a test with 'quotes' and more-{}", Uuid::new_v4()),
        0.6,
        0.7,
    );
    ctx.store.insert_belief(&b).await.unwrap();
    let got = ctx.store.get_belief(b.id).await.unwrap().unwrap();
    assert_eq!(got.content, b.content);
    ctx.cleanup().await;
}

#[tokio::test]
async fn test_belief_content_with_backslash_and_doublequote() {
    let ctx = TestCtx::new().await;
    // Backslash + double-quote: exercises json_esc (\ → \\ and " → \")
    // before sql_esc, which is the two-layer escaping path for AGE PREPARE/EXECUTE.
    let b = ctx.belief(
        format!(r#"path\to\"file\" with back\\slash-{}"#, Uuid::new_v4()),
        0.7,
        0.8,
    );
    ctx.store.insert_belief(&b).await.unwrap();
    let got = ctx.store.get_belief(b.id).await.unwrap().unwrap();
    assert_eq!(got.content, b.content);
    ctx.cleanup().await;
}

#[tokio::test]
async fn test_belief_content_with_unicode() {
    let ctx = TestCtx::new().await;
    let b = ctx.belief(
        format!("信念 belief Überzeugung -{}", Uuid::new_v4()),
        0.7,
        0.8,
    );
    ctx.store.insert_belief(&b).await.unwrap();
    let got = ctx.store.get_belief(b.id).await.unwrap().unwrap();
    assert_eq!(got.content, b.content);
    ctx.cleanup().await;
}

// ---------------------------------------------------------------------------
// Pattern CRUD
// ---------------------------------------------------------------------------

#[tokio::test]
async fn test_insert_and_list_patterns() {
    let ctx = TestCtx::new().await;
    let p = ctx.pattern(
        format!("situation-{}", Uuid::new_v4()),
        format!("approach-{}", Uuid::new_v4()),
        0.8,
    );
    ctx.store.insert_pattern(&p).await.unwrap();
    let all = ctx.store.list_patterns().await.unwrap();
    assert!(all.iter().any(|x| x.id == p.id));
    ctx.cleanup().await;
}

#[tokio::test]
async fn test_list_patterns_by_project_scopes_correctly() {
    let ctx = TestCtx::new().await;
    let other_project = format!("_test-other-{}", Uuid::new_v4().simple());

    let mine = ctx.pattern(
        format!("situation-mine-{}", Uuid::new_v4()),
        format!("approach-mine-{}", Uuid::new_v4()),
        0.8,
    );
    ctx.store.insert_pattern(&mine).await.unwrap();

    let other = Pattern::new_in_project(
        format!("situation-other-{}", Uuid::new_v4()),
        format!("approach-other-{}", Uuid::new_v4()),
        0.8,
        other_project.clone(),
    )
    .unwrap();
    ctx.store.insert_pattern(&other).await.unwrap();

    let scoped = ctx
        .store
        .list_patterns_by_project(&ctx.project)
        .await
        .unwrap();
    assert!(
        scoped.iter().any(|p| p.id == mine.id),
        "own pattern missing"
    );
    assert!(
        !scoped.iter().any(|p| p.id == other.id),
        "another project's pattern leaked into scope"
    );

    ctx.cleanup().await;
    let _ = ctx.store.delete_project(&other_project).await;
}

#[tokio::test]
async fn test_list_patterns_multiple() {
    let ctx = TestCtx::new().await;
    let mut inserted = Vec::new();
    for i in 0..3 {
        let p = ctx.pattern(
            format!("sit-{}-{}", i, Uuid::new_v4()),
            format!("app-{}-{}", i, Uuid::new_v4()),
            0.5 + i as f64 * 0.1,
        );
        ctx.store.insert_pattern(&p).await.unwrap();
        inserted.push(p.id);
    }
    let all = ctx.store.list_patterns().await.unwrap();
    for id in &inserted {
        assert!(all.iter().any(|x| x.id == *id));
    }
    ctx.cleanup().await;
}

#[tokio::test]
async fn test_pattern_boundary_success_rate() {
    let ctx = TestCtx::new().await;
    let p = ctx.pattern(
        format!("sit-{}", Uuid::new_v4()),
        "approach".to_string(),
        1.0,
    );
    ctx.store.insert_pattern(&p).await.unwrap();
    let all = ctx.store.list_patterns().await.unwrap();
    let got = all.iter().find(|x| x.id == p.id).unwrap();
    assert!((got.success_rate.value() - 1.0).abs() < 1e-9);
    ctx.cleanup().await;
}

// ---------------------------------------------------------------------------
// Edges
// ---------------------------------------------------------------------------

#[tokio::test]
async fn test_insert_edge_supports() {
    let ctx = TestCtx::new().await;
    let b1 = ctx.belief(format!("cause-{}", Uuid::new_v4()), 0.8, 0.9);
    let b2 = ctx.belief(format!("effect-{}", Uuid::new_v4()), 0.7, 0.8);
    ctx.store.insert_belief(&b1).await.unwrap();
    ctx.store.insert_belief(&b2).await.unwrap();
    let edge = Edge::new(b1.id, b2.id, EdgeType::Supports, 0.9).unwrap();
    ctx.store.insert_edge(&edge).await.unwrap();
    let downstream = ctx.store.get_downstream_beliefs(b1.id).await.unwrap();
    assert!(downstream.iter().any(|b| b.id == b2.id));
    ctx.cleanup().await;
}

#[tokio::test]
async fn test_insert_edge_causes() {
    let ctx = TestCtx::new().await;
    let b1 = ctx.belief(format!("cause-{}", Uuid::new_v4()), 0.8, 0.9);
    let b2 = ctx.belief(format!("effect-{}", Uuid::new_v4()), 0.7, 0.8);
    ctx.store.insert_belief(&b1).await.unwrap();
    ctx.store.insert_belief(&b2).await.unwrap();
    let edge = Edge::new(b1.id, b2.id, EdgeType::Causes, 0.8).unwrap();
    ctx.store.insert_edge(&edge).await.unwrap();
    let downstream = ctx.store.get_downstream_beliefs(b1.id).await.unwrap();
    assert!(downstream.iter().any(|b| b.id == b2.id));
    ctx.cleanup().await;
}

#[tokio::test]
async fn test_insert_edge_defeats() {
    let ctx = TestCtx::new().await;
    let b1 = ctx.belief(format!("defeater-{}", Uuid::new_v4()), 0.9, 0.9);
    let b2 = ctx.belief(format!("defeated-{}", Uuid::new_v4()), 0.8, 0.8);
    ctx.store.insert_belief(&b1).await.unwrap();
    ctx.store.insert_belief(&b2).await.unwrap();
    let edge = Edge::new(b1.id, b2.id, EdgeType::Defeats, 1.0).unwrap();
    ctx.store.insert_edge(&edge).await.unwrap();
    // Edge stored — verify via get_edges_among
    let edges = ctx.store.get_edges_among(&[b1.id, b2.id]).await.unwrap();
    assert!(edges
        .iter()
        .any(|(f, t, et, _)| *f == b1.id && *t == b2.id && *et == EdgeType::Defeats));
    ctx.cleanup().await;
}

#[tokio::test]
async fn test_insert_edge_missing_source_fails() {
    let ctx = TestCtx::new().await;
    let b = ctx.belief(format!("only-{}", Uuid::new_v4()), 0.5, 0.5);
    ctx.store.insert_belief(&b).await.unwrap();
    // from_id is a random UUID that was never inserted
    let edge = Edge::new(Uuid::new_v4(), b.id, EdgeType::Supports, 0.5).unwrap();
    let result = ctx.store.insert_edge(&edge).await;
    assert!(result.is_err());
    ctx.cleanup().await;
}

#[tokio::test]
async fn test_insert_edge_missing_target_fails() {
    let ctx = TestCtx::new().await;
    let b = ctx.belief(format!("only-{}", Uuid::new_v4()), 0.5, 0.5);
    ctx.store.insert_belief(&b).await.unwrap();
    let edge = Edge::new(b.id, Uuid::new_v4(), EdgeType::Supports, 0.5).unwrap();
    let result = ctx.store.insert_edge(&edge).await;
    assert!(result.is_err());
    ctx.cleanup().await;
}

// ---------------------------------------------------------------------------
// Contradictions
// ---------------------------------------------------------------------------

#[tokio::test]
async fn test_contradicts_bidirectional() {
    let ctx = TestCtx::new().await;
    let b1 = ctx.belief(format!("contra-a-{}", Uuid::new_v4()), 0.6, 0.7);
    let b2 = ctx.belief(format!("contra-b-{}", Uuid::new_v4()), 0.4, 0.6);
    ctx.store.insert_belief(&b1).await.unwrap();
    ctx.store.insert_belief(&b2).await.unwrap();
    let w = Probability::new(0.95).unwrap();
    ctx.store.insert_contradicts(b1.id, b2.id, w).await.unwrap();
    let pairs = ctx.store.get_contradiction_pairs().await.unwrap();
    assert!(pairs.iter().any(|(a, b)| *a == b1.id && *b == b2.id));
    assert!(pairs.iter().any(|(a, b)| *a == b2.id && *b == b1.id));
    ctx.cleanup().await;
}

#[tokio::test]
async fn test_no_contradiction_without_edge() {
    let ctx = TestCtx::new().await;
    let b1 = ctx.belief(format!("nocont-a-{}", Uuid::new_v4()), 0.6, 0.7);
    let b2 = ctx.belief(format!("nocont-b-{}", Uuid::new_v4()), 0.6, 0.7);
    ctx.store.insert_belief(&b1).await.unwrap();
    ctx.store.insert_belief(&b2).await.unwrap();
    let pairs = ctx.store.get_contradiction_pairs().await.unwrap();
    let has = pairs
        .iter()
        .any(|(a, b)| (*a == b1.id && *b == b2.id) || (*a == b2.id && *b == b1.id));
    assert!(!has);
    ctx.cleanup().await;
}

#[tokio::test]
async fn test_get_contradiction_pairs_by_project_scopes_correctly() {
    let ctx = TestCtx::new().await;
    let other_project = format!("_test-other-{}", Uuid::new_v4().simple());

    // In-scope pair: both endpoints in ctx.project.
    let a1 = ctx.belief(format!("scopecontra-a1-{}", Uuid::new_v4()), 0.6, 0.7);
    let a2 = ctx.belief(format!("scopecontra-a2-{}", Uuid::new_v4()), 0.4, 0.6);
    ctx.store.insert_belief(&a1).await.unwrap();
    ctx.store.insert_belief(&a2).await.unwrap();
    let w = Probability::new(0.95).unwrap();
    ctx.store.insert_contradicts(a1.id, a2.id, w).await.unwrap();

    // Out-of-scope pair: both endpoints in a different project.
    let b1 = Belief::new_in_project(
        format!("scopecontra-b1-{}", Uuid::new_v4()),
        0.6,
        0.7,
        other_project.clone(),
    )
    .unwrap();
    let b2 = Belief::new_in_project(
        format!("scopecontra-b2-{}", Uuid::new_v4()),
        0.4,
        0.6,
        other_project.clone(),
    )
    .unwrap();
    ctx.store.insert_belief(&b1).await.unwrap();
    ctx.store.insert_belief(&b2).await.unwrap();
    ctx.store.insert_contradicts(b1.id, b2.id, w).await.unwrap();

    let scoped = ctx
        .store
        .get_contradiction_pairs_by_project(&ctx.project)
        .await
        .unwrap();
    assert!(
        scoped.iter().any(|(a, b)| *a == a1.id && *b == a2.id),
        "own contradiction pair missing"
    );
    assert!(
        !scoped.iter().any(|(a, b)| *a == b1.id && *b == b2.id),
        "another project's contradiction pair leaked into scope"
    );

    ctx.cleanup().await;
    let _ = ctx.store.delete_project(&other_project).await;
}

// ---------------------------------------------------------------------------
// get_edges_among
// ---------------------------------------------------------------------------

#[tokio::test]
async fn test_get_edges_among_two_edges() {
    let ctx = TestCtx::new().await;
    let b1 = ctx.belief(format!("ea-{}", Uuid::new_v4()), 0.8, 0.9);
    let b2 = ctx.belief(format!("eb-{}", Uuid::new_v4()), 0.7, 0.8);
    let b3 = ctx.belief(format!("ec-{}", Uuid::new_v4()), 0.6, 0.7);
    ctx.store.insert_belief(&b1).await.unwrap();
    ctx.store.insert_belief(&b2).await.unwrap();
    ctx.store.insert_belief(&b3).await.unwrap();
    ctx.store
        .insert_edge(&Edge::new(b1.id, b2.id, EdgeType::Supports, 0.9).unwrap())
        .await
        .unwrap();
    ctx.store
        .insert_edge(&Edge::new(b2.id, b3.id, EdgeType::Causes, 0.7).unwrap())
        .await
        .unwrap();

    let edges = ctx
        .store
        .get_edges_among(&[b1.id, b2.id, b3.id])
        .await
        .unwrap();
    assert!(edges
        .iter()
        .any(|(f, t, et, _)| *f == b1.id && *t == b2.id && *et == EdgeType::Supports));
    assert!(edges
        .iter()
        .any(|(f, t, et, _)| *f == b2.id && *t == b3.id && *et == EdgeType::Causes));
    ctx.cleanup().await;
}

#[tokio::test]
async fn test_get_edges_among_empty_input() {
    let ctx = TestCtx::new().await;
    let edges = ctx.store.get_edges_among(&[]).await.unwrap();
    assert!(edges.is_empty());
    ctx.cleanup().await;
}

#[tokio::test]
async fn test_get_edges_among_excludes_outside_set() {
    let ctx = TestCtx::new().await;
    let b1 = ctx.belief(format!("excl-a-{}", Uuid::new_v4()), 0.8, 0.9);
    let b2 = ctx.belief(format!("excl-b-{}", Uuid::new_v4()), 0.7, 0.8);
    let b3 = ctx.belief(format!("excl-c-{}", Uuid::new_v4()), 0.6, 0.7);
    ctx.store.insert_belief(&b1).await.unwrap();
    ctx.store.insert_belief(&b2).await.unwrap();
    ctx.store.insert_belief(&b3).await.unwrap();
    ctx.store
        .insert_edge(&Edge::new(b1.id, b3.id, EdgeType::Supports, 0.9).unwrap())
        .await
        .unwrap();

    // Only ask about b1 and b2 — the b1→b3 edge should not appear
    let edges = ctx.store.get_edges_among(&[b1.id, b2.id]).await.unwrap();
    assert!(!edges.iter().any(|(_, t, _, _)| *t == b3.id));
    ctx.cleanup().await;
}

// ---------------------------------------------------------------------------
// get_downstream_beliefs
// ---------------------------------------------------------------------------

#[tokio::test]
async fn test_get_downstream_via_causes() {
    let ctx = TestCtx::new().await;
    let b1 = ctx.belief(format!("dn-cause-{}", Uuid::new_v4()), 0.8, 0.9);
    let b2 = ctx.belief(format!("dn-effect-{}", Uuid::new_v4()), 0.6, 0.7);
    ctx.store.insert_belief(&b1).await.unwrap();
    ctx.store.insert_belief(&b2).await.unwrap();
    ctx.store
        .insert_edge(&Edge::new(b1.id, b2.id, EdgeType::Causes, 0.8).unwrap())
        .await
        .unwrap();
    let downstream = ctx.store.get_downstream_beliefs(b1.id).await.unwrap();
    assert!(downstream.iter().any(|b| b.id == b2.id));
    ctx.cleanup().await;
}

#[tokio::test]
async fn test_get_downstream_no_edges_empty() {
    let ctx = TestCtx::new().await;
    let b = ctx.belief(format!("isolated-{}", Uuid::new_v4()), 0.5, 0.5);
    ctx.store.insert_belief(&b).await.unwrap();
    let downstream = ctx.store.get_downstream_beliefs(b.id).await.unwrap();
    assert!(!downstream.iter().any(|x| x.id == b.id)); // self not included
    ctx.cleanup().await;
}

#[tokio::test]
async fn test_get_downstream_multi_hop() {
    let ctx = TestCtx::new().await;
    let b1 = ctx.belief(format!("hop1-{}", Uuid::new_v4()), 0.9, 0.9);
    let b2 = ctx.belief(format!("hop2-{}", Uuid::new_v4()), 0.8, 0.8);
    let b3 = ctx.belief(format!("hop3-{}", Uuid::new_v4()), 0.7, 0.7);
    ctx.store.insert_belief(&b1).await.unwrap();
    ctx.store.insert_belief(&b2).await.unwrap();
    ctx.store.insert_belief(&b3).await.unwrap();
    ctx.store
        .insert_edge(&Edge::new(b1.id, b2.id, EdgeType::Supports, 0.9).unwrap())
        .await
        .unwrap();
    ctx.store
        .insert_edge(&Edge::new(b2.id, b3.id, EdgeType::Supports, 0.8).unwrap())
        .await
        .unwrap();
    let downstream = ctx.store.get_downstream_beliefs(b1.id).await.unwrap();
    assert!(downstream.iter().any(|b| b.id == b2.id));
    assert!(downstream.iter().any(|b| b.id == b3.id));
    ctx.cleanup().await;
}

#[tokio::test]
async fn test_get_direct_downstream_by_project_one_hop() {
    let ctx = TestCtx::new().await;
    let other_project = format!("_test-other-{}", Uuid::new_v4().simple());
    let seed = ctx.belief(format!("dirdown-seed-{}", Uuid::new_v4()), 0.6, 0.6);
    let in_scope = ctx.belief(format!("dirdown-in-{}", Uuid::new_v4()), 0.6, 0.6);
    let out_of_scope = Belief::new_in_project(
        format!("dirdown-out-{}", Uuid::new_v4()),
        0.6,
        0.6,
        other_project.clone(),
    )
    .unwrap();
    ctx.store.insert_belief(&seed).await.unwrap();
    ctx.store.insert_belief(&in_scope).await.unwrap();
    ctx.store.insert_belief(&out_of_scope).await.unwrap();
    ctx.store
        .insert_edge(&Edge::new(seed.id, in_scope.id, EdgeType::Supports, 0.8).unwrap())
        .await
        .unwrap();
    ctx.store
        .insert_edge(&Edge::new(seed.id, out_of_scope.id, EdgeType::Supports, 0.8).unwrap())
        .await
        .unwrap();

    let neighbors = ctx
        .store
        .get_direct_downstream_by_project(seed.id, &ctx.project)
        .await
        .unwrap();
    assert!(
        neighbors.iter().any(|b| b.id == in_scope.id),
        "in-scope neighbor missing"
    );
    assert!(
        !neighbors.iter().any(|b| b.id == out_of_scope.id),
        "out-of-scope neighbor leaked"
    );

    ctx.cleanup().await;
    let _ = ctx.store.delete_project(&other_project).await;
}

// Working-memory beliefs must never surface from query_relevant's candidate
// pool (the token/vector/prior legs), even when their content directly
// matches the query term.
#[tokio::test]
async fn test_query_relevant_excludes_working_from_candidate_pool() {
    let svc = service().await;
    let ctx = TestCtx::new().await;
    let term = Uuid::new_v4().simple().to_string();

    let fact = ctx.belief(format!("factterm {term}"), 0.6, 0.6);
    let working = ctx
        .belief(format!("factterm {term}"), 0.6, 0.6)
        .with_memory_type(mimir_core::graph::MemoryType::Working);
    ctx.store.insert_belief(&fact).await.unwrap();
    ctx.store.insert_belief(&working).await.unwrap();

    let results = svc
        .query_relevant(&format!("factterm {term}"), 0, Some(&ctx.project))
        .await
        .unwrap();
    assert!(
        results.iter().any(|b| b.id == fact.id),
        "fact belief with matching content should be retrieved"
    );
    assert!(
        !results.iter().any(|b| b.id == working.id),
        "working belief with matching content leaked into query_relevant results"
    );

    ctx.cleanup().await;
}

// Working-memory beliefs must also be excluded when reached only via graph
// expansion (SUPPORTS/CAUSES traversal from a matched belief), not just from
// the direct candidate pool — this exercises the separate filter in the
// project-scoped BFS branch of query_relevant (lib.rs).
#[tokio::test]
async fn test_query_relevant_excludes_working_from_graph_expansion() {
    let svc = service().await;
    let ctx = TestCtx::new().await;
    let seed_term = Uuid::new_v4().simple().to_string();

    let seed = ctx.belief(format!("seedterm {seed_term}"), 0.6, 0.6);
    let working_neighbor = ctx
        .belief("unreachable working scratch note".to_string(), 0.6, 0.6)
        .with_memory_type(mimir_core::graph::MemoryType::Working);
    ctx.store.insert_belief(&seed).await.unwrap();
    ctx.store.insert_belief(&working_neighbor).await.unwrap();
    ctx.store
        .insert_edge(&Edge::new(seed.id, working_neighbor.id, EdgeType::Supports, 0.8).unwrap())
        .await
        .unwrap();

    let results = svc
        .query_relevant(&format!("seedterm {seed_term}"), 0, Some(&ctx.project))
        .await
        .unwrap();
    assert!(
        results.iter().any(|b| b.id == seed.id),
        "seed itself should match"
    );
    assert!(
        !results.iter().any(|b| b.id == working_neighbor.id),
        "working belief reached via graph expansion leaked into query_relevant results"
    );

    ctx.cleanup().await;
}

// query_relevant's graph-expansion BFS (lib.rs) walks get_direct_downstream_by_project
// hop-by-hop so a node reached only via an out-of-scope intermediate is excluded —
// something get_downstream_beliefs's single unbounded query plus an endpoint-only
// filter cannot express (AGE has no per-hop-node WHERE for variable-length paths;
// verified live: `all(x IN list WHERE ...)` list predicates aren't supported by this
// AGE version at all, syntax error even outside of a path context).
#[tokio::test]
async fn test_query_relevant_excludes_beliefs_reachable_only_via_out_of_scope_bridge() {
    let svc = service().await;
    let ctx = TestCtx::new().await;
    let other_project = format!("_test-other-{}", Uuid::new_v4().simple());
    let seed_term = Uuid::new_v4().simple().to_string();

    // No shared vocabulary between seed/bridge/target: the token leg (the
    // only leg active — `service()` has no embeddings configured) must find
    // target ONLY via graph expansion, never via direct text match.
    let seed = ctx.belief(format!("seedterm {seed_term}"), 0.6, 0.6);
    let bridge = Belief::new_in_project(
        "unrelated bridging content zzqvax".to_string(),
        0.6,
        0.6,
        other_project.clone(),
    )
    .unwrap();
    let target = ctx.belief("wombat burrow ventilation shaft".to_string(), 0.6, 0.6);
    ctx.store.insert_belief(&seed).await.unwrap();
    ctx.store.insert_belief(&bridge).await.unwrap();
    ctx.store.insert_belief(&target).await.unwrap();
    ctx.store
        .insert_edge(&Edge::new(seed.id, bridge.id, EdgeType::Supports, 0.8).unwrap())
        .await
        .unwrap();
    ctx.store
        .insert_edge(&Edge::new(bridge.id, target.id, EdgeType::Supports, 0.8).unwrap())
        .await
        .unwrap();

    let results = svc
        .query_relevant(&format!("seedterm {seed_term}"), 0, Some(&ctx.project))
        .await
        .unwrap();
    assert!(
        results.iter().any(|b| b.id == seed.id),
        "seed itself should match"
    );
    assert!(
        !results.iter().any(|b| b.id == target.id),
        "target reachable only via an out-of-scope bridge leaked into scoped results"
    );

    ctx.cleanup().await;
    let _ = ctx.store.delete_project(&other_project).await;
}

// ---------------------------------------------------------------------------
// query_intervention (do-operator) — read-only counterfactual
// ---------------------------------------------------------------------------

// Acceptance criterion: query_intervention computes a projection but writes
// NOTHING back to the store. Graph T -CAUSES-> B; do(T = 1.0) projects a new
// value for B, but B's stored probability is unchanged after the call.
#[tokio::test]
async fn test_intervention_is_read_only() {
    let ctx = TestCtx::new().await;
    let svc = service().await;

    let t = ctx.belief(format!("do-T-{}", Uuid::new_v4()), 0.4, 0.9);
    let b = ctx.belief(format!("do-B-{}", Uuid::new_v4()), 0.4, 0.9);
    ctx.store.insert_belief(&t).await.unwrap();
    ctx.store.insert_belief(&b).await.unwrap();
    ctx.store
        .insert_edge(&Edge::new(t.id, b.id, EdgeType::Causes, 0.5).unwrap())
        .await
        .unwrap();

    let b_before = ctx
        .store
        .get_belief(b.id)
        .await
        .unwrap()
        .unwrap()
        .probability
        .value();

    let updates = svc.query_intervention(t.id, 1.0).await.unwrap();
    // B is a causal descendant and must be projected. Conjugate Beta (spec
    // Mimir.Beta): B prior (p=0.4,c=0.9) ⇒ κ=180.2, α₀=72.08. do(T=1.0) feeds a
    // CAUSES edge w=0.5: α += w·μ_T·UNIT = 2.0 ⇒ mean 74.08/182.2 ≈ 0.40659.
    let projected = updates
        .iter()
        .find(|(id, _)| *id == b.id)
        .map(|(_, p)| p.value());
    assert!(projected.is_some(), "B should appear in the projection");
    let proj = projected.unwrap();
    assert!(
        proj > 0.4,
        "do(T) must raise B above its 0.4 base, got {proj}"
    );
    assert!((proj - 0.406_586).abs() < 1e-4, "got {proj}");

    // The decisive check: the store row for B is UNCHANGED (no writeback).
    let b_after = ctx
        .store
        .get_belief(b.id)
        .await
        .unwrap()
        .unwrap()
        .probability
        .value();
    assert!(
        (b_after - b_before).abs() < 1e-12,
        "query_intervention must not mutate the store: {} -> {}",
        b_before,
        b_after
    );
    assert!(
        (b_after - 0.4).abs() < 1e-9,
        "B should still be its stored 0.4"
    );
    ctx.cleanup().await;
}

// Acceptance criterion: validation. A value outside [0,1] is rejected (the
// Probability::new guard fires before any store access).
#[tokio::test]
async fn test_intervention_rejects_out_of_range_value() {
    let svc = service().await;
    let r = svc.query_intervention(Uuid::new_v4(), 1.5).await;
    assert!(r.is_err(), "value > 1.0 must be rejected");
}

// Acceptance criterion: an unknown target id is an error (not a silent empty).
#[tokio::test]
async fn test_intervention_unknown_target_errors() {
    let svc = service().await;
    let r = svc.query_intervention(Uuid::new_v4(), 0.5).await;
    assert!(r.is_err(), "unknown target belief must error");
}

// ---------------------------------------------------------------------------
// Evidence edges (Phase 4 C-core) — grounding + non-interference
// ---------------------------------------------------------------------------

// THE LOAD-BEARING TEST: executable form of spec Mimir.Evidence
// propagate-evidence-invariant: propagate(g) ≡ propagate(g ⊎ overlay).
//
// Strategy: capture the propagation result on a bare belief graph (no GROUNDS
// edges), then add a GROUNDS overlay (C-coupling fires, raising α), then run
// propagation again. The two result sets must be identical — GROUNDS edges must
// not enter the belief↔belief inference substrate at all.
//
// We use a *separate* belief graph (fresh UUIDs) so this test is independent of
// the C-coupling test above.
#[tokio::test]
async fn test_evidence_does_not_perturb_propagation() {
    let ctx = TestCtx::new().await;
    let svc = service().await;

    let a = ctx.belief(format!("grnd-A-{}", Uuid::new_v4()), 0.8, 0.9);
    let b = ctx.belief(format!("grnd-B-{}", Uuid::new_v4()), 0.3, 0.8);
    ctx.store.insert_belief(&a).await.unwrap();
    ctx.store.insert_belief(&b).await.unwrap();
    ctx.store
        .insert_edge(&Edge::new(a.id, b.id, EdgeType::Supports, 0.5).unwrap())
        .await
        .unwrap();

    // Phase 1: propagate on the BARE graph (no evidence overlay yet).
    let bare_updates = svc.propagate_from(a.id).await.unwrap();
    assert!(
        !bare_updates.is_empty(),
        "bare propagation must produce at least one update"
    );
    // Collect (belief_id → new_alpha) from the bare run so we can compare.
    let bare_map: std::collections::HashMap<uuid::Uuid, f64> =
        bare_updates.iter().map(|u| (u.0, u.1.value())).collect();

    // Phase 2: add a GROUNDS overlay — C-coupling intentionally raises α on a
    // and b. This must NOT affect how propagate_from routes support/defeat edges.
    let chunk = ctx.chunk(
        "evidence-doc.md",
        "a grounding passage for the non-interference test",
    );
    ctx.store.insert_document_chunk(&chunk).await.unwrap();
    svc.add_evidence(b.id, chunk.id, 0.9).await.unwrap();
    svc.add_evidence(a.id, chunk.id, 0.5).await.unwrap();

    // Reset A and B back to their initial (α,β) so both propagation runs start
    // from identical belief state. We're testing routing (are GROUNDS edges
    // invisible to the inference traversal?), not that C-coupling is a no-op.
    ctx.store
        .update_belief_beta(a.id, a.alpha, a.beta)
        .await
        .unwrap();
    ctx.store
        .update_belief_beta(b.id, b.alpha, b.beta)
        .await
        .unwrap();

    // Re-run propagation from a with the GROUNDS overlay present.
    let overlay_updates = svc.propagate_from(a.id).await.unwrap();

    // The belief→belief inference result must be identical: same set of target
    // IDs and same computed α values. GROUNDS edges must be invisible to
    // propagation (non-interference).
    let overlay_map: std::collections::HashMap<uuid::Uuid, f64> =
        overlay_updates.iter().map(|u| (u.0, u.1.value())).collect();

    assert_eq!(
        bare_map.keys().collect::<std::collections::HashSet<_>>(),
        overlay_map.keys().collect::<std::collections::HashSet<_>>(),
        "propagation must update the same belief IDs with and without GROUNDS overlay"
    );
    for (id, &bare_alpha) in &bare_map {
        let overlay_alpha = overlay_map[id];
        assert!(
            (bare_alpha - overlay_alpha).abs() < 1e-12,
            "belief {id}: bare α={bare_alpha} but overlay α={overlay_alpha}; \
             GROUNDS edges must not perturb propagation routing"
        );
    }
    ctx.cleanup().await;
}

// C-coupling: add_evidence must raise α on the target belief.
#[tokio::test]
async fn test_add_evidence_raises_alpha() {
    let ctx = TestCtx::new().await;
    let svc = service().await;

    let b = ctx.belief(format!("coupling-{}", Uuid::new_v4()), 0.7, 0.8);
    ctx.store.insert_belief(&b).await.unwrap();
    let alpha_before = b.alpha;

    let chunk = ctx.chunk("coupling-doc.md", "grounding passage for coupling test");
    ctx.store.insert_document_chunk(&chunk).await.unwrap();
    svc.add_evidence(b.id, chunk.id, 0.8).await.unwrap();

    let b_after = ctx.store.get_belief(b.id).await.unwrap().unwrap();
    assert!(
        b_after.alpha > alpha_before,
        "add_evidence must raise α (C-coupling): before={alpha_before}, after={}",
        b_after.alpha
    );
    assert_eq!(
        b_after.beta, b.beta,
        "add_evidence must not change β: before={}, after={}",
        b.beta, b_after.beta
    );
    ctx.cleanup().await;
}

// add_evidence creates a GROUNDS edge; query_relevant_grounded returns the
// belief with its grounding passage.
#[tokio::test]
async fn test_add_and_query_grounded() {
    let ctx = TestCtx::new().await;
    let svc = service().await;

    let token = format!("zqxgrounded{}", Uuid::new_v4().simple());
    let b = ctx.belief(format!("a belief about {}", token), 0.7, 0.8);
    ctx.store.insert_belief(&b).await.unwrap();
    let chunk = DocumentChunk::new(
        "src.md".to_string(),
        vec!["Section One".to_string()],
        "the passage that grounds the belief".to_string(),
        None,
        Some(ctx.project.clone()),
    );
    ctx.store.insert_document_chunk(&chunk).await.unwrap();
    svc.add_evidence(b.id, chunk.id, 0.8).await.unwrap();

    let grounded = svc
        .query_relevant_grounded(&token, 10, 3, None)
        .await
        .unwrap();
    let gb = grounded
        .iter()
        .find(|g| g.belief.id == b.id)
        .expect("belief should be retrieved by its unique token");
    assert_eq!(gb.evidence.len(), 1, "one grounding passage expected");
    let e = &gb.evidence[0];
    assert!(e.snippet.contains("grounds the belief"));
    assert!((e.weight - 0.8).abs() < 1e-9);
    assert_eq!(e.section_path, vec!["Section One".to_string()]);
    ctx.cleanup().await;
}

// delete_belief leaves no dangling GROUNDS edge (DETACH DELETE).
#[tokio::test]
async fn test_delete_belief_removes_grounds_edge() {
    let ctx = TestCtx::new().await;
    let svc = service().await;

    let b = ctx.belief(format!("grnd-del-{}", Uuid::new_v4()), 0.5, 0.5);
    ctx.store.insert_belief(&b).await.unwrap();
    let chunk = ctx.chunk("d.md", "passage");
    ctx.store.insert_document_chunk(&chunk).await.unwrap();
    svc.add_evidence(b.id, chunk.id, 1.0).await.unwrap();

    assert_eq!(
        ctx.store
            .get_evidence_for_beliefs(&[b.id])
            .await
            .unwrap()
            .len(),
        1
    );
    assert!(svc.delete_belief(b.id).await.unwrap());
    assert_eq!(
        ctx.store
            .get_evidence_for_beliefs(&[b.id])
            .await
            .unwrap()
            .len(),
        0,
        "deleting the belief must remove its GROUNDS edges"
    );
    ctx.cleanup().await;
}

// REGRESSION (#1, spec Mimir.Beta evidence completeness): a belief's evidence
// from a parent OUTSIDE the triggering seed's subgraph must NOT be erased when
// propagation is triggered from a different seed.
//
// Graph: X -SUPPORTS-> T  and  Y -SUPPORTS-> T  (X and Y otherwise unconnected).
// get_downstream_beliefs(Y) reaches T but NOT X, so X is out-of-subgraph when
// propagating from Y. After propagate_from(Y), T must still carry X's support
// (its α must reflect BOTH supporters), not be reset to prior + Y only.
#[tokio::test]
async fn test_propagate_preserves_out_of_subgraph_evidence() {
    let ctx = TestCtx::new().await;
    let svc = service().await;

    let x = ctx.belief(format!("oosX-{}", Uuid::new_v4()), 0.9, 0.5);
    let y = ctx.belief(format!("oosY-{}", Uuid::new_v4()), 0.9, 0.5);
    let t = ctx.belief(format!("oosT-{}", Uuid::new_v4()), 0.3, 0.5);
    ctx.store.insert_belief(&x).await.unwrap();
    ctx.store.insert_belief(&y).await.unwrap();
    ctx.store.insert_belief(&t).await.unwrap();
    let t_alpha0 = t.alpha;

    svc.add_edge(x.id, t.id, EdgeType::Supports, 1.0)
        .await
        .unwrap();
    svc.add_edge(y.id, t.id, EdgeType::Supports, 1.0)
        .await
        .unwrap();

    // Propagate from X → T gains X's support.
    svc.propagate_from(x.id).await.unwrap();
    let t_after_x = ctx.store.get_belief(t.id).await.unwrap().unwrap().alpha;
    assert!(
        t_after_x > t_alpha0 + 1e-9,
        "X's support must raise T's α: α0={t_alpha0}, after X={t_after_x}"
    );

    // Propagate from Y. X is OUT of Y's subgraph. With the fix T re-derives from
    // ALL incoming edges (X external + Y), so X's support is preserved.
    svc.propagate_from(y.id).await.unwrap();
    let t_after_y = ctx.store.get_belief(t.id).await.unwrap().unwrap().alpha;

    // T must reflect BOTH supporters — α at least the X-only value (the buggy
    // code reset it to prior + Y only, LOSING X, i.e. t_after_y == t_after_x's
    // pre-X baseline). With both counted, α ≥ the single-supporter value.
    assert!(
        t_after_y >= t_after_x - 1e-9,
        "out-of-subgraph support (X) was erased: after_X={t_after_x}, after_Y={t_after_y}"
    );
    assert!(
        t_after_y > t_alpha0 + 1e-9,
        "T must stay above its prior after propagation: α0={t_alpha0}, after_Y={t_after_y}"
    );
    ctx.cleanup().await;
}

// REGRESSION (spec Mimir.Graph propagation scope / defeat-target-is-reached):
// a bare S -DEFEATS-> T (T otherwise unconnected) must LOWER T's mean. Before
// the propagation-scope fix, get_downstream_beliefs followed only SUPPORTS/CAUSES,
// so T was never in the recompute set and the defeat was inert.
#[tokio::test]
async fn test_bare_defeat_lowers_target() {
    let ctx = TestCtx::new().await;
    let svc = service().await;

    let seed = ctx.belief(format!("defS-{}", Uuid::new_v4()), 0.9, 0.9);
    let t = ctx.belief(format!("defT-{}", Uuid::new_v4()), 0.6, 0.5);
    ctx.store.insert_belief(&seed).await.unwrap();
    ctx.store.insert_belief(&t).await.unwrap();
    let t_beta0 = t.beta;
    let t_mean0 = t.probability.value();

    // add_edge(DEFEATS) auto-triggers propagate_from(seed). T is reachable from
    // seed ONLY via this DEFEATS edge — the previously-inert case.
    svc.add_edge(seed.id, t.id, EdgeType::Defeats, 1.0)
        .await
        .unwrap();

    let got = ctx.store.get_belief(t.id).await.unwrap().unwrap();
    // Defeat adds to β (spec defeat-anti): β grew, mean dropped below its base.
    assert!(
        got.beta > t_beta0 + 1e-9,
        "defeat must raise T's β: β0={t_beta0}, after={}",
        got.beta
    );
    assert!(
        got.probability.value() < t_mean0 - 1e-9,
        "defeat must lower T's mean: m0={t_mean0}, after={}",
        got.probability.value()
    );
    ctx.cleanup().await;
}

// REGRESSION (spec Mimir.Inference keep-causes-into-nontarget): under do(T), a
// CAUSES co-cause X→M where X is OUTSIDE T's causal-descendant set must still
// count in M's projection (surgery cuts only edges INTO T, never into M).
// Before the fix, intervene used an empty external_means and dropped X→M.
#[tokio::test]
async fn test_intervene_counts_out_of_set_cocause() {
    let ctx = TestCtx::new().await;
    let svc = service().await;

    // T -CAUSES-> M ; X -CAUSES-> M.  X is NOT a causal descendant of T.
    let t = ctx.belief(format!("ccT-{}", Uuid::new_v4()), 0.3, 0.9);
    let m = ctx.belief(format!("ccM-{}", Uuid::new_v4()), 0.3, 0.9);
    let x = ctx.belief(format!("ccX-{}", Uuid::new_v4()), 0.95, 0.9);
    ctx.store.insert_belief(&t).await.unwrap();
    ctx.store.insert_belief(&m).await.unwrap();
    ctx.store.insert_belief(&x).await.unwrap();
    svc.add_edge(t.id, m.id, EdgeType::Causes, 0.5)
        .await
        .unwrap();
    svc.add_edge(x.id, m.id, EdgeType::Causes, 0.5)
        .await
        .unwrap();

    let proj = svc.query_intervention(t.id, 1.0).await.unwrap();
    let m_with_x = proj
        .iter()
        .find(|(id, _)| *id == m.id)
        .map(|(_, p)| p.value())
        .expect("M should be projected");

    // Now remove X's edge and re-run: M's projection should be LOWER, proving X's
    // co-cause contributed in the first run (it was not dropped).
    svc.delete_belief(x.id).await.unwrap(); // DETACH DELETE removes X→M
    let proj2 = svc.query_intervention(t.id, 1.0).await.unwrap();
    let m_without_x = proj2
        .iter()
        .find(|(id, _)| *id == m.id)
        .map(|(_, p)| p.value())
        .expect("M still projected via T");

    assert!(
        m_with_x > m_without_x + 1e-9,
        "out-of-set co-cause X must raise M's projection: with X={m_with_x}, without={m_without_x}"
    );
    ctx.cleanup().await;
}

// ---------------------------------------------------------------------------
// sweep_expired_defeated (attenuated deletion)
// docs/proposals/80-memory-evolution-open-questions.md, section 1.
//
// These tests bypass svc.add_edge's auto-propagation (which would recompute
// the defeated belief's Beta state from the defeat itself) by inserting the
// DEFEATS edge directly via store.insert_edge, then forcing an exact
// probability via update_beliefs_beta. This isolates the sweep's own
// threshold/grace-period/project-scoping logic from defeat-attenuation math,
// which is already covered by test_bare_defeat_lowers_target.
// ---------------------------------------------------------------------------

#[tokio::test]
async fn test_sweep_expired_defeated_deletes_low_prob_past_grace() {
    let ctx = TestCtx::new().await;
    let svc = service().await;

    let defeater = ctx.belief(format!("sweepA-{}", Uuid::new_v4()), 0.9, 0.9);
    let defeated = ctx.belief(format!("sweepB-{}", Uuid::new_v4()), 0.9, 0.9);
    ctx.store.insert_belief(&defeater).await.unwrap();
    ctx.store.insert_belief(&defeated).await.unwrap();
    ctx.store
        .insert_edge(&Edge::new(defeater.id, defeated.id, EdgeType::Defeats, 1.0).unwrap())
        .await
        .unwrap();
    // Force a low probability directly (alpha=1, beta=99 -> mean=0.01),
    // independent of whatever propagate_from would have computed.
    ctx.store
        .update_beliefs_beta(&[(defeated.id, 1.0, 99.0)])
        .await
        .unwrap();

    // grace_hours=0.0: the defeat "just happened" (defeater's created_at is
    // ~now), so even a zero-length grace period has elapsed.
    let deleted = svc
        .sweep_expired_defeated(0.3, 0.0, Some(&ctx.project))
        .await
        .unwrap();
    assert_eq!(deleted, 1);
    assert!(
        ctx.store.get_belief(defeated.id).await.unwrap().is_none(),
        "defeated belief should have been deleted"
    );
    ctx.cleanup().await;
}

#[tokio::test]
async fn test_sweep_expired_defeated_keeps_within_grace_period() {
    let ctx = TestCtx::new().await;
    let svc = service().await;

    let defeater = ctx.belief(format!("sweepC-{}", Uuid::new_v4()), 0.9, 0.9);
    let defeated = ctx.belief(format!("sweepD-{}", Uuid::new_v4()), 0.9, 0.9);
    ctx.store.insert_belief(&defeater).await.unwrap();
    ctx.store.insert_belief(&defeated).await.unwrap();
    ctx.store
        .insert_edge(&Edge::new(defeater.id, defeated.id, EdgeType::Defeats, 1.0).unwrap())
        .await
        .unwrap();
    ctx.store
        .update_beliefs_beta(&[(defeated.id, 1.0, 99.0)])
        .await
        .unwrap();

    // grace_hours=24.0: the defeat just happened, well within a 24h window —
    // must NOT be deleted yet, even though probability is already low.
    let deleted = svc
        .sweep_expired_defeated(0.3, 24.0, Some(&ctx.project))
        .await
        .unwrap();
    assert_eq!(deleted, 0);
    assert!(
        ctx.store.get_belief(defeated.id).await.unwrap().is_some(),
        "defeated belief must survive within its grace period"
    );
    ctx.cleanup().await;
}

#[tokio::test]
async fn test_sweep_expired_defeated_keeps_above_threshold() {
    let ctx = TestCtx::new().await;
    let svc = service().await;

    let defeater = ctx.belief(format!("sweepE-{}", Uuid::new_v4()), 0.9, 0.9);
    let defeated = ctx.belief(format!("sweepF-{}", Uuid::new_v4()), 0.9, 0.9);
    ctx.store.insert_belief(&defeater).await.unwrap();
    ctx.store.insert_belief(&defeated).await.unwrap();
    ctx.store
        .insert_edge(&Edge::new(defeater.id, defeated.id, EdgeType::Defeats, 1.0).unwrap())
        .await
        .unwrap();
    // High probability (alpha=99, beta=1 -> mean=0.99) despite being defeated
    // — e.g. a low-weight defeat that barely attenuated the target.
    ctx.store
        .update_beliefs_beta(&[(defeated.id, 99.0, 1.0)])
        .await
        .unwrap();

    let deleted = svc
        .sweep_expired_defeated(0.3, 0.0, Some(&ctx.project))
        .await
        .unwrap();
    assert_eq!(deleted, 0);
    assert!(
        ctx.store.get_belief(defeated.id).await.unwrap().is_some(),
        "belief above the probability threshold must not be deleted regardless of grace period"
    );
    ctx.cleanup().await;
}

#[tokio::test]
async fn test_sweep_expired_defeated_is_project_scoped() {
    // Two independent projects, each with an eligible-for-deletion pair. A
    // sweep scoped to ctx_a's project must delete ONLY ctx_a's belief and
    // leave ctx_b's untouched — this is the whole reason sweep_expired_defeated
    // takes a project filter instead of always operating on the entire graph.
    let ctx_a = TestCtx::new().await;
    let ctx_b = TestCtx::new().await;
    let svc = service().await;

    let defeater_a = ctx_a.belief(format!("sweepG-{}", Uuid::new_v4()), 0.9, 0.9);
    let defeated_a = ctx_a.belief(format!("sweepH-{}", Uuid::new_v4()), 0.9, 0.9);
    ctx_a.store.insert_belief(&defeater_a).await.unwrap();
    ctx_a.store.insert_belief(&defeated_a).await.unwrap();
    ctx_a
        .store
        .insert_edge(&Edge::new(defeater_a.id, defeated_a.id, EdgeType::Defeats, 1.0).unwrap())
        .await
        .unwrap();
    ctx_a
        .store
        .update_beliefs_beta(&[(defeated_a.id, 1.0, 99.0)])
        .await
        .unwrap();

    let defeater_b = ctx_b.belief(format!("sweepI-{}", Uuid::new_v4()), 0.9, 0.9);
    let defeated_b = ctx_b.belief(format!("sweepJ-{}", Uuid::new_v4()), 0.9, 0.9);
    ctx_b.store.insert_belief(&defeater_b).await.unwrap();
    ctx_b.store.insert_belief(&defeated_b).await.unwrap();
    ctx_b
        .store
        .insert_edge(&Edge::new(defeater_b.id, defeated_b.id, EdgeType::Defeats, 1.0).unwrap())
        .await
        .unwrap();
    ctx_b
        .store
        .update_beliefs_beta(&[(defeated_b.id, 1.0, 99.0)])
        .await
        .unwrap();

    let deleted = svc
        .sweep_expired_defeated(0.3, 0.0, Some(&ctx_a.project))
        .await
        .unwrap();
    assert_eq!(deleted, 1, "sweep must delete exactly ctx_a's eligible belief");
    assert!(ctx_a.store.get_belief(defeated_a.id).await.unwrap().is_none());
    assert!(
        ctx_b.store.get_belief(defeated_b.id).await.unwrap().is_some(),
        "sweep scoped to ctx_a's project must not touch ctx_b's belief"
    );

    ctx_a.cleanup().await;
    ctx_b.cleanup().await;
}
