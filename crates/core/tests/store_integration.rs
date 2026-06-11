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
        pgbouncer: false,
        max_connections: 10,
    }
}

async fn store() -> AgeStore {
    let cfg = test_db_config();
    let graph_name = cfg.dbname.clone();
    let pool = db::connect(&cfg).await.expect("connect");
    AgeStore::new(pool, graph_name)
}

// ---------------------------------------------------------------------------
// Belief CRUD
// ---------------------------------------------------------------------------

#[tokio::test]
async fn test_insert_and_get_belief() {
    let s = store().await;
    let b = Belief::new(format!("belief-{}", Uuid::new_v4()), 0.75, 0.85).unwrap();
    s.insert_belief(&b).await.expect("insert_belief");
    let got = s
        .get_belief(b.id)
        .await
        .expect("get_belief")
        .expect("should exist");
    assert_eq!(got.id, b.id);
    assert_eq!(got.content, b.content);
    assert!((got.probability.value() - 0.75).abs() < 1e-9);
    assert!((got.confidence.value() - 0.85).abs() < 1e-9);
}

#[tokio::test]
async fn test_get_nonexistent_belief_returns_none() {
    let s = store().await;
    let result = s.get_belief(Uuid::new_v4()).await.expect("get_belief");
    assert!(result.is_none());
}

#[tokio::test]
async fn test_list_beliefs_contains_inserted() {
    let s = store().await;
    let b = Belief::new(format!("list-{}", Uuid::new_v4()), 0.5, 0.5).unwrap();
    s.insert_belief(&b).await.unwrap();
    let all = s.list_beliefs().await.unwrap();
    assert!(all.iter().any(|x| x.id == b.id));
}

#[tokio::test]
async fn test_list_beliefs_multiple() {
    let s = store().await;
    let ids: Vec<Uuid> = (0..5)
        .map(|i| {
            let b = Belief::new(format!("multi-{}-{}", i, Uuid::new_v4()), 0.5, 0.5).unwrap();
            b.id
        })
        .collect();
    // Re-create to get owned beliefs for insertion
    let mut inserted = Vec::new();
    for i in 0..5 {
        let b = Belief::new(format!("multi-{}-{}", i, Uuid::new_v4()), 0.5, 0.5).unwrap();
        s.insert_belief(&b).await.unwrap();
        inserted.push(b.id);
    }
    let all = s.list_beliefs().await.unwrap();
    for id in &inserted {
        assert!(all.iter().any(|x| x.id == *id), "missing {}", id);
    }
    let _ = ids; // suppress unused warning
}

// Phase 3 (spec Mimir.Graph: RETIRED SCALAR SETTERS): the old field-independent
// setters update_belief_probability / update_belief_confidence are retired —
// belief state is written only via the Beta posterior (update_belief_beta), so
// the tests that asserted the old scalar contract are removed.

#[tokio::test]
async fn test_update_belief_beta_round_trips_mean_and_strength() {
    let s = store().await;
    let b = Belief::new(format!("upd-beta-{}", Uuid::new_v4()), 0.5, 0.5).unwrap();
    s.insert_belief(&b).await.unwrap();
    // A strong support posterior: mean 0.9 at strength 100 ⇒ (α,β)=(90,10).
    s.update_belief_beta(b.id, 90.0, 10.0).await.unwrap();
    let got = s.get_belief(b.id).await.unwrap().unwrap();
    // Durable (α,β) persisted (spec store-load-round-trip); mean derived = 0.9.
    assert!(
        (got.alpha - 90.0).abs() < 1e-6,
        "α persisted: {}",
        got.alpha
    );
    assert!((got.beta - 10.0).abs() < 1e-6, "β persisted: {}", got.beta);
    assert!((got.probability.value() - 0.9).abs() < 1e-9);
}

#[tokio::test]
async fn test_belief_boundary_probabilities() {
    let s = store().await;
    let b = Belief::new(format!("bound-{}", Uuid::new_v4()), 0.0, 1.0).unwrap();
    s.insert_belief(&b).await.unwrap();
    let got = s.get_belief(b.id).await.unwrap().unwrap();
    assert!((got.probability.value() - 0.0).abs() < 1e-9);
    assert!((got.confidence.value() - 1.0).abs() < 1e-9);
}

#[tokio::test]
async fn test_belief_content_with_special_chars() {
    let s = store().await;
    // Content with apostrophe — exercises the esc() helper
    let b = Belief::new(
        format!("it's a test with 'quotes' and more-{}", Uuid::new_v4()),
        0.6,
        0.7,
    )
    .unwrap();
    s.insert_belief(&b).await.unwrap();
    let got = s.get_belief(b.id).await.unwrap().unwrap();
    assert_eq!(got.content, b.content);
}

#[tokio::test]
async fn test_belief_content_with_unicode() {
    let s = store().await;
    let b = Belief::new(
        format!("信念 belief Überzeugung -{}", Uuid::new_v4()),
        0.7,
        0.8,
    )
    .unwrap();
    s.insert_belief(&b).await.unwrap();
    let got = s.get_belief(b.id).await.unwrap().unwrap();
    assert_eq!(got.content, b.content);
}

// ---------------------------------------------------------------------------
// Pattern CRUD
// ---------------------------------------------------------------------------

#[tokio::test]
async fn test_insert_and_list_patterns() {
    let s = store().await;
    let p = Pattern::new(
        format!("situation-{}", Uuid::new_v4()),
        format!("approach-{}", Uuid::new_v4()),
        0.8,
    )
    .unwrap();
    s.insert_pattern(&p).await.unwrap();
    let all = s.list_patterns().await.unwrap();
    assert!(all.iter().any(|x| x.id == p.id));
}

#[tokio::test]
async fn test_list_patterns_multiple() {
    let s = store().await;
    let mut inserted = Vec::new();
    for i in 0..3 {
        let p = Pattern::new(
            format!("sit-{}-{}", i, Uuid::new_v4()),
            format!("app-{}-{}", i, Uuid::new_v4()),
            0.5 + i as f64 * 0.1,
        )
        .unwrap();
        s.insert_pattern(&p).await.unwrap();
        inserted.push(p.id);
    }
    let all = s.list_patterns().await.unwrap();
    for id in &inserted {
        assert!(all.iter().any(|x| x.id == *id));
    }
}

#[tokio::test]
async fn test_pattern_boundary_success_rate() {
    let s = store().await;
    let p = Pattern::new(
        format!("sit-{}", Uuid::new_v4()),
        "approach".to_string(),
        1.0,
    )
    .unwrap();
    s.insert_pattern(&p).await.unwrap();
    let all = s.list_patterns().await.unwrap();
    let got = all.iter().find(|x| x.id == p.id).unwrap();
    assert!((got.success_rate.value() - 1.0).abs() < 1e-9);
}

// ---------------------------------------------------------------------------
// Edges
// ---------------------------------------------------------------------------

#[tokio::test]
async fn test_insert_edge_supports() {
    let s = store().await;
    let b1 = Belief::new(format!("cause-{}", Uuid::new_v4()), 0.8, 0.9).unwrap();
    let b2 = Belief::new(format!("effect-{}", Uuid::new_v4()), 0.7, 0.8).unwrap();
    s.insert_belief(&b1).await.unwrap();
    s.insert_belief(&b2).await.unwrap();
    let edge = Edge::new(b1.id, b2.id, EdgeType::Supports, 0.9).unwrap();
    s.insert_edge(&edge).await.unwrap();
    let downstream = s.get_downstream_beliefs(b1.id).await.unwrap();
    assert!(downstream.iter().any(|b| b.id == b2.id));
}

#[tokio::test]
async fn test_insert_edge_causes() {
    let s = store().await;
    let b1 = Belief::new(format!("cause-{}", Uuid::new_v4()), 0.8, 0.9).unwrap();
    let b2 = Belief::new(format!("effect-{}", Uuid::new_v4()), 0.7, 0.8).unwrap();
    s.insert_belief(&b1).await.unwrap();
    s.insert_belief(&b2).await.unwrap();
    let edge = Edge::new(b1.id, b2.id, EdgeType::Causes, 0.8).unwrap();
    s.insert_edge(&edge).await.unwrap();
    let downstream = s.get_downstream_beliefs(b1.id).await.unwrap();
    assert!(downstream.iter().any(|b| b.id == b2.id));
}

#[tokio::test]
async fn test_insert_edge_defeats() {
    let s = store().await;
    let b1 = Belief::new(format!("defeater-{}", Uuid::new_v4()), 0.9, 0.9).unwrap();
    let b2 = Belief::new(format!("defeated-{}", Uuid::new_v4()), 0.8, 0.8).unwrap();
    s.insert_belief(&b1).await.unwrap();
    s.insert_belief(&b2).await.unwrap();
    let edge = Edge::new(b1.id, b2.id, EdgeType::Defeats, 1.0).unwrap();
    s.insert_edge(&edge).await.unwrap();
    // Edge stored — verify via get_edges_among
    let edges = s.get_edges_among(&[b1.id, b2.id]).await.unwrap();
    assert!(edges
        .iter()
        .any(|(f, t, et, _)| *f == b1.id && *t == b2.id && *et == EdgeType::Defeats));
}

#[tokio::test]
async fn test_insert_edge_missing_source_fails() {
    let s = store().await;
    let b = Belief::new(format!("only-{}", Uuid::new_v4()), 0.5, 0.5).unwrap();
    s.insert_belief(&b).await.unwrap();
    // from_id is a random UUID that was never inserted
    let edge = Edge::new(Uuid::new_v4(), b.id, EdgeType::Supports, 0.5).unwrap();
    let result = s.insert_edge(&edge).await;
    assert!(result.is_err());
}

#[tokio::test]
async fn test_insert_edge_missing_target_fails() {
    let s = store().await;
    let b = Belief::new(format!("only-{}", Uuid::new_v4()), 0.5, 0.5).unwrap();
    s.insert_belief(&b).await.unwrap();
    let edge = Edge::new(b.id, Uuid::new_v4(), EdgeType::Supports, 0.5).unwrap();
    let result = s.insert_edge(&edge).await;
    assert!(result.is_err());
}

// ---------------------------------------------------------------------------
// Contradictions
// ---------------------------------------------------------------------------

#[tokio::test]
async fn test_contradicts_bidirectional() {
    let s = store().await;
    let b1 = Belief::new(format!("contra-a-{}", Uuid::new_v4()), 0.6, 0.7).unwrap();
    let b2 = Belief::new(format!("contra-b-{}", Uuid::new_v4()), 0.4, 0.6).unwrap();
    s.insert_belief(&b1).await.unwrap();
    s.insert_belief(&b2).await.unwrap();
    let w = Probability::new(0.95).unwrap();
    s.insert_contradicts(b1.id, b2.id, w).await.unwrap();
    let pairs = s.get_contradiction_pairs().await.unwrap();
    assert!(pairs.iter().any(|(a, b)| *a == b1.id && *b == b2.id));
    assert!(pairs.iter().any(|(a, b)| *a == b2.id && *b == b1.id));
}

#[tokio::test]
async fn test_no_contradiction_without_edge() {
    let s = store().await;
    let b1 = Belief::new(format!("nocont-a-{}", Uuid::new_v4()), 0.6, 0.7).unwrap();
    let b2 = Belief::new(format!("nocont-b-{}", Uuid::new_v4()), 0.6, 0.7).unwrap();
    s.insert_belief(&b1).await.unwrap();
    s.insert_belief(&b2).await.unwrap();
    let pairs = s.get_contradiction_pairs().await.unwrap();
    let has = pairs
        .iter()
        .any(|(a, b)| (*a == b1.id && *b == b2.id) || (*a == b2.id && *b == b1.id));
    assert!(!has);
}

// ---------------------------------------------------------------------------
// get_edges_among
// ---------------------------------------------------------------------------

#[tokio::test]
async fn test_get_edges_among_two_edges() {
    let s = store().await;
    let b1 = Belief::new(format!("ea-{}", Uuid::new_v4()), 0.8, 0.9).unwrap();
    let b2 = Belief::new(format!("eb-{}", Uuid::new_v4()), 0.7, 0.8).unwrap();
    let b3 = Belief::new(format!("ec-{}", Uuid::new_v4()), 0.6, 0.7).unwrap();
    s.insert_belief(&b1).await.unwrap();
    s.insert_belief(&b2).await.unwrap();
    s.insert_belief(&b3).await.unwrap();
    s.insert_edge(&Edge::new(b1.id, b2.id, EdgeType::Supports, 0.9).unwrap())
        .await
        .unwrap();
    s.insert_edge(&Edge::new(b2.id, b3.id, EdgeType::Causes, 0.7).unwrap())
        .await
        .unwrap();

    let edges = s.get_edges_among(&[b1.id, b2.id, b3.id]).await.unwrap();
    assert!(edges
        .iter()
        .any(|(f, t, et, _)| *f == b1.id && *t == b2.id && *et == EdgeType::Supports));
    assert!(edges
        .iter()
        .any(|(f, t, et, _)| *f == b2.id && *t == b3.id && *et == EdgeType::Causes));
}

#[tokio::test]
async fn test_get_edges_among_empty_input() {
    let s = store().await;
    let edges = s.get_edges_among(&[]).await.unwrap();
    assert!(edges.is_empty());
}

#[tokio::test]
async fn test_get_edges_among_excludes_outside_set() {
    let s = store().await;
    let b1 = Belief::new(format!("excl-a-{}", Uuid::new_v4()), 0.8, 0.9).unwrap();
    let b2 = Belief::new(format!("excl-b-{}", Uuid::new_v4()), 0.7, 0.8).unwrap();
    let b3 = Belief::new(format!("excl-c-{}", Uuid::new_v4()), 0.6, 0.7).unwrap();
    s.insert_belief(&b1).await.unwrap();
    s.insert_belief(&b2).await.unwrap();
    s.insert_belief(&b3).await.unwrap();
    s.insert_edge(&Edge::new(b1.id, b3.id, EdgeType::Supports, 0.9).unwrap())
        .await
        .unwrap();

    // Only ask about b1 and b2 — the b1→b3 edge should not appear
    let edges = s.get_edges_among(&[b1.id, b2.id]).await.unwrap();
    assert!(!edges.iter().any(|(_, t, _, _)| *t == b3.id));
}

// ---------------------------------------------------------------------------
// get_downstream_beliefs
// ---------------------------------------------------------------------------

#[tokio::test]
async fn test_get_downstream_via_causes() {
    let s = store().await;
    let b1 = Belief::new(format!("dn-cause-{}", Uuid::new_v4()), 0.8, 0.9).unwrap();
    let b2 = Belief::new(format!("dn-effect-{}", Uuid::new_v4()), 0.6, 0.7).unwrap();
    s.insert_belief(&b1).await.unwrap();
    s.insert_belief(&b2).await.unwrap();
    s.insert_edge(&Edge::new(b1.id, b2.id, EdgeType::Causes, 0.8).unwrap())
        .await
        .unwrap();
    let downstream = s.get_downstream_beliefs(b1.id).await.unwrap();
    assert!(downstream.iter().any(|b| b.id == b2.id));
}

#[tokio::test]
async fn test_get_downstream_no_edges_empty() {
    let s = store().await;
    let b = Belief::new(format!("isolated-{}", Uuid::new_v4()), 0.5, 0.5).unwrap();
    s.insert_belief(&b).await.unwrap();
    let downstream = s.get_downstream_beliefs(b.id).await.unwrap();
    assert!(!downstream.iter().any(|x| x.id == b.id)); // self not included
}

#[tokio::test]
async fn test_get_downstream_multi_hop() {
    let s = store().await;
    let b1 = Belief::new(format!("hop1-{}", Uuid::new_v4()), 0.9, 0.9).unwrap();
    let b2 = Belief::new(format!("hop2-{}", Uuid::new_v4()), 0.8, 0.8).unwrap();
    let b3 = Belief::new(format!("hop3-{}", Uuid::new_v4()), 0.7, 0.7).unwrap();
    s.insert_belief(&b1).await.unwrap();
    s.insert_belief(&b2).await.unwrap();
    s.insert_belief(&b3).await.unwrap();
    s.insert_edge(&Edge::new(b1.id, b2.id, EdgeType::Supports, 0.9).unwrap())
        .await
        .unwrap();
    s.insert_edge(&Edge::new(b2.id, b3.id, EdgeType::Supports, 0.8).unwrap())
        .await
        .unwrap();
    let downstream = s.get_downstream_beliefs(b1.id).await.unwrap();
    assert!(downstream.iter().any(|b| b.id == b2.id));
    assert!(downstream.iter().any(|b| b.id == b3.id));
}

// ---------------------------------------------------------------------------
// query_intervention (do-operator) — read-only counterfactual
// ---------------------------------------------------------------------------

async fn service() -> MimirService {
    let cfg = Config {
        database: test_db_config(),
        embeddings: None,
    };
    MimirService::connect(&cfg).await.expect("connect service")
}

// Acceptance criterion: query_intervention computes a projection but writes
// NOTHING back to the store. Graph T -CAUSES-> B; do(T = 1.0) projects a new
// value for B, but B's stored probability is unchanged after the call.
#[tokio::test]
async fn test_intervention_is_read_only() {
    let s = store().await;
    let svc = service().await;

    let t = Belief::new(format!("do-T-{}", Uuid::new_v4()), 0.4, 0.9).unwrap();
    let b = Belief::new(format!("do-B-{}", Uuid::new_v4()), 0.4, 0.9).unwrap();
    s.insert_belief(&t).await.unwrap();
    s.insert_belief(&b).await.unwrap();
    s.insert_edge(&Edge::new(t.id, b.id, EdgeType::Causes, 0.5).unwrap())
        .await
        .unwrap();

    let b_before = s
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
    let b_after = s
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

fn sorted_updates(mut v: Vec<(Uuid, Probability)>) -> Vec<(Uuid, f64)> {
    v.sort_by_key(|a| a.0);
    v.into_iter().map(|(id, p)| (id, p.value())).collect()
}

// THE LOAD-BEARING TEST: the executable form of the non-interference theorem.
// Seed a belief graph, capture propagate_from output, reset, overlay GROUNDS
// edges + a DocumentChunk, and assert propagate_from output is bit-identical.
#[tokio::test]
async fn test_evidence_does_not_perturb_propagation() {
    let s = store().await;
    let svc = service().await;

    let a = Belief::new(format!("grnd-A-{}", Uuid::new_v4()), 0.8, 0.9).unwrap();
    let b = Belief::new(format!("grnd-B-{}", Uuid::new_v4()), 0.3, 0.8).unwrap();
    s.insert_belief(&a).await.unwrap();
    s.insert_belief(&b).await.unwrap();
    s.insert_edge(&Edge::new(a.id, b.id, EdgeType::Supports, 0.5).unwrap())
        .await
        .unwrap();

    // Baseline: propagate (this writes b), capture the result.
    let baseline = svc.propagate_from(a.id).await.unwrap();
    // Reset b to its original Beta state so the second run starts identically.
    s.update_belief_beta(b.id, b.alpha, b.beta).await.unwrap();

    // Overlay: a DocumentChunk grounding BOTH beliefs.
    let chunk = DocumentChunk::new(
        "evidence-doc.md".to_string(),
        vec![],
        "a grounding passage for the non-interference test".to_string(),
        None,
        None,
    );
    s.insert_document_chunk(&chunk).await.unwrap();
    svc.add_evidence(b.id, chunk.id, 0.9).await.unwrap();
    svc.add_evidence(a.id, chunk.id, 0.5).await.unwrap();

    // Re-run propagation over the overlaid graph.
    let rerun = svc.propagate_from(a.id).await.unwrap();

    assert_eq!(
        sorted_updates(baseline),
        sorted_updates(rerun),
        "GROUNDS overlay must not change propagation output"
    );
}

// add_evidence creates a GROUNDS edge; query_relevant_grounded returns the
// belief with its grounding passage.
#[tokio::test]
async fn test_add_and_query_grounded() {
    let s = store().await;
    let svc = service().await;

    let token = format!("zqxgrounded{}", Uuid::new_v4().simple());
    let b = Belief::new(format!("a belief about {}", token), 0.7, 0.8).unwrap();
    s.insert_belief(&b).await.unwrap();
    let chunk = DocumentChunk::new(
        "src.md".to_string(),
        vec!["Section One".to_string()],
        "the passage that grounds the belief".to_string(),
        None,
        None,
    );
    s.insert_document_chunk(&chunk).await.unwrap();
    svc.add_evidence(b.id, chunk.id, 0.8).await.unwrap();

    let grounded = svc.query_relevant_grounded(&token, 10, 3).await.unwrap();
    let gb = grounded
        .iter()
        .find(|g| g.belief.id == b.id)
        .expect("belief should be retrieved by its unique token");
    assert_eq!(gb.evidence.len(), 1, "one grounding passage expected");
    let e = &gb.evidence[0];
    assert!(e.snippet.contains("grounds the belief"));
    assert!((e.weight - 0.8).abs() < 1e-9);
    assert_eq!(e.section_path, vec!["Section One".to_string()]);
}

// delete_belief leaves no dangling GROUNDS edge (DETACH DELETE).
#[tokio::test]
async fn test_delete_belief_removes_grounds_edge() {
    let s = store().await;
    let svc = service().await;

    let b = Belief::new(format!("grnd-del-{}", Uuid::new_v4()), 0.5, 0.5).unwrap();
    s.insert_belief(&b).await.unwrap();
    let chunk = DocumentChunk::new(
        "d.md".to_string(),
        vec![],
        "passage".to_string(),
        None,
        None,
    );
    s.insert_document_chunk(&chunk).await.unwrap();
    svc.add_evidence(b.id, chunk.id, 1.0).await.unwrap();

    assert_eq!(s.get_evidence_for_beliefs(&[b.id]).await.unwrap().len(), 1);
    assert!(svc.delete_belief(b.id).await.unwrap());
    assert_eq!(
        s.get_evidence_for_beliefs(&[b.id]).await.unwrap().len(),
        0,
        "deleting the belief must remove its GROUNDS edges"
    );
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
    let s = store().await;
    let svc = service().await;

    let x = Belief::new(format!("oosX-{}", Uuid::new_v4()), 0.9, 0.5).unwrap();
    let y = Belief::new(format!("oosY-{}", Uuid::new_v4()), 0.9, 0.5).unwrap();
    let t = Belief::new(format!("oosT-{}", Uuid::new_v4()), 0.3, 0.5).unwrap();
    s.insert_belief(&x).await.unwrap();
    s.insert_belief(&y).await.unwrap();
    s.insert_belief(&t).await.unwrap();
    let t_alpha0 = t.alpha;

    svc.add_edge(x.id, t.id, EdgeType::Supports, 1.0)
        .await
        .unwrap();
    svc.add_edge(y.id, t.id, EdgeType::Supports, 1.0)
        .await
        .unwrap();

    // Propagate from X → T gains X's support.
    svc.propagate_from(x.id).await.unwrap();
    let t_after_x = s.get_belief(t.id).await.unwrap().unwrap().alpha;
    assert!(
        t_after_x > t_alpha0 + 1e-9,
        "X's support must raise T's α: α0={t_alpha0}, after X={t_after_x}"
    );

    // Propagate from Y. X is OUT of Y's subgraph. With the fix T re-derives from
    // ALL incoming edges (X external + Y), so X's support is preserved.
    svc.propagate_from(y.id).await.unwrap();
    let t_after_y = s.get_belief(t.id).await.unwrap().unwrap().alpha;

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

    // cleanup
    for id in [x.id, y.id, t.id] {
        let _ = svc.delete_belief(id).await;
    }
}
