use mimir_core::{
    config::DatabaseConfig,
    db,
    graph::{Belief, Edge, EdgeType, Pattern, Probability},
    store::AgeStore,
};
use uuid::Uuid;

fn test_db_config() -> DatabaseConfig {
    DatabaseConfig {
        host:   std::env::var("MIMIR_HOST")
                    .expect("MIMIR_HOST must be set to run integration tests"),
        port:   std::env::var("MIMIR_PORT")
                    .expect("MIMIR_PORT must be set to run integration tests")
                    .parse()
                    .expect("MIMIR_PORT must be a valid port number"),
        dbname: std::env::var("MIMIR_DBNAME")
                    .expect("MIMIR_DBNAME must be set to run integration tests"),
        user:   std::env::var("MIMIR_USER")
                    .expect("MIMIR_USER must be set to run integration tests"),
    }
}

async fn store() -> AgeStore {
    let cfg = test_db_config();
    let graph_name = cfg.dbname.clone();
    let pool = db::connect(&cfg).await.expect("connect");
    AgeStore::new(pool, graph_name).await.expect("ensure_labels")
}

// ---------------------------------------------------------------------------
// Belief CRUD
// ---------------------------------------------------------------------------

#[tokio::test]
async fn test_insert_and_get_belief() {
    let s = store().await;
    let b = Belief::new(format!("belief-{}", Uuid::new_v4()), 0.75, 0.85).unwrap();
    s.insert_belief(&b).await.expect("insert_belief");
    let got = s.get_belief(b.id).await.expect("get_belief").expect("should exist");
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

#[tokio::test]
async fn test_update_belief_probability() {
    let s = store().await;
    let b = Belief::new(format!("upd-prob-{}", Uuid::new_v4()), 0.5, 0.5).unwrap();
    s.insert_belief(&b).await.unwrap();
    s.update_belief_probability(b.id, Probability::new(0.9).unwrap()).await.unwrap();
    let got = s.get_belief(b.id).await.unwrap().unwrap();
    assert!((got.probability.value() - 0.9).abs() < 1e-9);
}

#[tokio::test]
async fn test_update_belief_confidence() {
    let s = store().await;
    let b = Belief::new(format!("upd-conf-{}", Uuid::new_v4()), 0.5, 0.5).unwrap();
    s.insert_belief(&b).await.unwrap();
    s.update_belief_confidence(b.id, Probability::new(0.2).unwrap()).await.unwrap();
    let got = s.get_belief(b.id).await.unwrap().unwrap();
    assert!((got.confidence.value() - 0.2).abs() < 1e-9);
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
    assert!(edges.iter().any(|(f, t, et, _)| *f == b1.id && *t == b2.id && *et == EdgeType::Defeats));
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
    let has = pairs.iter().any(|(a, b)| {
        (*a == b1.id && *b == b2.id) || (*a == b2.id && *b == b1.id)
    });
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
    s.insert_edge(&Edge::new(b1.id, b2.id, EdgeType::Supports, 0.9).unwrap()).await.unwrap();
    s.insert_edge(&Edge::new(b2.id, b3.id, EdgeType::Causes, 0.7).unwrap()).await.unwrap();

    let edges = s.get_edges_among(&[b1.id, b2.id, b3.id]).await.unwrap();
    assert!(edges.iter().any(|(f, t, et, _)| *f == b1.id && *t == b2.id && *et == EdgeType::Supports));
    assert!(edges.iter().any(|(f, t, et, _)| *f == b2.id && *t == b3.id && *et == EdgeType::Causes));
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
    s.insert_edge(&Edge::new(b1.id, b3.id, EdgeType::Supports, 0.9).unwrap()).await.unwrap();

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
    s.insert_edge(&Edge::new(b1.id, b2.id, EdgeType::Causes, 0.8).unwrap()).await.unwrap();
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
    s.insert_edge(&Edge::new(b1.id, b2.id, EdgeType::Supports, 0.9).unwrap()).await.unwrap();
    s.insert_edge(&Edge::new(b2.id, b3.id, EdgeType::Supports, 0.8).unwrap()).await.unwrap();
    let downstream = s.get_downstream_beliefs(b1.id).await.unwrap();
    assert!(downstream.iter().any(|b| b.id == b2.id));
    assert!(downstream.iter().any(|b| b.id == b3.id));
}
