use ai_mem_core::{
    db,
    graph::{Belief, Edge, EdgeType},
    store::AgeStore,
};
use uuid::Uuid;

fn dsn() -> String {
    std::env::var("AI_MEM_DSN")
        .unwrap_or_else(|_| "postgresql://ai_mem@localhost:5450/ai_mem".to_string())
}

#[tokio::test]
async fn test_insert_and_get_belief() {
    let pool = db::connect(&dsn()).await.expect("connect");
    let store = AgeStore::new(pool);

    let belief = Belief::new(
        format!("test-belief-{}", Uuid::new_v4()),
        0.75,
        0.85,
    )
    .expect("belief");

    store.insert_belief(&belief).await.expect("insert_belief");

    let fetched = store
        .get_belief(belief.id)
        .await
        .expect("get_belief")
        .expect("belief should exist");

    assert_eq!(fetched.id, belief.id);
    assert_eq!(fetched.content, belief.content);
    assert!((fetched.probability.value() - 0.75).abs() < 1e-9);
    assert!((fetched.confidence.value() - 0.85).abs() < 1e-9);
}

#[tokio::test]
async fn test_insert_edge_supports() {
    let pool = db::connect(&dsn()).await.expect("connect");
    let store = AgeStore::new(pool);

    let b1 = Belief::new(
        format!("cause-belief-{}", Uuid::new_v4()),
        0.8,
        0.9,
    )
    .expect("b1");
    let b2 = Belief::new(
        format!("effect-belief-{}", Uuid::new_v4()),
        0.7,
        0.8,
    )
    .expect("b2");

    store.insert_belief(&b1).await.expect("insert b1");
    store.insert_belief(&b2).await.expect("insert b2");

    let edge = Edge::new(b1.id, b2.id, EdgeType::Supports, 0.9).expect("edge");
    store.insert_edge(&edge).await.expect("insert_edge");

    let downstream = store
        .get_downstream_beliefs(b1.id)
        .await
        .expect("get_downstream_beliefs");

    let found = downstream.iter().any(|b| b.id == b2.id);
    assert!(
        found,
        "b2 should be reachable from b1 via SUPPORTS; got: {:?}",
        downstream.iter().map(|b| b.id).collect::<Vec<_>>()
    );
}

#[tokio::test]
async fn test_contradicts_bidirectional() {
    let pool = db::connect(&dsn()).await.expect("connect");
    let store = AgeStore::new(pool);

    let b1 = Belief::new(
        format!("contra-a-{}", Uuid::new_v4()),
        0.6,
        0.7,
    )
    .expect("b1");
    let b2 = Belief::new(
        format!("contra-b-{}", Uuid::new_v4()),
        0.4,
        0.6,
    )
    .expect("b2");

    store.insert_belief(&b1).await.expect("insert b1");
    store.insert_belief(&b2).await.expect("insert b2");

    let weight = ai_mem_core::graph::Probability::new(0.95).expect("weight");
    store
        .insert_contradicts(b1.id, b2.id, weight)
        .await
        .expect("insert_contradicts");

    let pairs = store
        .get_contradiction_pairs()
        .await
        .expect("get_contradiction_pairs");

    let has_forward = pairs.iter().any(|(a, b)| *a == b1.id && *b == b2.id);
    let has_backward = pairs.iter().any(|(a, b)| *a == b2.id && *b == b1.id);

    assert!(
        has_forward,
        "expected forward contradiction pair (b1→b2); got: {:?}",
        pairs
    );
    assert!(
        has_backward,
        "expected backward contradiction pair (b2→b1); got: {:?}",
        pairs
    );
}
