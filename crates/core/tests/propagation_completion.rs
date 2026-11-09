//! Complete propagation must not depend on a chain's depth or UUID order.
use mimir_core::{
    graph::{Belief, EdgeType, Probability},
    inference::InferenceEngine,
};
use std::collections::HashMap;
use uuid::Uuid;

#[test]
fn every_descendant_in_a_reverse_ordered_chain_receives_its_complete_posterior() {
    let mut seed = Belief::new("known source".into(), 1.0, 0.0).unwrap();
    seed.id = Uuid::from_u128(2000);
    let mut descendants = Vec::new();
    let mut edges = Vec::new();
    let mut parent = seed.id;
    for depth in 0..60 {
        let mut belief = Belief::new(format!("descendant {depth}"), 0.0, 0.0).unwrap();
        // The engine's UUID sort visits children before their parents.
        belief.id = Uuid::from_u128(1000 - depth);
        edges.push((
            parent,
            belief.id,
            EdgeType::Supports,
            Probability::new(1.0).unwrap(),
        ));
        parent = belief.id;
        descendants.push(belief);
    }
    let result = InferenceEngine::new()
        .propagate_defeat(&seed, &descendants, &edges, &HashMap::new())
        .unwrap();
    assert_eq!(
        result.len(),
        descendants.len(),
        "propagation reported success with missing descendants"
    );
    // On this path each posterior has exactly its fixed prior plus its one
    // parent's evidence. This is the intended result, independent of passes.
    let mut parent_mean = 1.0;
    for belief in &descendants {
        let expected_alpha = belief.alpha0 + mimir_core::graph::EVIDENCE_UNIT * parent_mean;
        let expected_beta = belief.beta0;
        let (_, posterior) = result.iter().find(|(id, _)| *id == belief.id).unwrap();
        assert_eq!(
            *posterior,
            (expected_alpha, expected_beta),
            "incomplete posterior for {}",
            belief.content
        );
        parent_mean = mimir_core::graph::beta_mean(expected_alpha, expected_beta);
    }
}

#[test]
fn an_actual_small_posterior_change_is_not_silently_discarded() {
    let mut seed = Belief::new("small but explicit source probability".into(), 1e-12, 0.0).unwrap();
    seed.id = Uuid::from_u128(1);
    let mut target = Belief::new("receives every contribution".into(), 0.0, 0.0).unwrap();
    target.id = Uuid::from_u128(2);
    let edges = [(
        seed.id,
        target.id,
        EdgeType::Supports,
        Probability::new(1.0).unwrap(),
    )];
    let result = InferenceEngine::new()
        .propagate_defeat(&seed, &[target.clone()], &edges, &HashMap::new())
        .unwrap();
    assert_eq!(
        result,
        vec![(
            target.id,
            (mimir_core::graph::EVIDENCE_UNIT * 1e-12, target.beta0)
        )]
    );
}
