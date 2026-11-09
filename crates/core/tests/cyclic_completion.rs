use mimir_core::{
    graph::{Belief, EdgeType, Probability},
    inference::{InferenceEngine, NumericalDecision},
};
use std::collections::HashMap;
use uuid::Uuid;

#[test]
fn repeated_incomplete_counts_request_a_user_decision_instead_of_success() {
    let mut a = Belief::new("A".into(), 0.1, 0.0).unwrap();
    let mut b = Belief::new("B".into(), 0.1, 0.0).unwrap();
    a.id = Uuid::from_u128(1);
    b.id = Uuid::from_u128(2);
    let edges = [
        (
            b.id,
            a.id,
            EdgeType::Defeats,
            Probability::new(0.7).unwrap(),
        ),
        (
            a.id,
            b.id,
            EdgeType::Supports,
            Probability::new(1.0).unwrap(),
        ),
    ];
    let error = InferenceEngine::new()
        .recompute(&[a, b], &edges, &HashMap::new())
        .unwrap_err();
    let decision = error
        .downcast_ref::<NumericalDecision>()
        .expect("numerical user decision");
    let issue = decision.issue();
    let message = &issue.fault().message;
    assert!(message.contains("2 distinct"), "{message}");
    assert!(message.contains("2.414395413276088"));
    assert!(message.contains("2.4143954132760874"));
    assert!(issue.suggested_correction().contains("Open a dialog"));
}

#[test]
fn completed_cycle_satisfies_every_final_count_equation_exactly() {
    let mut a = Belief::new("A".into(), 0.25, 0.0).unwrap();
    let mut b = Belief::new("B".into(), 0.75, 0.0).unwrap();
    a.id = Uuid::from_u128(1);
    b.id = Uuid::from_u128(2);
    let edges = [
        (
            b.id,
            a.id,
            EdgeType::Supports,
            Probability::new(1.0).unwrap(),
        ),
        (
            a.id,
            b.id,
            EdgeType::Supports,
            Probability::new(1.0).unwrap(),
        ),
    ];
    let beliefs = [a, b];
    let computed = InferenceEngine::new()
        .recompute(&beliefs, &edges, &HashMap::new())
        .unwrap();
    let mut final_values: HashMap<_, _> =
        beliefs.iter().map(|b| (b.id, (b.alpha, b.beta))).collect();
    final_values.extend(computed);
    for belief in &beliefs {
        let mut alpha = belief.alpha0;
        let beta = belief.beta0;
        for (source, target, _, weight) in &edges {
            if *target == belief.id {
                let (a, b) = final_values[source];
                alpha += weight.value()
                    * mimir_core::graph::beta_mean(a, b)
                    * mimir_core::graph::EVIDENCE_UNIT;
            }
        }
        assert_eq!(final_values[&belief.id].0.to_bits(), alpha.to_bits());
        assert_eq!(final_values[&belief.id].1.to_bits(), beta.to_bits());
    }
}
