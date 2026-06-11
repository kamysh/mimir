use anyhow::Result;
use std::collections::HashMap;
use uuid::Uuid;

use crate::graph::{Belief, EdgeType, Probability};

pub struct InferenceEngine;

impl InferenceEngine {
    pub fn new() -> Self {
        Self
    }

    /// Apply defeat attenuation: P(target) = P(target) × (1 - weight × P(defeater))
    pub fn attenuate_by_defeat(
        &self,
        target_prob: Probability,
        defeater_prob: Probability,
        weight: Probability,
    ) -> Result<Probability> {
        let result = target_prob.value() * (1.0 - weight.value() * defeater_prob.value());
        Probability::new(result.clamp(0.0, 1.0))
    }

    /// Apply support boost: P(target) = P(target) + (1-P(target)) × weight × P(supporter)
    pub fn boost_by_support(
        &self,
        target_prob: Probability,
        supporter_prob: Probability,
        weight: Probability,
    ) -> Result<Probability> {
        let p = target_prob.value();
        let result = p + (1.0 - p) * weight.value() * supporter_prob.value();
        Probability::new(result.clamp(0.0, 1.0))
    }

    /// Apply time decay to a single probability value.
    /// P_new = P × decay_factor^days_since_activation
    /// decay_factor ∈ (0, 1]: a value of 0.99 means ~1% decay per day.
    pub fn apply_decay(
        &self,
        prob: Probability,
        days_since_activation: f64,
        decay_factor: f64,
    ) -> Result<Probability> {
        let result = prob.value() * decay_factor.powf(days_since_activation);
        Probability::new(result.clamp(0.0, 1.0))
    }

    /// Check if two beliefs actively contradict: P(X) + P(Y) > 1.0 + ε
    pub fn is_contradicting(&self, belief_a: &Belief, belief_b: &Belief) -> bool {
        const EPSILON: f64 = 0.0;
        belief_a.probability.value() + belief_b.probability.value() > 1.0 + EPSILON
    }

    /// BFS propagation: given a seed belief whose probability changed,
    /// compute updated probabilities for all downstream beliefs.
    /// Returns Vec<(Uuid, Probability)> — the new probability for each affected belief.
    /// Does NOT write to the store — caller does that.
    pub fn propagate_defeat(
        &self,
        seed: &Belief,
        downstream: &[Belief],
        edges: &[(Uuid, Uuid, EdgeType, Probability)],
    ) -> Result<Vec<(Uuid, Probability)>> {
        self.propagate_core(seed.id, seed.probability, downstream, edges)
    }

    /// Counterfactual projection P(· | do(target = value)). Pearl's do-operator
    /// as graph surgery: delete every edge INTO `target_id` (sever its parents),
    /// keep only CAUSES edges (cut the evidential/correlational paths an
    /// intervention must ignore), clamp the target to `value`, and propagate
    /// forward along the surgical edge set.
    ///
    /// Pure and read-only — returns projected downstream probabilities; writes
    /// nothing. Contrast `propagate_defeat`, whose caller (`propagate_from`)
    /// persists the result. At the MCP layer the result key is
    /// `projected_probability`, reinforcing that nothing was written.
    ///
    /// As of Phase 2 the shared `propagate_core` is an order-independent
    /// fixpoint (per-node one-shot aggregation), so cycles and re-convergent
    /// paths in the causal subgraph yield a well-defined, order-independent
    /// result for both functions at once.
    pub fn intervene(
        &self,
        target_id: Uuid,
        value: Probability,
        downstream: &[Belief],
        edges: &[(Uuid, Uuid, EdgeType, Probability)],
    ) -> Result<Vec<(Uuid, Probability)>> {
        // Graph mutilation: drop edges into the target, keep CAUSES only.
        let surgical: Vec<(Uuid, Uuid, EdgeType, Probability)> = edges
            .iter()
            .copied()
            .filter(|&(_from, to, et, _w)| to != target_id && et == EdgeType::Causes)
            .collect();
        self.propagate_core(target_id, value, downstream, &surgical)
    }

    /// Shared fixpoint propagation core. `seed_id`/`seed_prob` is the changed
    /// (or clamped) node, held fixed; `edges` is the edge set to follow, already
    /// filtered by the caller (`propagate_defeat` passes every edge; `intervene`
    /// passes only the surgical CAUSES set). Snapshots every node's probability,
    /// then iterates to a fixpoint: each node aggregates ALL of its incoming
    /// edges in one shot (noisy-OR over SUPPORTS/CAUSES, noisy-AND over DEFEATS).
    /// Because the aggregation is a product it is order-independent. Bounded by
    /// MAX_ITERS; pure, never writes to the store.
    fn propagate_core(
        &self,
        seed_id: Uuid,
        seed_prob: Probability,
        downstream: &[Belief],
        edges: &[(Uuid, Uuid, EdgeType, Probability)],
    ) -> Result<Vec<(Uuid, Probability)>> {
        if downstream.is_empty() {
            return Ok(vec![]);
        }

        const MAX_ITERS: usize = 50;
        const EPS: f64 = 1e-9;

        // Snapshot every node's probability at pass start. Downstream first, then
        // the seed, so the seed's clamped value always wins and is held fixed.
        let mut base: HashMap<Uuid, f64> = HashMap::new();
        for b in downstream {
            base.insert(b.id, b.probability.value());
        }
        base.insert(seed_id, seed_prob.value());

        // Incoming adjacency keyed by TARGET: target -> [(type, weight, source)].
        // Only edges with both endpoints in the snapshot can contribute.
        let mut incoming: HashMap<Uuid, Vec<(EdgeType, f64, Uuid)>> = HashMap::new();
        for &(from, to, etype, weight) in edges {
            if base.contains_key(&from) && base.contains_key(&to) {
                incoming
                    .entry(to)
                    .or_default()
                    .push((etype, weight.value(), from));
            }
        }

        // Working values, initialised to base. The seed is never swept, so it
        // stays clamped. Sweep order is the downstream ids sorted, for a
        // deterministic (but order-independent) traversal.
        let mut val: HashMap<Uuid, f64> = base.clone();
        let mut order: Vec<Uuid> = downstream
            .iter()
            .map(|b| b.id)
            .filter(|id| *id != seed_id)
            .collect();
        order.sort();

        // Fixpoint iteration. Each node aggregates ALL of its incoming edges in
        // one shot — noisy-OR over SUPPORTS/CAUSES, noisy-AND over DEFEATS — which
        // is a product and therefore order-independent, reading the current
        // values of its parents. On a DAG one sweep is exact; cycles converge.
        let mut converged = false;
        for _ in 0..MAX_ITERS {
            let mut max_delta = 0.0_f64;
            for &v in &order {
                let b = base[&v];
                let mut p = b;
                if let Some(edges_in) = incoming.get(&v) {
                    let mut support_complement = 1.0_f64; // ∏ supports (1 − w·src)
                    let mut defeat_factor = 1.0_f64; //      ∏ defeats  (1 − w·src)
                    for &(etype, w, src) in edges_in {
                        let s = val[&src];
                        match etype {
                            EdgeType::Supports | EdgeType::Causes => {
                                support_complement *= 1.0 - w * s;
                            }
                            EdgeType::Defeats => {
                                defeat_factor *= 1.0 - w * s;
                            }
                            EdgeType::Contradicts => {} // skipped during propagation
                        }
                    }
                    p = 1.0 - (1.0 - b) * support_complement; // noisy-OR onto base
                    p *= defeat_factor; //                       noisy-AND attenuation
                }
                let p = p.clamp(0.0, 1.0);
                let delta = (p - val[&v]).abs();
                if delta > max_delta {
                    max_delta = delta;
                }
                val.insert(v, p);
            }
            if max_delta < EPS {
                converged = true;
                break;
            }
        }
        if !converged {
            tracing::warn!(
                subgraph_size = order.len(),
                "propagate_core hit MAX_ITERS without converging; returning current values"
            );
        }

        // Report only nodes whose value actually moved from base (seed excluded).
        let mut updated: Vec<(Uuid, Probability)> = Vec::new();
        for &v in &order {
            let p = val[&v];
            if (p - base[&v]).abs() > EPS {
                updated.push((v, Probability::new(p)?));
            }
        }
        Ok(updated)
    }

    /// Find all actively contradicting pairs from the contradiction pairs list.
    /// A pair actively contradicts when P(a) + P(b) > 1.0 (probabilities sum to more than 100%).
    pub fn detect_active_contradictions(
        &self,
        beliefs: &HashMap<Uuid, &Belief>,
        contradiction_pairs: &[(Uuid, Uuid)],
    ) -> Vec<(Uuid, Uuid)> {
        let mut result = Vec::new();
        for &(a_id, b_id) in contradiction_pairs {
            if let (Some(a), Some(b)) = (beliefs.get(&a_id), beliefs.get(&b_id)) {
                if self.is_contradicting(a, b) {
                    result.push((a_id, b_id));
                }
            }
        }
        result
    }

    /// Compute decayed confidence values for all beliefs.
    /// Returns Vec<(Uuid, Probability)> of beliefs whose confidence actually changed.
    /// decay_factor is configurable; default is 0.99 (~1% per day).
    pub fn decay_all(
        &self,
        beliefs: &[Belief],
        now: chrono::DateTime<chrono::Utc>,
        decay_factor: f64,
    ) -> Result<Vec<(Uuid, Probability)>> {
        let mut result = Vec::new();
        for belief in beliefs {
            let days = (now - belief.last_activated_at).num_seconds() as f64 / 86400.0;
            let days = days.max(0.0);
            let decayed = self.apply_decay(belief.confidence, days, decay_factor)?;
            // Only report if the value actually changed (using a tiny epsilon)
            if (decayed.value() - belief.confidence.value()).abs() > f64::EPSILON {
                result.push((belief.id, decayed));
            }
        }
        Ok(result)
    }
}

impl Default for InferenceEngine {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::Belief;
    use proptest::prelude::*;

    fn prob(v: f64) -> Probability {
        Probability::new(v).unwrap()
    }

    fn engine() -> InferenceEngine {
        InferenceEngine::new()
    }

    // ------------------------------------------------------------------
    // attenuate_by_defeat — unit tests
    // ------------------------------------------------------------------

    #[test]
    fn test_attenuate_by_defeat() {
        // P=0.8, defeater=0.5, w=1.0 → 0.8 × (1 - 1.0 × 0.5) = 0.4
        let r = engine()
            .attenuate_by_defeat(prob(0.8), prob(0.5), prob(1.0))
            .unwrap();
        assert!((r.value() - 0.4).abs() < 1e-9, "got {}", r.value());
    }

    #[test]
    fn test_attenuate_weight_zero_is_identity() {
        // weight=0 → no defeat effect
        let r = engine()
            .attenuate_by_defeat(prob(0.7), prob(0.9), prob(0.0))
            .unwrap();
        assert!((r.value() - 0.7).abs() < 1e-12);
    }

    #[test]
    fn test_attenuate_defeater_zero_is_identity() {
        // defeater prob=0 → no effect regardless of weight
        let r = engine()
            .attenuate_by_defeat(prob(0.7), prob(0.0), prob(1.0))
            .unwrap();
        assert!((r.value() - 0.7).abs() < 1e-12);
    }

    #[test]
    fn test_attenuate_full_defeat() {
        // defeater=1, weight=1 → target × (1 - 1) = 0
        let r = engine()
            .attenuate_by_defeat(prob(0.8), prob(1.0), prob(1.0))
            .unwrap();
        assert!((r.value() - 0.0).abs() < 1e-12);
    }

    #[test]
    fn test_attenuate_never_increases_concrete() {
        let r = engine()
            .attenuate_by_defeat(prob(0.6), prob(0.4), prob(0.5))
            .unwrap();
        // 0.6 × (1 - 0.5 × 0.4) = 0.6 × 0.8 = 0.48
        assert!(r.value() <= 0.6 + 1e-12);
        assert!((r.value() - 0.48).abs() < 1e-9);
    }

    // ------------------------------------------------------------------
    // boost_by_support — unit tests
    // ------------------------------------------------------------------

    #[test]
    fn test_boost_by_support() {
        // P=0.3, supporter=0.8, w=0.5 → 0.3 + 0.7 × 0.5 × 0.8 = 0.58
        let r = engine()
            .boost_by_support(prob(0.3), prob(0.8), prob(0.5))
            .unwrap();
        assert!((r.value() - 0.58).abs() < 1e-9, "got {}", r.value());
    }

    #[test]
    fn test_boost_weight_zero_is_identity() {
        let r = engine()
            .boost_by_support(prob(0.4), prob(0.9), prob(0.0))
            .unwrap();
        assert!((r.value() - 0.4).abs() < 1e-12);
    }

    #[test]
    fn test_boost_supporter_zero_is_identity() {
        let r = engine()
            .boost_by_support(prob(0.4), prob(0.0), prob(1.0))
            .unwrap();
        assert!((r.value() - 0.4).abs() < 1e-12);
    }

    #[test]
    fn test_boost_target_at_one_stays_one() {
        // target=1.0: 1 + (1-1) × w × s = 1
        let r = engine()
            .boost_by_support(prob(1.0), prob(0.9), prob(0.9))
            .unwrap();
        assert!((r.value() - 1.0).abs() < 1e-12);
    }

    #[test]
    fn test_boost_never_decreases_concrete() {
        let r = engine()
            .boost_by_support(prob(0.5), prob(0.6), prob(0.7))
            .unwrap();
        assert!(r.value() >= 0.5 - 1e-12);
    }

    // ------------------------------------------------------------------
    // apply_decay — unit tests
    // ------------------------------------------------------------------

    #[test]
    fn test_apply_decay_zero_days() {
        let r = engine().apply_decay(prob(0.75), 0.0, 0.99).unwrap();
        assert!((r.value() - 0.75).abs() < 1e-9);
    }

    #[test]
    fn test_apply_decay_one_day() {
        // 0.75 × 0.99 = 0.7425
        let r = engine().apply_decay(prob(0.75), 1.0, 0.99).unwrap();
        assert!((r.value() - 0.7425).abs() < 1e-9);
    }

    #[test]
    fn test_apply_decay_factor_one_no_change() {
        let r = engine().apply_decay(prob(0.6), 30.0, 1.0).unwrap();
        assert!((r.value() - 0.6).abs() < 1e-12);
    }

    #[test]
    fn test_apply_decay_factor_zero_gives_zero() {
        let r = engine().apply_decay(prob(0.8), 1.0, 0.0).unwrap();
        assert_eq!(r.value(), 0.0);
    }

    #[test]
    fn test_apply_decay_more_days_more_decay() {
        let r1 = engine().apply_decay(prob(0.9), 1.0, 0.9).unwrap();
        let r2 = engine().apply_decay(prob(0.9), 10.0, 0.9).unwrap();
        assert!(r2.value() < r1.value());
    }

    // ------------------------------------------------------------------
    // is_contradicting — unit tests
    // ------------------------------------------------------------------

    #[test]
    fn test_is_contradicting_both_high() {
        let a = Belief::new("A".to_string(), 0.8, 0.9).unwrap();
        let b = Belief::new("B".to_string(), 0.9, 0.8).unwrap();
        assert!(engine().is_contradicting(&a, &b));
    }

    #[test]
    fn test_is_contradicting_one_low() {
        // 0.8 + 0.1 = 0.9 ≤ 1.0
        let a = Belief::new("A".to_string(), 0.8, 0.9).unwrap();
        let b = Belief::new("B".to_string(), 0.1, 0.8).unwrap();
        assert!(!engine().is_contradicting(&a, &b));
    }

    #[test]
    fn test_is_contradicting_exactly_one_not_contradicting() {
        // 0.5 + 0.5 = 1.0, which is NOT > 1.0
        let a = Belief::new("A".to_string(), 0.5, 0.5).unwrap();
        let b = Belief::new("B".to_string(), 0.5, 0.5).unwrap();
        assert!(!engine().is_contradicting(&a, &b));
    }

    #[test]
    fn test_is_contradicting_just_above_one() {
        // 0.6 + 0.5 = 1.1 > 1.0
        let a = Belief::new("A".to_string(), 0.6, 0.5).unwrap();
        let b = Belief::new("B".to_string(), 0.5, 0.5).unwrap();
        assert!(engine().is_contradicting(&a, &b));
    }

    // ------------------------------------------------------------------
    // propagate_defeat — unit tests
    // ------------------------------------------------------------------

    #[test]
    fn test_propagate_defeat_empty_downstream() {
        let seed = Belief::new("seed".to_string(), 0.9, 0.9).unwrap();
        let result = engine().propagate_defeat(&seed, &[], &[]).unwrap();
        assert!(result.is_empty());
    }

    #[test]
    fn test_propagate_defeat_single_defeat_edge_reduces_probability() {
        let seed = Belief::new("seed".to_string(), 0.8, 0.9).unwrap();
        let target = Belief::new("target".to_string(), 0.7, 0.8).unwrap();
        let w = Probability::new(1.0).unwrap();
        let edges = vec![(seed.id, target.id, EdgeType::Defeats, w)];
        let downstream = vec![target.clone()];

        let updates = engine()
            .propagate_defeat(&seed, &downstream, &edges)
            .unwrap();
        let new_prob = updates
            .iter()
            .find(|(id, _)| *id == target.id)
            .map(|(_, p)| p.value());
        // 0.7 × (1 - 1.0 × 0.8) = 0.7 × 0.2 = 0.14
        assert!(new_prob.is_some());
        assert!((new_prob.unwrap() - 0.14).abs() < 1e-9);
    }

    #[test]
    fn test_propagate_defeat_single_support_edge_increases_probability() {
        let seed = Belief::new("seed".to_string(), 0.8, 0.9).unwrap();
        let target = Belief::new("target".to_string(), 0.3, 0.8).unwrap();
        let w = Probability::new(0.5).unwrap();
        let edges = vec![(seed.id, target.id, EdgeType::Supports, w)];
        let downstream = vec![target.clone()];

        let updates = engine()
            .propagate_defeat(&seed, &downstream, &edges)
            .unwrap();
        let new_prob = updates
            .iter()
            .find(|(id, _)| *id == target.id)
            .map(|(_, p)| p.value());
        // 0.3 + (1-0.3) × 0.5 × 0.8 = 0.3 + 0.28 = 0.58
        assert!(new_prob.is_some());
        assert!(new_prob.unwrap() > 0.3);
    }

    // ------------------------------------------------------------------
    // intervene (do-operator) — unit tests
    // ------------------------------------------------------------------

    // Test 1: surgery severs incoming edges to the target. Graph
    // A -CAUSES-> T -CAUSES-> B. do(T = v) must update B via T only, and be
    // completely unaffected by A's probability or the A→T edge.
    #[test]
    fn test_intervene_ignores_incoming_edges_to_target() {
        let t = Belief::new("T".to_string(), 0.2, 0.9).unwrap();
        let b = Belief::new("B".to_string(), 0.3, 0.9).unwrap();
        let a_lo = Belief::new("A".to_string(), 0.1, 0.9).unwrap();
        let a_hi = Belief::new("A".to_string(), 0.99, 0.9).unwrap();
        let w = Probability::new(0.5).unwrap();
        let clamp = Probability::new(1.0).unwrap();
        let downstream = vec![b.clone()];

        // Vary A's probability and keep the A→T edge present; B's projection
        // must be identical because do(T) deletes the edge into T.
        let edges_lo = vec![
            (a_lo.id, t.id, EdgeType::Causes, w),
            (t.id, b.id, EdgeType::Causes, w),
        ];
        let edges_hi = vec![
            (a_hi.id, t.id, EdgeType::Causes, w),
            (t.id, b.id, EdgeType::Causes, w),
        ];

        let lo = engine()
            .intervene(t.id, clamp, &downstream, &edges_lo)
            .unwrap();
        let hi = engine()
            .intervene(t.id, clamp, &downstream, &edges_hi)
            .unwrap();

        let b_lo = lo
            .iter()
            .find(|(id, _)| *id == b.id)
            .map(|(_, p)| p.value());
        let b_hi = hi
            .iter()
            .find(|(id, _)| *id == b.id)
            .map(|(_, p)| p.value());
        assert!(b_lo.is_some(), "B should be updated through T");
        assert_eq!(
            b_lo, b_hi,
            "B's projection must not depend on A (parent of T)"
        );
        // B = boost(0.3, 1.0, 0.5) = 0.3 + 0.7 × 0.5 × 1.0 = 0.65
        assert!((b_lo.unwrap() - 0.65).abs() < 1e-9);
    }

    // Test 2: only CAUSES edges are followed. Graph T -SUPPORTS-> B.
    // do(T = v) drops the SUPPORTS edge, so B is unchanged. This fails if
    // someone collapses Causes back into the Supports arm.
    #[test]
    fn test_intervene_follows_only_causes_edges() {
        let t = Belief::new("T".to_string(), 0.2, 0.9).unwrap();
        let b = Belief::new("B".to_string(), 0.3, 0.9).unwrap();
        let w = Probability::new(0.9).unwrap();
        let clamp = Probability::new(1.0).unwrap();
        let downstream = vec![b.clone()];
        let edges = vec![(t.id, b.id, EdgeType::Supports, w)];

        let updates = engine()
            .intervene(t.id, clamp, &downstream, &edges)
            .unwrap();
        assert!(
            updates.iter().all(|(id, _)| *id != b.id),
            "SUPPORTS edge must not propagate under an intervention"
        );
    }

    // Test 3 (canonical confounder example): fork C -CAUSES-> T, C -CAUSES-> B.
    // T and B are evidentially associated through C, but T does not cause B.
    // do(T = v) — "forcing T" — must tell us nothing about B: the surgical set
    // keeps C→B (target ≠ T) but drops C→T (target = T), and BFS starts from T,
    // which has no outgoing surgical edge → B is never reached.
    #[test]
    fn test_intervene_confounder_does_not_reach_associated_node() {
        let c = Belief::new("C".to_string(), 0.9, 0.9).unwrap();
        let t = Belief::new("T".to_string(), 0.4, 0.9).unwrap();
        let b = Belief::new("B".to_string(), 0.4, 0.9).unwrap();
        let w = Probability::new(0.8).unwrap();
        let clamp = Probability::new(1.0).unwrap();
        let downstream = vec![b.clone()];
        let edges = vec![
            (c.id, t.id, EdgeType::Causes, w),
            (c.id, b.id, EdgeType::Causes, w),
        ];

        let updates = engine()
            .intervene(t.id, clamp, &downstream, &edges)
            .unwrap();
        assert!(
            updates.iter().all(|(id, _)| *id != b.id),
            "do(T) must not affect B when their only link is a common cause C"
        );
    }

    // ------------------------------------------------------------------
    // detect_active_contradictions — unit tests
    // ------------------------------------------------------------------

    #[test]
    fn test_detect_contradictions_empty_input() {
        let result = engine().detect_active_contradictions(&HashMap::new(), &[]);
        assert!(result.is_empty());
    }

    #[test]
    fn test_detect_contradictions_filters_low_probs() {
        let a = Belief::new("A".to_string(), 0.3, 0.5).unwrap();
        let b = Belief::new("B".to_string(), 0.4, 0.5).unwrap();
        // 0.3 + 0.4 = 0.7 ≤ 1.0 → not contradicting
        let beliefs: HashMap<uuid::Uuid, &Belief> = [(a.id, &a), (b.id, &b)].into_iter().collect();
        let pairs = vec![(a.id, b.id)];
        let result = engine().detect_active_contradictions(&beliefs, &pairs);
        assert!(result.is_empty());
    }

    #[test]
    fn test_detect_contradictions_finds_active_pair() {
        let a = Belief::new("A".to_string(), 0.8, 0.9).unwrap();
        let b = Belief::new("B".to_string(), 0.7, 0.9).unwrap();
        // 0.8 + 0.7 = 1.5 > 1.0
        let beliefs: HashMap<uuid::Uuid, &Belief> = [(a.id, &a), (b.id, &b)].into_iter().collect();
        let pairs = vec![(a.id, b.id)];
        let result = engine().detect_active_contradictions(&beliefs, &pairs);
        assert_eq!(result.len(), 1);
    }

    // ------------------------------------------------------------------
    // decay_all — unit tests
    // ------------------------------------------------------------------

    #[test]
    fn test_decay_all_recently_activated_no_change() {
        let b = Belief::new("fresh".to_string(), 0.8, 0.9).unwrap();
        let now = b.last_activated_at; // same instant → 0 days
        let updates = engine().decay_all(&[b], now, 0.99).unwrap();
        // 0 days of decay → no change → not reported
        assert!(updates.is_empty());
    }

    #[test]
    fn test_decay_all_old_belief_decays() {
        let mut b = Belief::new("old".to_string(), 0.9, 0.9).unwrap();
        // Wind back last_activated_at by 100 days
        b.last_activated_at -= chrono::Duration::days(100);
        let now = chrono::Utc::now();
        let updates = engine().decay_all(&[b.clone()], now, 0.99).unwrap();
        assert_eq!(updates.len(), 1);
        let (_, new_conf) = updates[0];
        assert!(new_conf.value() < b.confidence.value());
    }

    // ------------------------------------------------------------------
    // Phase 2 — order-independent, fixpoint propagation
    // ------------------------------------------------------------------

    // RED: re-convergence order-dependence. Graph S→A, S→T, A→T, T→D (all
    // SUPPORTS, w=1). T has two parents (S, A) AND a child D. Under the old
    // single-pass BFS, D was computed from T's value at the moment T was popped
    // — before A's edge had finished raising T — so permuting the edge slice
    // changed D (0.838 vs 0.974). A well-defined propagation is independent of
    // edge order.
    #[test]
    fn test_propagate_is_order_independent_on_reconvergent_graph() {
        let s = Belief::new("S".to_string(), 0.8, 0.9).unwrap();
        let a = Belief::new("A".to_string(), 0.2, 0.9).unwrap();
        let t = Belief::new("T".to_string(), 0.1, 0.9).unwrap();
        let d = Belief::new("D".to_string(), 0.1, 0.9).unwrap();
        let w = prob(1.0);
        let downstream = vec![a.clone(), t.clone(), d.clone()];

        let order1 = vec![
            (s.id, t.id, EdgeType::Supports, w),
            (s.id, a.id, EdgeType::Supports, w),
            (a.id, t.id, EdgeType::Supports, w),
            (t.id, d.id, EdgeType::Supports, w),
        ];
        let mut order2 = order1.clone();
        order2.reverse();

        let r1 = engine().propagate_defeat(&s, &downstream, &order1).unwrap();
        let r2 = engine().propagate_defeat(&s, &downstream, &order2).unwrap();

        let val = |r: &[(uuid::Uuid, Probability)], id: uuid::Uuid| {
            r.iter().find(|(i, _)| *i == id).map(|(_, p)| p.value())
        };
        assert_eq!(
            val(&r1, d.id),
            val(&r2, d.id),
            "D must not depend on edge order"
        );
        assert_eq!(
            val(&r1, t.id),
            val(&r2, t.id),
            "T must not depend on edge order"
        );
    }

    // RED: convergence + stability on a cycle. S→A, A→B, B→A (SUPPORTS). The old
    // single-pass BFS visited each node once and never reached a fixpoint;
    // feeding its output back in changed it. A correct propagation converges, so
    // a second propagation from the converged base is stable.
    #[test]
    fn test_propagate_converges_and_is_stable_on_cycle() {
        let s = Belief::new("S".to_string(), 0.9, 0.9).unwrap();
        let a = Belief::new("A".to_string(), 0.2, 0.9).unwrap();
        let b = Belief::new("B".to_string(), 0.2, 0.9).unwrap();
        let w = prob(1.0);
        let edges = vec![
            (s.id, a.id, EdgeType::Supports, w),
            (a.id, b.id, EdgeType::Supports, w),
            (b.id, a.id, EdgeType::Supports, w),
        ];

        let r1 = engine()
            .propagate_defeat(&s, &[a.clone(), b.clone()], &edges)
            .unwrap();

        // Feed the result back as the new base and propagate again.
        let mut a2 = a.clone();
        let mut b2 = b.clone();
        for (id, p) in &r1 {
            if *id == a.id {
                a2.probability = *p;
            }
            if *id == b.id {
                b2.probability = *p;
            }
        }
        let r2 = engine()
            .propagate_defeat(&s, &[a2.clone(), b2.clone()], &edges)
            .unwrap();

        let pa1 = r1
            .iter()
            .find(|(i, _)| *i == a.id)
            .map(|(_, p)| p.value())
            .unwrap();
        let pb1 = r1
            .iter()
            .find(|(i, _)| *i == b.id)
            .map(|(_, p)| p.value())
            .unwrap();
        // After convergence the fixpoint impl reports no change, so fall back to
        // the (already converged) fed-back value.
        let pa2 = r2
            .iter()
            .find(|(i, _)| *i == a.id)
            .map(|(_, p)| p.value())
            .unwrap_or(a2.probability.value());
        let pb2 = r2
            .iter()
            .find(|(i, _)| *i == b.id)
            .map(|(_, p)| p.value())
            .unwrap_or(b2.probability.value());

        assert!(
            (pa1 - pa2).abs() < 1e-9,
            "A not stable across calls: {pa1} vs {pa2}"
        );
        assert!(
            (pb1 - pb2).abs() < 1e-9,
            "B not stable across calls: {pb1} vs {pb2}"
        );
    }

    // GUARD: a node with two supporters takes the noisy-OR of them onto its base.
    // S→A, S→B, A→T, B→T (SUPPORTS, w=1): T = 1−(1−0.1)(1−0.84)(1−0.84) ≈ 0.97696.
    #[test]
    fn test_propagate_multi_parent_noisy_or() {
        let s = Belief::new("S".to_string(), 0.8, 0.9).unwrap();
        let a = Belief::new("A".to_string(), 0.2, 0.9).unwrap();
        let b = Belief::new("B".to_string(), 0.2, 0.9).unwrap();
        let t = Belief::new("T".to_string(), 0.1, 0.9).unwrap();
        let w = prob(1.0);
        let edges = vec![
            (s.id, a.id, EdgeType::Supports, w),
            (s.id, b.id, EdgeType::Supports, w),
            (a.id, t.id, EdgeType::Supports, w),
            (b.id, t.id, EdgeType::Supports, w),
        ];
        let r = engine()
            .propagate_defeat(&s, &[a.clone(), b.clone(), t.clone()], &edges)
            .unwrap();
        let tp = r
            .iter()
            .find(|(i, _)| *i == t.id)
            .map(|(_, p)| p.value())
            .unwrap();
        assert!(
            (tp - 0.97696).abs() < 1e-6,
            "T should be the noisy-OR ≈ 0.97696, got {tp}"
        );
    }

    // ------------------------------------------------------------------
    // Proptest — property-based tests
    // ------------------------------------------------------------------

    proptest! {
        #[test]
        fn prop_attenuate_result_in_range(
            target in 0.0f64..=1.0f64,
            defeater in 0.0f64..=1.0f64,
            weight in 0.0f64..=1.0f64,
        ) {
            let r = engine()
                .attenuate_by_defeat(prob(target), prob(defeater), prob(weight))
                .unwrap();
            prop_assert!(r.value() >= 0.0 && r.value() <= 1.0);
        }

        #[test]
        fn prop_attenuate_never_increases(
            target in 0.0f64..=1.0f64,
            defeater in 0.0f64..=1.0f64,
            weight in 0.0f64..=1.0f64,
        ) {
            let r = engine()
                .attenuate_by_defeat(prob(target), prob(defeater), prob(weight))
                .unwrap();
            prop_assert!(r.value() <= target + 1e-12);
        }

        #[test]
        fn prop_boost_result_in_range(
            target in 0.0f64..=1.0f64,
            supporter in 0.0f64..=1.0f64,
            weight in 0.0f64..=1.0f64,
        ) {
            let r = engine()
                .boost_by_support(prob(target), prob(supporter), prob(weight))
                .unwrap();
            prop_assert!(r.value() >= 0.0 && r.value() <= 1.0);
        }

        #[test]
        fn prop_boost_never_decreases(
            target in 0.0f64..=1.0f64,
            supporter in 0.0f64..=1.0f64,
            weight in 0.0f64..=1.0f64,
        ) {
            let r = engine()
                .boost_by_support(prob(target), prob(supporter), prob(weight))
                .unwrap();
            prop_assert!(r.value() >= target - 1e-12);
        }

        #[test]
        fn prop_decay_result_in_range(
            p in 0.0f64..=1.0f64,
            days in 0.0f64..=365.0f64,
            factor in 0.0f64..=1.0f64,
        ) {
            let r = engine().apply_decay(prob(p), days, factor).unwrap();
            prop_assert!(r.value() >= 0.0 && r.value() <= 1.0);
        }

        #[test]
        fn prop_decay_never_increases(
            p in 0.0f64..=1.0f64,
            days in 0.0f64..=365.0f64,
            factor in 0.0f64..=1.0f64,
        ) {
            let r = engine().apply_decay(prob(p), days, factor).unwrap();
            prop_assert!(r.value() <= p + 1e-12);
        }

        #[test]
        fn prop_is_contradicting_high_sum(
            a in 0.5f64..=1.0f64,
            b in 0.5f64..=1.0f64,
        ) {
            // a + b ≥ 1.0; contradicting only when strictly > 1.0
            let ba = Belief::new("A".to_string(), a, 0.5).unwrap();
            let bb = Belief::new("B".to_string(), b, 0.5).unwrap();
            let contradicting = engine().is_contradicting(&ba, &bb);
            prop_assert_eq!(contradicting, a + b > 1.0);
        }
    }
}
