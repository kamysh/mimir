use anyhow::Result;
use std::collections::{HashMap, HashSet, VecDeque};
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
    pub fn apply_decay(&self, prob: Probability, days_since_activation: f64, decay_factor: f64) -> Result<Probability> {
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
        if downstream.is_empty() {
            return Ok(vec![]);
        }

        // Build lookup maps
        let mut belief_map: HashMap<Uuid, Probability> = HashMap::new();
        belief_map.insert(seed.id, seed.probability);
        for b in downstream {
            belief_map.insert(b.id, b.probability);
        }

        // Build adjacency: for each belief, which edges go out from it
        let mut adj: HashMap<Uuid, Vec<(Uuid, EdgeType, Probability)>> = HashMap::new();
        for &(from, to, etype, weight) in edges {
            adj.entry(from).or_default().push((to, etype, weight));
        }

        let downstream_ids: HashSet<Uuid> = downstream.iter().map(|b| b.id).collect();

        // BFS from seed
        let mut queue: VecDeque<Uuid> = VecDeque::new();
        queue.push_back(seed.id);
        let mut visited: HashSet<Uuid> = HashSet::new();
        visited.insert(seed.id);

        let mut updated: HashMap<Uuid, Probability> = HashMap::new();

        while let Some(current_id) = queue.pop_front() {
            let current_prob = *belief_map.get(&current_id).unwrap_or(&seed.probability);

            if let Some(neighbors) = adj.get(&current_id) {
                for &(to_id, etype, weight) in neighbors {
                    let target_prob = match belief_map.get(&to_id) {
                        Some(&p) => p,
                        None => continue,
                    };

                    let new_prob = match etype {
                        EdgeType::Defeats => {
                            self.attenuate_by_defeat(target_prob, current_prob, weight)?
                        }
                        EdgeType::Supports | EdgeType::Causes => {
                            self.boost_by_support(target_prob, current_prob, weight)?
                        }
                        EdgeType::Contradicts => continue,
                    };

                    // Update the working probability for downstream propagation
                    belief_map.insert(to_id, new_prob);

                    if downstream_ids.contains(&to_id) {
                        updated.insert(to_id, new_prob);
                    }

                    if !visited.contains(&to_id) {
                        visited.insert(to_id);
                        queue.push_back(to_id);
                    }
                }
            }
        }

        Ok(updated.into_iter().collect())
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
        let r = engine().attenuate_by_defeat(prob(0.8), prob(0.5), prob(1.0)).unwrap();
        assert!((r.value() - 0.4).abs() < 1e-9, "got {}", r.value());
    }

    #[test]
    fn test_attenuate_weight_zero_is_identity() {
        // weight=0 → no defeat effect
        let r = engine().attenuate_by_defeat(prob(0.7), prob(0.9), prob(0.0)).unwrap();
        assert!((r.value() - 0.7).abs() < 1e-12);
    }

    #[test]
    fn test_attenuate_defeater_zero_is_identity() {
        // defeater prob=0 → no effect regardless of weight
        let r = engine().attenuate_by_defeat(prob(0.7), prob(0.0), prob(1.0)).unwrap();
        assert!((r.value() - 0.7).abs() < 1e-12);
    }

    #[test]
    fn test_attenuate_full_defeat() {
        // defeater=1, weight=1 → target × (1 - 1) = 0
        let r = engine().attenuate_by_defeat(prob(0.8), prob(1.0), prob(1.0)).unwrap();
        assert!((r.value() - 0.0).abs() < 1e-12);
    }

    #[test]
    fn test_attenuate_never_increases_concrete() {
        let r = engine().attenuate_by_defeat(prob(0.6), prob(0.4), prob(0.5)).unwrap();
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
        let r = engine().boost_by_support(prob(0.3), prob(0.8), prob(0.5)).unwrap();
        assert!((r.value() - 0.58).abs() < 1e-9, "got {}", r.value());
    }

    #[test]
    fn test_boost_weight_zero_is_identity() {
        let r = engine().boost_by_support(prob(0.4), prob(0.9), prob(0.0)).unwrap();
        assert!((r.value() - 0.4).abs() < 1e-12);
    }

    #[test]
    fn test_boost_supporter_zero_is_identity() {
        let r = engine().boost_by_support(prob(0.4), prob(0.0), prob(1.0)).unwrap();
        assert!((r.value() - 0.4).abs() < 1e-12);
    }

    #[test]
    fn test_boost_target_at_one_stays_one() {
        // target=1.0: 1 + (1-1) × w × s = 1
        let r = engine().boost_by_support(prob(1.0), prob(0.9), prob(0.9)).unwrap();
        assert!((r.value() - 1.0).abs() < 1e-12);
    }

    #[test]
    fn test_boost_never_decreases_concrete() {
        let r = engine().boost_by_support(prob(0.5), prob(0.6), prob(0.7)).unwrap();
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

        let updates = engine().propagate_defeat(&seed, &downstream, &edges).unwrap();
        let new_prob = updates.iter().find(|(id, _)| *id == target.id).map(|(_, p)| p.value());
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

        let updates = engine().propagate_defeat(&seed, &downstream, &edges).unwrap();
        let new_prob = updates.iter().find(|(id, _)| *id == target.id).map(|(_, p)| p.value());
        // 0.3 + (1-0.3) × 0.5 × 0.8 = 0.3 + 0.28 = 0.58
        assert!(new_prob.is_some());
        assert!(new_prob.unwrap() > 0.3);
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
        let beliefs: HashMap<uuid::Uuid, &Belief> =
            [(a.id, &a), (b.id, &b)].into_iter().collect();
        let pairs = vec![(a.id, b.id)];
        let result = engine().detect_active_contradictions(&beliefs, &pairs);
        assert!(result.is_empty());
    }

    #[test]
    fn test_detect_contradictions_finds_active_pair() {
        let a = Belief::new("A".to_string(), 0.8, 0.9).unwrap();
        let b = Belief::new("B".to_string(), 0.7, 0.9).unwrap();
        // 0.8 + 0.7 = 1.5 > 1.0
        let beliefs: HashMap<uuid::Uuid, &Belief> =
            [(a.id, &a), (b.id, &b)].into_iter().collect();
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
        b.last_activated_at = b.last_activated_at - chrono::Duration::days(100);
        let now = chrono::Utc::now();
        let updates = engine().decay_all(&[b.clone()], now, 0.99).unwrap();
        assert_eq!(updates.len(), 1);
        let (_, new_conf) = updates[0];
        assert!(new_conf.value() < b.confidence.value());
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
