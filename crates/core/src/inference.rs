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
    /// P_new = P × e^(-λ × hours_since_activation), λ = 0.01
    pub fn apply_decay(&self, prob: Probability, hours_since_activation: f64) -> Result<Probability> {
        const LAMBDA: f64 = 0.01;
        let result = prob.value() * (-LAMBDA * hours_since_activation).exp();
        Probability::new(result.clamp(0.0, 1.0))
    }

    /// Check if two beliefs actively contradict: both have probability > 0.5
    pub fn is_contradicting(&self, belief_a: &Belief, belief_b: &Belief) -> bool {
        belief_a.probability.value() > 0.5 && belief_b.probability.value() > 0.5
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
    /// Returns pairs where both beliefs have probability > 0.5.
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

    /// Compute decayed probabilities for all beliefs.
    /// Returns Vec<(Uuid, Probability)> of beliefs whose probability actually changed.
    pub fn decay_all(
        &self,
        beliefs: &[Belief],
        now: chrono::DateTime<chrono::Utc>,
    ) -> Result<Vec<(Uuid, Probability)>> {
        let mut result = Vec::new();
        for belief in beliefs {
            let hours = (now - belief.last_activated_at).num_seconds() as f64 / 3600.0;
            let hours = hours.max(0.0);
            let decayed = self.apply_decay(belief.probability, hours)?;
            // Only report if the value actually changed (using a tiny epsilon)
            if (decayed.value() - belief.probability.value()).abs() > f64::EPSILON {
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

    fn prob(v: f64) -> Probability {
        Probability::new(v).unwrap()
    }

    #[test]
    fn test_attenuate_by_defeat() {
        let engine = InferenceEngine::new();
        // P=0.8, defeater=0.5, w=1.0 → 0.8 × (1 - 1.0 × 0.5) = 0.8 × 0.5 = 0.4
        let result = engine
            .attenuate_by_defeat(prob(0.8), prob(0.5), prob(1.0))
            .unwrap();
        let diff = (result.value() - 0.4).abs();
        assert!(diff < 1e-9, "expected ≈0.4 but got {}", result.value());
    }

    #[test]
    fn test_boost_by_support() {
        let engine = InferenceEngine::new();
        // P=0.3, supporter=0.8, w=0.5 → 0.3 + 0.7 × 0.5 × 0.8 = 0.3 + 0.28 = 0.58
        let result = engine
            .boost_by_support(prob(0.3), prob(0.8), prob(0.5))
            .unwrap();
        let diff = (result.value() - 0.58).abs();
        assert!(diff < 1e-9, "expected 0.58 but got {}", result.value());
    }

    #[test]
    fn test_apply_decay_zero_hours() {
        let engine = InferenceEngine::new();
        // decay with 0 hours → e^0 = 1.0 → probability unchanged
        let p = prob(0.75);
        let result = engine.apply_decay(p, 0.0).unwrap();
        let diff = (result.value() - 0.75).abs();
        assert!(diff < 1e-9, "expected 0.75 but got {}", result.value());
    }

    #[test]
    fn test_is_contradicting_both_high() {
        let engine = InferenceEngine::new();
        let a = Belief::new("claim A".to_string(), 0.8, 0.9).unwrap();
        let b = Belief::new("claim B".to_string(), 0.9, 0.8).unwrap();
        assert!(engine.is_contradicting(&a, &b));
    }

    #[test]
    fn test_is_contradicting_one_low() {
        let engine = InferenceEngine::new();
        let a = Belief::new("claim A".to_string(), 0.8, 0.9).unwrap();
        let b = Belief::new("claim B".to_string(), 0.3, 0.8).unwrap();
        assert!(!engine.is_contradicting(&a, &b));
    }
}
