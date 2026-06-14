use anyhow::{bail, Result};
use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};
use uuid::Uuid;

/// Validated probability value in [0, 1].
#[derive(Debug, Clone, Copy, PartialEq, Serialize, Deserialize)]
pub struct Probability(f64);

impl Probability {
    pub fn new(v: f64) -> Result<Self> {
        if !(0.0..=1.0).contains(&v) {
            bail!("probability {} is outside [0, 1]", v);
        }
        Ok(Self(v))
    }

    pub fn value(self) -> f64 {
        self.0
    }

    pub fn attenuate(self, factor: f64) -> Self {
        Self((self.0 * factor).clamp(0.0, 1.0))
    }
}

// ---------------------------------------------------------------------------
// Beta(α, β) belief representation (Phase 3)
// ---------------------------------------------------------------------------

/// Prior-mapping constants, documented in one place (see docs/proposals/50).
/// A belief's evidence state is Beta(α, β): mean = α/(α+β) is the probability,
/// strength κ = α+β is the (former) confidence as a real pseudo-count.
pub const KAPPA_MIN: f64 = 2.0;
pub const KAPPA_MAX: f64 = 200.0;
/// Evidence quantum: one unit-weight parent observation contributes this much
/// α (support / causes) or β (defeat). Used by the inference engine.
pub const EVIDENCE_UNIT: f64 = 4.0;

/// Map (probability, confidence) → Beta prior (α₀, β₀):
///   κ  = KAPPA_MIN + c·(KAPPA_MAX − KAPPA_MIN)
///   α₀ = p·κ,  β₀ = (1−p)·κ
/// α₀+β₀ = κ ≥ KAPPA_MIN > 0 always, so mean = α₀/(α₀+β₀) = p is well-defined
/// even at p ∈ {0,1} (one count is 0; mean and strength remain exact).
pub fn prior_from(probability: f64, confidence: f64) -> (f64, f64) {
    let kappa = KAPPA_MIN + confidence * (KAPPA_MAX - KAPPA_MIN);
    (probability * kappa, (1.0 - probability) * kappa)
}

/// The mean of a Beta (α, β): α/(α+β), clamped to [0,1]; ½ for the empty Beta
/// (α+β = 0). The single canonical definition — every site that needs a mean
/// from a bare (α, β) pair (propagation, intervention, persistence) calls this.
pub fn beta_mean(alpha: f64, beta: f64) -> f64 {
    let s = alpha + beta;
    if s > 0.0 {
        (alpha / s).clamp(0.0, 1.0)
    } else {
        0.5
    }
}

/// Recover (mean, confidence) from a Beta (α, β): mean = beta_mean;
/// confidence = (κ − KAPPA_MIN)/(KAPPA_MAX − KAPPA_MIN), clamped to [0,1].
pub(crate) fn beta_to_pc(alpha: f64, beta: f64) -> (f64, f64) {
    let mean = beta_mean(alpha, beta);
    let conf = ((alpha + beta - KAPPA_MIN) / (KAPPA_MAX - KAPPA_MIN)).clamp(0.0, 1.0);
    (mean, conf)
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Belief {
    pub id: Uuid,
    pub content: String,
    /// Cached mean = α/(α+β). The (α,β) pair is the source of truth; this is
    /// kept in sync (via `refresh_cached`) for backward-compatible reads.
    pub probability: Probability,
    /// Cached confidence derived from strength κ = α+β.
    pub confidence: Probability,
    /// Posterior Beta counts (source of truth). α₀,β₀ are the fixed prior.
    pub alpha: f64,
    pub beta: f64,
    pub alpha0: f64,
    pub beta0: f64,
    pub created_at: DateTime<Utc>,
    pub last_activated_at: DateTime<Utc>,
    /// Optional project scope. Beliefs tagged with a project can be bulk-deleted
    /// via `delete_project` when that project's work is complete.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub project: Option<String>,
}

impl Belief {
    pub fn new(content: String, probability: f64, confidence: f64) -> Result<Self> {
        // Validate inputs are in range before mapping to (α₀, β₀).
        let p = Probability::new(probability)?;
        let c = Probability::new(confidence)?;
        let now = Utc::now();
        let (alpha0, beta0) = prior_from(p.value(), c.value());
        Ok(Self {
            id: Uuid::new_v4(),
            content,
            probability: p,
            confidence: c,
            alpha: alpha0,
            beta: beta0,
            alpha0,
            beta0,
            created_at: now,
            last_activated_at: now,
            project: None,
        })
    }

    pub fn new_in_project(
        content: String,
        probability: f64,
        confidence: f64,
        project: String,
    ) -> Result<Self> {
        let mut b = Self::new(content, probability, confidence)?;
        b.project = Some(project);
        Ok(b)
    }

    /// Reconstruct a belief from persisted fields (store / migration). The
    /// cached probability/confidence are derived from the supplied (α, β).
    #[allow(clippy::too_many_arguments)]
    pub fn from_stored(
        id: Uuid,
        content: String,
        alpha: f64,
        beta: f64,
        alpha0: f64,
        beta0: f64,
        created_at: DateTime<Utc>,
        last_activated_at: DateTime<Utc>,
        project: Option<String>,
    ) -> Result<Self> {
        let (mean, conf) = beta_to_pc(alpha, beta);
        Ok(Self {
            id,
            content,
            probability: Probability::new(mean)?,
            confidence: Probability::new(conf)?,
            alpha,
            beta,
            alpha0,
            beta0,
            created_at,
            last_activated_at,
            project,
        })
    }

    /// Mean α/(α+β) — the value the rest of the system reads as "probability".
    pub fn mean(&self) -> Probability {
        let (mean, _) = beta_to_pc(self.alpha, self.beta);
        Probability::new(mean).expect("mean is clamped to [0,1]")
    }

    /// Pseudo-count strength κ = α + β.
    pub fn strength(&self) -> f64 {
        self.alpha + self.beta
    }

    /// Confidence recovered from strength κ.
    pub fn confidence_from_strength(&self) -> Probability {
        let (_, conf) = beta_to_pc(self.alpha, self.beta);
        Probability::new(conf).expect("confidence is clamped to [0,1]")
    }

    /// Refresh the cached probability/confidence from the current (α, β).
    /// Call after any update to α/β (propagation, decay).
    pub fn refresh_cached(&mut self) {
        self.probability = self.mean();
        self.confidence = self.confidence_from_strength();
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Pattern {
    pub id: Uuid,
    pub situation: String,
    pub approach: String,
    pub activation_count: u32,
    pub success_rate: Probability,
    pub created_at: DateTime<Utc>,
    pub project: Option<String>,
}

impl Pattern {
    pub fn new(situation: String, approach: String, success_rate: f64) -> Result<Self> {
        Ok(Self {
            id: Uuid::new_v4(),
            situation,
            approach,
            activation_count: 0,
            success_rate: Probability::new(success_rate)?,
            created_at: Utc::now(),
            project: None,
        })
    }

    pub fn new_in_project(
        situation: String,
        approach: String,
        success_rate: f64,
        project: String,
    ) -> Result<Self> {
        let mut p = Self::new(situation, approach, success_rate)?;
        p.project = Some(project);
        Ok(p)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum EdgeType {
    Supports,
    Defeats,
    Causes,
    Contradicts,
}

impl EdgeType {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Supports => "SUPPORTS",
            Self::Defeats => "DEFEATS",
            Self::Causes => "CAUSES",
            Self::Contradicts => "CONTRADICTS",
        }
    }
}

impl std::str::FromStr for EdgeType {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self> {
        match s {
            "SUPPORTS" => Ok(Self::Supports),
            "DEFEATS" => Ok(Self::Defeats),
            "CAUSES" => Ok(Self::Causes),
            "CONTRADICTS" => Ok(Self::Contradicts),
            other => bail!("unknown edge type: {}", other),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Edge {
    pub from_id: Uuid,
    pub to_id: Uuid,
    pub edge_type: EdgeType,
    pub weight: Probability,
}

impl Edge {
    pub fn new(from_id: Uuid, to_id: Uuid, edge_type: EdgeType, weight: f64) -> Result<Self> {
        Ok(Self {
            from_id,
            to_id,
            edge_type,
            weight: Probability::new(weight)?,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;
    use std::str::FromStr;

    // ------------------------------------------------------------------
    // Beta(α, β) representation — round-trip & mapping (Phase 3)
    // ------------------------------------------------------------------

    #[test]
    fn beta_prior_round_trips_p_and_c() {
        // (p, c) → (α₀, β₀) → mean/strength must recover p exactly and a
        // monotone function of c. κ = 2 + 0.5·198 = 101.
        let b = Belief::new("x".to_string(), 0.8, 0.5).unwrap();
        assert!(
            (b.mean().value() - 0.8).abs() < 1e-12,
            "mean {}",
            b.mean().value()
        );
        assert!(
            (b.strength() - 101.0).abs() < 1e-9,
            "strength {}",
            b.strength()
        );
        // posterior starts at the prior
        assert!((b.alpha - b.alpha0).abs() < 1e-12);
        assert!((b.beta - b.beta0).abs() < 1e-12);
        assert!((b.alpha0 + b.beta0 - b.strength()).abs() < 1e-9);
        // confidence recovered from strength
        assert!((b.confidence_from_strength().value() - 0.5).abs() < 1e-9);
        // cached fields agree with the (α,β) source of truth
        assert!((b.probability.value() - b.mean().value()).abs() < 1e-12);
    }

    #[test]
    fn beta_strength_monotone_in_confidence() {
        let lo = Belief::new("y".to_string(), 0.8, 0.1).unwrap();
        let hi = Belief::new("z".to_string(), 0.8, 0.9).unwrap();
        assert!(hi.strength() > lo.strength());
        // both still have mean p = 0.8
        assert!((lo.mean().value() - 0.8).abs() < 1e-12);
        assert!((hi.mean().value() - 0.8).abs() < 1e-12);
    }

    #[test]
    fn beta_boundary_probabilities_are_exact() {
        // p ∈ {0, 1}: one count is 0 but α+β = κ > 0, so the mean is exact.
        let zero = Belief::new("a".to_string(), 0.0, 0.5).unwrap();
        let one = Belief::new("b".to_string(), 1.0, 0.5).unwrap();
        assert_eq!(zero.mean().value(), 0.0);
        assert_eq!(one.mean().value(), 1.0);
        assert!(zero.strength() > 0.0 && one.strength() > 0.0);
    }

    // ------------------------------------------------------------------
    // Probability — unit tests
    // ------------------------------------------------------------------

    #[test]
    fn probability_rejects_out_of_range() {
        assert!(Probability::new(1.1).is_err());
        assert!(Probability::new(-0.1).is_err());
    }

    #[test]
    fn probability_accepts_bounds() {
        assert!(Probability::new(0.0).is_ok());
        assert!(Probability::new(1.0).is_ok());
        assert!(Probability::new(0.5).is_ok());
    }

    #[test]
    fn probability_rejects_nan() {
        assert!(Probability::new(f64::NAN).is_err());
    }

    #[test]
    fn probability_rejects_infinity() {
        assert!(Probability::new(f64::INFINITY).is_err());
        assert!(Probability::new(f64::NEG_INFINITY).is_err());
    }

    #[test]
    fn probability_attenuate_by_zero_gives_zero() {
        let p = Probability::new(0.9).unwrap();
        assert_eq!(p.attenuate(0.0).value(), 0.0);
    }

    #[test]
    fn probability_attenuate_by_one_unchanged() {
        let p = Probability::new(0.7).unwrap();
        assert!((p.attenuate(1.0).value() - 0.7).abs() < 1e-12);
    }

    #[test]
    fn probability_attenuate_result_clamped_above_one() {
        // factor > 1 → clamp to 1.0
        let p = Probability::new(0.9).unwrap();
        assert_eq!(p.attenuate(2.0).value(), 1.0);
    }

    #[test]
    fn probability_attenuate_result_clamped_below_zero() {
        // factor < 0 → 0.9 * -1 = -0.9 → clamped to 0.0
        let p = Probability::new(0.9).unwrap();
        assert_eq!(p.attenuate(-1.0).value(), 0.0);
    }

    #[test]
    fn probability_value_roundtrip() {
        let v = 0.314159;
        let p = Probability::new(v).unwrap();
        assert!((p.value() - v).abs() < 1e-15);
    }

    // ------------------------------------------------------------------
    // EdgeType — unit tests
    // ------------------------------------------------------------------

    #[test]
    fn edge_type_variants_exist() {
        let _ = EdgeType::Supports;
        let _ = EdgeType::Defeats;
        let _ = EdgeType::Causes;
        let _ = EdgeType::Contradicts;
    }

    #[test]
    fn edge_type_supports_roundtrip() {
        assert_eq!(EdgeType::from_str("SUPPORTS").unwrap(), EdgeType::Supports);
        assert_eq!(EdgeType::Supports.as_str(), "SUPPORTS");
    }

    #[test]
    fn edge_type_defeats_roundtrip() {
        assert_eq!(EdgeType::from_str("DEFEATS").unwrap(), EdgeType::Defeats);
        assert_eq!(EdgeType::Defeats.as_str(), "DEFEATS");
    }

    #[test]
    fn edge_type_causes_roundtrip() {
        assert_eq!(EdgeType::from_str("CAUSES").unwrap(), EdgeType::Causes);
        assert_eq!(EdgeType::Causes.as_str(), "CAUSES");
    }

    #[test]
    fn edge_type_contradicts_roundtrip() {
        assert_eq!(
            EdgeType::from_str("CONTRADICTS").unwrap(),
            EdgeType::Contradicts
        );
        assert_eq!(EdgeType::Contradicts.as_str(), "CONTRADICTS");
    }

    #[test]
    fn edge_type_unknown_str_fails() {
        assert!(EdgeType::from_str("UNKNOWN").is_err());
        assert!(EdgeType::from_str("").is_err());
        assert!(EdgeType::from_str("supports").is_err()); // case-sensitive
    }

    // ------------------------------------------------------------------
    // Belief — unit tests
    // ------------------------------------------------------------------

    #[test]
    fn belief_construction() {
        let b = Belief::new("the sky is blue".to_string(), 0.9, 0.8).unwrap();
        assert_eq!(b.probability.value(), 0.9);
        assert_eq!(b.confidence.value(), 0.8);
    }

    #[test]
    fn belief_boundary_probabilities() {
        let b = Belief::new("edge case".to_string(), 0.0, 1.0).unwrap();
        assert_eq!(b.probability.value(), 0.0);
        assert_eq!(b.confidence.value(), 1.0);
    }

    #[test]
    fn belief_invalid_probability_fails() {
        assert!(Belief::new("bad".to_string(), 1.5, 0.5).is_err());
        assert!(Belief::new("bad".to_string(), -0.1, 0.5).is_err());
    }

    #[test]
    fn belief_invalid_confidence_fails() {
        assert!(Belief::new("bad".to_string(), 0.5, 1.1).is_err());
        assert!(Belief::new("bad".to_string(), 0.5, -0.1).is_err());
    }

    #[test]
    fn belief_has_unique_ids() {
        let b1 = Belief::new("same content".to_string(), 0.5, 0.5).unwrap();
        let b2 = Belief::new("same content".to_string(), 0.5, 0.5).unwrap();
        assert_ne!(b1.id, b2.id);
    }

    // ------------------------------------------------------------------
    // Pattern — unit tests
    // ------------------------------------------------------------------

    #[test]
    fn pattern_new_valid() {
        let p = Pattern::new("situation".to_string(), "approach".to_string(), 0.8).unwrap();
        assert_eq!(p.activation_count, 0);
        assert!((p.success_rate.value() - 0.8).abs() < 1e-12);
    }

    #[test]
    fn pattern_invalid_success_rate_fails() {
        assert!(Pattern::new("s".to_string(), "a".to_string(), 1.2).is_err());
        assert!(Pattern::new("s".to_string(), "a".to_string(), -0.1).is_err());
    }

    // ------------------------------------------------------------------
    // Edge — unit tests
    // ------------------------------------------------------------------

    #[test]
    fn edge_new_valid() {
        let from = uuid::Uuid::new_v4();
        let to = uuid::Uuid::new_v4();
        let e = Edge::new(from, to, EdgeType::Supports, 0.6).unwrap();
        assert_eq!(e.from_id, from);
        assert_eq!(e.to_id, to);
        assert!((e.weight.value() - 0.6).abs() < 1e-12);
    }

    #[test]
    fn edge_new_invalid_weight_fails() {
        let id = uuid::Uuid::new_v4();
        assert!(Edge::new(id, id, EdgeType::Supports, -0.1).is_err());
        assert!(Edge::new(id, id, EdgeType::Supports, 1.1).is_err());
    }

    // ------------------------------------------------------------------
    // Proptest — property-based tests
    // ------------------------------------------------------------------

    proptest! {
        #[test]
        fn prop_probability_valid_range_accepted(v in 0.0f64..=1.0f64) {
            prop_assert!(Probability::new(v).is_ok());
        }

        #[test]
        fn prop_probability_gt_one_rejected(v in 1.0001f64..=1e10f64) {
            prop_assert!(Probability::new(v).is_err());
        }

        #[test]
        fn prop_probability_negative_rejected(v in -1e10f64..=-0.0001f64) {
            prop_assert!(Probability::new(v).is_err());
        }

        #[test]
        fn prop_attenuate_stays_in_range(
            p in 0.0f64..=1.0f64,
            factor in 0.0f64..=2.0f64,
        ) {
            let prob = Probability::new(p).unwrap();
            let result = prob.attenuate(factor);
            prop_assert!(result.value() >= 0.0);
            prop_assert!(result.value() <= 1.0);
        }

        #[test]
        fn prop_edge_type_roundtrip(idx in 0usize..4usize) {
            let variants = [
                EdgeType::Supports,
                EdgeType::Defeats,
                EdgeType::Causes,
                EdgeType::Contradicts,
            ];
            let et = variants[idx];
            prop_assert_eq!(EdgeType::from_str(et.as_str()).unwrap(), et);
        }

        #[test]
        fn prop_probability_value_preserved(v in 0.0f64..=1.0f64) {
            let p = Probability::new(v).unwrap();
            prop_assert!((p.value() - v).abs() < 1e-15);
        }
    }
}
