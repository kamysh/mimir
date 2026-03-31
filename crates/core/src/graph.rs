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

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Belief {
    pub id: Uuid,
    pub content: String,
    pub probability: Probability,
    pub confidence: Probability,
    pub created_at: DateTime<Utc>,
    pub last_activated_at: DateTime<Utc>,
}

impl Belief {
    pub fn new(content: String, probability: f64, confidence: f64) -> Result<Self> {
        let now = Utc::now();
        Ok(Self {
            id: Uuid::new_v4(),
            content,
            probability: Probability::new(probability)?,
            confidence: Probability::new(confidence)?,
            created_at: now,
            last_activated_at: now,
        })
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
}

impl Pattern {
    pub fn new(situation: String, approach: String) -> Result<Self> {
        Ok(Self {
            id: Uuid::new_v4(),
            situation,
            approach,
            activation_count: 0,
            success_rate: Probability::new(0.5)?,
            created_at: Utc::now(),
        })
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

    pub fn from_str(s: &str) -> anyhow::Result<Self> {
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
    fn belief_construction() {
        let b = Belief::new("the sky is blue".to_string(), 0.9, 0.8).unwrap();
        assert_eq!(b.probability.value(), 0.9);
        assert_eq!(b.confidence.value(), 0.8);
    }

    #[test]
    fn edge_type_variants_exist() {
        let _ = EdgeType::Supports;
        let _ = EdgeType::Defeats;
        let _ = EdgeType::Causes;
        let _ = EdgeType::Contradicts;
    }
}