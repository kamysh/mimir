//! Versioned learning assessments. These never update generic graph probability.
use crate::learning::{BeliefTarget, Experience, ObservationSource};
use anyhow::{ensure, Result};
use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use uuid::Uuid;

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ItemKind {
    Estimate,
    Decision,
    Suggestion,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Prediction {
    pub quantity: String,
    pub value: f64,
    pub unit: String,
    pub probability: Option<f64>,
    pub lower: Option<f64>,
    pub upper: Option<f64>,
    pub horizon: String,
    pub recorded_at: String,
    pub inferred: bool,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LearningItem {
    /// Present on stored/read-back items; new declarations use a local key.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub id: Option<Uuid>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub key: Option<String>,
    pub kind: ItemKind,
    pub source_ref: String,
    pub actor: String,
    pub statement: String,
    pub conditions: String,
    #[serde(default)]
    pub predictions: Vec<Prediction>,
}

fn nonempty(s: &str) -> Result<()> {
    ensure!(
        !s.trim().is_empty(),
        "text must contain a non-whitespace character"
    );
    Ok(())
}
fn range(x: f64, min: f64, max: f64) -> Result<()> {
    ensure!(
        x.is_finite() && (min..=max).contains(&x),
        "invalid finite assessment range"
    );
    Ok(())
}
pub(crate) fn validate_local_key(key: &str, path: Vec<crate::validation::Segment>) -> Result<()> {
    use crate::{interaction::RequestCorrection, validation::Code};
    if key.trim().is_empty() {
        return Err(RequestCorrection::local_key(
            path,
            Code::EmptyText,
            "The local key is empty or contains only whitespace.".into(),
        )
        .into());
    }
    if key != key.trim() {
        return Err(RequestCorrection::local_key(path, Code::MalformedInput,
            "The local key has leading or trailing whitespace; its identity cannot be silently changed.".into()).into());
    }
    Ok(())
}

pub fn validate_items(items: &[LearningItem]) -> Result<()> {
    let mut ids = HashSet::new();
    let mut keys = HashSet::new();
    for (index, item) in items.iter().enumerate() {
        if item.id.is_none() && item.key.is_none() {
            return Err(crate::interaction::RequestCorrection::learning_item(
                vec![
                    crate::validation::Segment::Index(index),
                    crate::validation::Segment::Key("key".into()),
                ],
                crate::validation::Code::MissingReference,
                "learning item requires a key or an existing ID".into(),
            )
            .into());
        }
        if let Some(id) = item.id {
            ensure!(ids.insert(id), "duplicate learning item ID");
        }
        if let Some(key) = &item.key {
            let path = vec![
                crate::validation::Segment::Index(index),
                crate::validation::Segment::Key("key".into()),
            ];
            validate_local_key(key, path.clone())?;
            if !keys.insert(key) {
                return Err(crate::interaction::RequestCorrection::local_key(
                    path,
                    crate::validation::Code::Duplicate,
                    format!("Learning item at index {index} repeats key {key:?}."),
                )
                .into());
            }
        }
        for text in [
            &item.source_ref,
            &item.actor,
            &item.statement,
            &item.conditions,
        ] {
            nonempty(text)?;
        }
        for p in &item.predictions {
            for text in [&p.quantity, &p.unit, &p.horizon, &p.recorded_at] {
                nonempty(text)?;
            }
            ensure!(p.value.is_finite(), "prediction must be finite");
            if let Some(v) = p.probability {
                range(v, 0., 1.)?;
            }
            ensure!(
                p.lower.is_some() == p.upper.is_some(),
                "interval requires both bounds"
            );
            if let (Some(lo), Some(hi)) = (p.lower, p.upper) {
                ensure!(
                    lo.is_finite() && hi.is_finite() && lo <= p.value && p.value <= hi,
                    "invalid prediction interval"
                );
            }
        }
    }
    Ok(())
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Axis {
    /// None means unresolved; it must carry zero weight.
    pub value: Option<f64>,
    pub weight: f64,
}
impl Axis {
    fn validate(&self, min: f64) -> Result<()> {
        range(self.weight, 0., 1.)?;
        if let Some(v) = self.value {
            range(v, min, 1.)?;
        }
        ensure!(
            self.value.is_some() || self.weight == 0.,
            "unresolved axis cannot contribute evidence"
        );
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Assessment {
    pub target: BeliefTarget,
    pub scope: String,
    pub rubric: String,
    pub correctness: Axis,
    pub usefulness: Axis,
    /// Indices refer to the immutable reviewed experience version.
    pub evidence_indices: Vec<usize>,
    #[serde(default)]
    pub item_ids: Vec<Uuid>,
    /// Experience-local references, resolved to UUIDs before persistence.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub item_keys: Vec<String>,
    pub rationale: String,
}
impl Assessment {
    pub fn validate(&self) -> Result<()> {
        nonempty(&self.scope)?;
        nonempty(&self.rubric)?;
        nonempty(&self.rationale)?;
        self.correctness.validate(0.)?;
        self.usefulness.validate(-1.)?;
        ensure!(
            self.evidence_indices.iter().collect::<HashSet<_>>().len()
                == self.evidence_indices.len(),
            "duplicate evidence reference"
        );
        ensure!(
            self.item_ids.iter().collect::<HashSet<_>>().len() == self.item_ids.len(),
            "duplicate item reference"
        );
        let mut keys = HashSet::new();
        for (index, key) in self.item_keys.iter().enumerate() {
            let path = vec![
                crate::validation::Segment::Key("item_keys".into()),
                crate::validation::Segment::Index(index),
            ];
            validate_local_key(key, path.clone())?;
            if !keys.insert(key) {
                return Err(crate::interaction::RequestCorrection::local_key(
                    path,
                    crate::validation::Code::Duplicate,
                    format!("Item reference at index {index} repeats key {key:?}."),
                )
                .into());
            }
        }
        if self.correctness.weight > 0. || self.usefulness.weight > 0. {
            ensure!(
                !self.evidence_indices.is_empty(),
                "weighted assessment requires evidence"
            );
        }
        Ok(())
    }
    pub fn validate_source(&self, experience: &Experience) -> Result<()> {
        self.validate()?;
        ensure!(
            self.item_keys.is_empty(),
            "item keys must be resolved before source validation"
        );
        for i in &self.evidence_indices {
            ensure!(
                experience
                    .evidence
                    .get(*i)
                    .is_some_and(|s| !s.trim().is_empty()),
                "missing assessment evidence"
            );
        }
        for id in &self.item_ids {
            ensure!(
                experience.learning_items.iter().any(|i| i.id == Some(*id)),
                "missing learning item"
            );
        }
        let observed = if experience.source_records.is_empty() {
            experience.source != ObservationSource::AgentReport
        } else {
            self.evidence_indices.iter().any(|i| {
                experience
                    .source_records
                    .get(*i)
                    .is_some_and(|s| s.provenance != ObservationSource::AgentReport)
            })
        };
        if !observed {
            ensure!(
                self.correctness.weight == 0. && self.usefulness.weight == 0.,
                "agent report alone is not observed evidence"
            );
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Scores {
    pub model_version: u32,
    pub correctness: f64,
    pub usefulness: f64,
    pub alpha: f64,
    pub beta: f64,
    pub benefit_sum: f64,
    pub correctness_mass: f64,
    pub usefulness_mass: f64,
    pub correctness_spread: f64,
    pub incidents: i64,
    pub unresolved_correctness: i64,
    pub unresolved_usefulness: i64,
    pub calibrated: bool,
}
impl Scores {
    pub(crate) fn from_totals(
        pos: f64,
        neg: f64,
        benefit_sum: f64,
        usefulness_mass: f64,
        incidents: i64,
        unresolved_correctness: i64,
        unresolved_usefulness: i64,
    ) -> Result<Self> {
        ensure!(
            [pos, neg, benefit_sum, usefulness_mass]
                .iter()
                .all(|x| x.is_finite()),
            "nonfinite aggregate"
        );
        ensure!(
            pos >= 0. && neg >= 0. && usefulness_mass >= 0.,
            "negative evidence mass"
        );
        ensure!(
            benefit_sum.abs() <= usefulness_mass + 1e-12,
            "benefit exceeds evidence mass"
        );
        let alpha = 1. + pos;
        let beta = 1. + neg;
        Ok(Self {
            model_version: 1,
            correctness: alpha / (alpha + beta),
            usefulness: benefit_sum / (1. + usefulness_mass),
            alpha,
            beta,
            benefit_sum,
            correctness_mass: pos + neg,
            usefulness_mass,
            correctness_spread: (alpha * beta / ((alpha + beta).powi(2) * (alpha + beta + 1.)))
                .sqrt(),
            incidents,
            unresolved_correctness,
            unresolved_usefulness,
            calibrated: false,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;
    #[test]
    fn explicit_legacy_rejection_can_be_scored_without_source_records() {
        let mut experience: Experience = mimir_json::from_value(serde_json::json!({
            "id":"11111111-1111-4111-8111-111111111111","project":"rejection-fixture",
            "context":"Copying succeeded; scope compliance was rejected",
            "action":"Created unsolicited backups","outcome":"unknown","source":"user_feedback",
            "evidence":["Copying completed", "Remove all backups. Nobody asked you to make them."],
            "belief_ids":[],"pattern_id":null
        }))
        .unwrap();
        let mut assessment: Assessment = mimir_json::from_value(serde_json::json!({
            "target":{"belief_id":"22222222-2222-4222-8222-222222222222"},
            "scope":"This unsolicited-backup decision","rubric":"authorized-and-user-accepted/v1",
            "correctness":{"value":0,"weight":1},"usefulness":{"value":-1,"weight":1},
            "evidence_indices":[1],"rationale":"Explicit user rejection of authorization and benefit; no claim of technical failure"
        })).unwrap();
        assessment.validate_source(&experience).unwrap();
        let score = Scores::from_totals(0., 1., -1., 1., 1, 0, 0).unwrap();
        assert_eq!(score.correctness, 1. / 3.);
        assert_eq!(score.usefulness, -0.5);
        // Technical correctness can remain unknown while benefit is observed.
        assessment.correctness = Axis {
            value: None,
            weight: 0.,
        };
        assessment.validate_source(&experience).unwrap();
        assessment.evidence_indices.clear();
        assert!(assessment.validate_source(&experience).is_err());
        assessment.evidence_indices = vec![2];
        assert!(assessment.validate_source(&experience).is_err());
        assessment.evidence_indices = vec![1];
        experience.source = ObservationSource::AgentReport;
        assert!(assessment.validate_source(&experience).is_err());
        // Structured provenance overrides the root and cannot flow to neighbors.
        experience.source = ObservationSource::UserFeedback;
        experience.evidence = vec!["agent".into(), "human".into()];
        experience.source_records=mimir_json::from_value(serde_json::json!([
            {"source_ref":"agent","actor":"agent","provenance":"agent_report","text":"Copy succeeded"},
            {"source_ref":"human","actor":"human","provenance":"user_feedback","text":"Nobody asked you to make them"}
        ])).unwrap();
        assessment.evidence_indices = vec![0];
        assert!(assessment.validate_source(&experience).is_err());
        assessment.evidence_indices = vec![1];
        assessment.validate_source(&experience).unwrap();
    }
    #[test]
    fn numerical_walkthroughs() {
        for (pos, neg, benefit, mass, c, u) in [
            (0., 1., -0.5, 1., 1. / 3., -0.25),
            (0., 0., 0., 0., 0.5, 0.),
            (1., 0., 1., 1., 2. / 3., 0.5),
        ] {
            let score = Scores::from_totals(pos, neg, benefit, mass, 1, 0, 0).unwrap();
            assert!((score.correctness - c).abs() < 1e-12);
            assert!((score.usefulness - u).abs() < 1e-12);
            assert!(!score.calibrated);
        }
    }
    #[test]
    fn rejects_nonfinite_and_unresolved_mass() {
        for v in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY, 1.1, -0.1] {
            assert!(Axis {
                value: Some(v),
                weight: 1.
            }
            .validate(0.)
            .is_err());
        }
        assert!(Axis {
            value: None,
            weight: 1.
        }
        .validate(0.)
        .is_err());
        assert!(Axis {
            value: None,
            weight: 0.
        }
        .validate(0.)
        .is_ok());
        assert!(Scores::from_totals(0., 0., 2., 1., 1, 0, 0).is_err());
    }
    proptest! {
        #[test]
        fn score_bounds(pos in 0f64..100000., neg in 0f64..100000., mass in 0f64..100000., benefit in -1f64..1.) {
            let s=Scores::from_totals(pos,neg,mass*benefit,mass,100,0,0).unwrap();
            prop_assert!((0.0..=1.0).contains(&s.correctness));
            prop_assert!((-1.0..=1.0).contains(&s.usefulness));
            prop_assert!(s.correctness_spread.is_finite());
        }
    }
}
