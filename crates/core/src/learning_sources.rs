//! Source coverage belongs to the existing judge, never a second analyzer.
use crate::{
    assessment::validate_items,
    learning::{Experience, ObservationSource, Review},
};
use anyhow::{ensure, Result};
use serde::{Deserialize, Serialize};
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SourceRecord {
    pub source_ref: String,
    pub actor: String,
    pub provenance: ObservationSource,
    pub text: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub recorded_at: Option<String>,
}
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CoverageStatus {
    Complete,
    Unresolved,
}
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Coverage {
    pub source_ref: String,
    pub status: CoverageStatus,
    pub reason: String,
}
pub fn validate_sources(sources: &[SourceRecord]) -> Result<()> {
    let mut seen = HashSet::new();
    for s in sources {
        ensure!(
            s.recorded_at.as_ref().is_none_or(|t| !t.is_empty()),
            "invalid source timestamp"
        );
        ensure!(
            !s.source_ref.trim().is_empty() && !s.actor.trim().is_empty() && !s.text.is_empty(),
            "invalid learning source"
        );
        ensure!(seen.insert(&s.source_ref), "duplicate learning source");
    }
    Ok(())
}
pub fn validate_review(review: &Review, experience: &Experience) -> Result<()> {
    validate_items(&review.extracted_items)?;
    if experience.source_records.is_empty() {
        ensure!(
            review.source_coverage.is_empty() && review.extracted_items.is_empty(),
            "extraction requires source records"
        );
        return Ok(());
    }
    ensure!(
        review.feedback.is_empty()
            && review.candidate_feedback.is_empty()
            && review.links.is_empty()
            && review.candidate_links.is_empty(),
        "source reviews use typed assessments, not legacy evidence contributions"
    );
    let sources: HashMap<_, _> = experience
        .source_records
        .iter()
        .map(|s| (&s.source_ref, s))
        .collect();
    let mut seen = HashSet::new();
    ensure!(
        review.source_coverage.len() == sources.len(),
        "every source needs explicit coverage"
    );
    for c in &review.source_coverage {
        ensure!(
            sources.contains_key(&c.source_ref) && seen.insert(&c.source_ref),
            "invalid or duplicate coverage reference"
        );
        ensure!(!c.reason.trim().is_empty(), "coverage needs a reason");
    }
    let mut ids: HashSet<_> = experience.learning_items.iter().map(|i| i.id).collect();
    for (index, item) in review.extracted_items.iter().enumerate() {
        let source = sources
            .get(&item.source_ref)
            .ok_or_else(|| anyhow::anyhow!("extracted item has no source"))?;
        ensure!(
            source.actor == item.actor && ids.insert(item.id),
            "extracted item provenance or identity conflict"
        );
        // Statement is an exact quotation. Interpretations belong in conditions/rationale.
        if !source.text.contains(&item.statement) {
            use crate::validation::{Code, Refusal, Segment};
            return Err(Refusal::invalid(
                Code::QuotationMismatch,
                vec![Segment::Key("extracted_items".into()), Segment::Index(index), Segment::Key("statement".into())],
                format!("extracted statement is not in its cited source: extracted_items[{index}].statement (item {}, source {}). Copy an exact contiguous substring of that source record's text. Preserve literal backslashes, escaped quotes and whitespace when the text contains serialized JSON; put interpretation in conditions.", item.id, item.source_ref),
            ).into());
        }
    }
    // Each extracted item must participate in an assessment or be explicitly
    // unresolved; completeness is the judge's claim, not semantic proof.
    for item in &review.extracted_items {
        let unresolved = review
            .source_coverage
            .iter()
            .any(|c| c.source_ref == item.source_ref && c.status == CoverageStatus::Unresolved);
        ensure!(
            unresolved
                || review
                    .assessments
                    .iter()
                    .any(|a| a.item_ids.contains(&item.id)),
            "extracted item has neither assessment nor unresolved coverage"
        );
    }
    Ok(())
}

#[cfg(test)]
mod complete_input_tests {
    use super::*;
    use serde_json::json;
    use uuid::Uuid;

    #[test]
    fn full_review_survives_former_size_and_count_caps_without_relaxing_provenance() {
        let sources: Vec<_> = (0..65)
            .map(|n| SourceRecord {
                source_ref: format!("source-{n}-{}", "r".repeat(1001)),
                actor: "a".repeat(201),
                provenance: ObservationSource::AgentReport,
                text: "statement ".repeat(1500),
                recorded_at: None,
            })
            .collect();
        let experience = Experience {
            id: Uuid::new_v4(),
            project: "large-review".into(),
            context: "complete source".into(),
            action: "review all recommendations".into(),
            outcome: crate::learning::Outcome::Unknown,
            source: ObservationSource::AgentReport,
            evidence: sources.iter().map(|s| s.source_ref.clone()).collect(),
            belief_ids: Vec::new(),
            pattern_id: None,
            learning_items: Vec::new(),
            source_records: sources,
        };
        experience.validate().unwrap();
        let items: Vec<_> = experience
            .source_records
            .iter()
            .map(|s| {
                json!({
                    "id":Uuid::new_v4(), "kind":"suggestion", "statement":s.text,
                    "actor":s.actor, "source_ref":s.source_ref, "conditions":"context".repeat(1000),
                    "predictions":[]
                })
            })
            .collect();
        let coverage: Vec<_> = experience.source_records.iter().map(|s| json!({
            "source_ref":s.source_ref,"status":"unresolved","reason":"Awaiting independent evidence. ".repeat(200)
        })).collect();
        let mut review: Review = serde_json::from_value(json!({
            "experience_id":experience.id,"experience_revision":1,"reviewer":"fixture","rationale":"complete input",
            "extracted_items":items,"source_coverage":coverage
        })).unwrap();
        review.validate().unwrap();
        validate_review(&review, &experience).unwrap();
        assert!(serde_json::to_vec(&review).unwrap().len() > 65536);
        review.extracted_items[0].statement = "This quotation never occurred.".into();
        assert!(validate_review(&review, &experience).is_err());
        let mut duplicated = experience.source_records.clone();
        duplicated.push(duplicated[0].clone());
        assert!(validate_sources(&duplicated).is_err());
    }
}
