//! Outcome evidence is distinct from an agent's asserted belief confidence.
//! Reviews interpret observations; success alone never proves a belief true.
use crate::graph::{Belief, EdgeType, Pattern};
use crate::interaction::RequestCorrection;
use crate::validation::{Code, Segment};
use anyhow::{ensure, Result};
use serde::{Deserialize, Serialize};
use uuid::Uuid;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Outcome {
    Success,
    Failure,
    Unknown,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ObservationSource {
    ToolResult,
    UserFeedback,
    AgentReport,
}

/// A direct MCP belief must come from a source independent of a queued
/// experience. Incident-derived conclusions belong to review candidates.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum IndependentBasis {
    UserInstruction,
    Document,
}

impl IndependentBasis {
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::UserInstruction => "user_instruction",
            Self::Document => "document",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct IndependentProvenance {
    pub basis: IndependentBasis,
    pub reference: String,
}

impl IndependentProvenance {
    pub fn validate(&self) -> Result<()> {
        ensure!(
            !self.reference.trim().is_empty() && self.reference == self.reference.trim(),
            "independent provenance needs a trimmed reference"
        );
        Ok(())
    }
}
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Experience {
    /// Caller-stable identity: retry the same incident using the same ID.
    pub id: Uuid,
    pub project: String,
    pub context: String,
    pub action: String,
    pub outcome: Outcome,
    pub source: ObservationSource,
    pub evidence: Vec<String>,
    #[serde(default)]
    pub belief_ids: Vec<Uuid>,
    pub pattern_id: Option<Uuid>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub learning_items: Vec<crate::assessment::LearningItem>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub source_records: Vec<crate::learning_sources::SourceRecord>,
}
impl Experience {
    pub fn validate(&self) -> Result<()> {
        crate::assessment::validate_items(&self.learning_items).map_err(|error| {
            crate::interaction::RequestCorrection::prefix(
                error,
                &[
                    crate::validation::Segment::Key("experience".into()),
                    crate::validation::Segment::Key("learning_items".into()),
                ],
            )
        })?;
        crate::learning_sources::validate_sources(&self.source_records)?;
        ensure!(
            self.source_records.is_empty()
                || (self.source_records.len() == self.evidence.len()
                    && self
                        .source_records
                        .iter()
                        .zip(&self.evidence)
                        .all(|(s, e)| s.source_ref == *e)),
            "source evidence indices must correspond to source references"
        );
        ensure!(!self.project.trim().is_empty(), "project must be explicit");
        ensure!(
            !self.context.trim().is_empty() && !self.action.trim().is_empty(),
            "context and action are required"
        );
        ensure!(
            self.outcome == Outcome::Unknown || self.evidence.iter().any(|e| !e.trim().is_empty()),
            "a known outcome requires evidence"
        );
        Ok(())
    }
}
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Verdict {
    Support,
    Defeat,
}
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Feedback {
    pub belief_id: Uuid,
    pub verdict: Verdict,
    pub weight: f64,
}
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LearningLink {
    pub from_id: Uuid,
    pub to_id: Uuid,
    pub relation: EdgeType,
    pub weight: f64,
}

fn experiential_memory() -> crate::graph::MemoryType {
    crate::graph::MemoryType::Experiential
}

/// A candidate key is stable within one experience. The server owns its UUID.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum Candidate {
    Belief {
        key: String,
        content: String,
        #[serde(default = "experiential_memory")]
        memory_type: crate::graph::MemoryType,
    },
    Pattern {
        key: String,
        situation: String,
        approach: String,
    },
}

impl Candidate {
    pub fn key(&self) -> &str {
        match self {
            Self::Belief { key, .. } | Self::Pattern { key, .. } => key,
        }
    }

    pub fn kind(&self) -> &'static str {
        match self {
            Self::Belief { .. } => "belief",
            Self::Pattern { .. } => "pattern",
        }
    }

    fn validate(&self) -> Result<()> {
        let key = self.key();
        crate::assessment::validate_local_key(key, vec![Segment::Key("key".into())])?;
        match self {
            Self::Belief {
                content,
                memory_type,
                ..
            } => {
                ensure!(
                    !content.trim().is_empty(),
                    "candidate belief content is empty"
                );
                ensure!(
                    *memory_type != crate::graph::MemoryType::Working,
                    "working memory cannot be a review candidate"
                );
            }
            Self::Pattern {
                situation,
                approach,
                ..
            } => ensure!(
                !situation.trim().is_empty() && !approach.trim().is_empty(),
                "candidate pattern situation and approach are required"
            ),
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(untagged)]
pub enum BeliefTarget {
    Existing { belief_id: Uuid },
    Candidate { candidate_key: String },
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CandidateFeedback {
    pub target: BeliefTarget,
    pub verdict: Verdict,
    pub weight: f64,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CandidateLink {
    pub from: BeliefTarget,
    pub to: BeliefTarget,
    pub relation: EdgeType,
    pub weight: f64,
}
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Review {
    pub experience_id: Uuid,
    pub experience_revision: i64,
    pub reviewer: String,
    pub rationale: String,
    #[serde(default)]
    pub feedback: Vec<Feedback>,
    #[serde(default)]
    pub links: Vec<LearningLink>,
    /// Explicit retirement, separate from probabilistic counter-evidence.
    /// Correct a review with an empty list to restore a mistakenly retired belief.
    #[serde(default)]
    pub superseded_beliefs: Vec<Uuid>,
    #[serde(default)]
    pub candidates: Vec<Candidate>,
    #[serde(default)]
    pub candidate_feedback: Vec<CandidateFeedback>,
    #[serde(default)]
    pub candidate_links: Vec<CandidateLink>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub assessments: Vec<crate::assessment::Assessment>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub extracted_items: Vec<crate::assessment::LearningItem>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub source_coverage: Vec<crate::learning_sources::Coverage>,
}
impl Review {
    pub fn validate(&self) -> Result<()> {
        crate::assessment::validate_items(&self.extracted_items).map_err(|error| {
            crate::interaction::RequestCorrection::prefix(
                error,
                &[
                    crate::validation::Segment::Key("review".into()),
                    crate::validation::Segment::Key("extracted_items".into()),
                ],
            )
        })?;
        ensure!(
            self.experience_revision > 0,
            "experience_revision must be positive"
        );
        ensure!(
            !self.reviewer.trim().is_empty() && !self.rationale.trim().is_empty(),
            "reviewer and rationale are required"
        );
        let mut candidate_keys = std::collections::HashSet::new();
        for (index, candidate) in self.candidates.iter().enumerate() {
            candidate.validate().map_err(|error| {
                RequestCorrection::prefix(
                    error,
                    &[
                        Segment::Key("review".into()),
                        Segment::Key("candidates".into()),
                        Segment::Index(index),
                    ],
                )
            })?;
            if !candidate_keys.insert(candidate.key()) {
                return Err(RequestCorrection::candidate_declaration(
                    vec![Segment::Key("review".into()), Segment::Key("candidates".into())], Code::Duplicate,
                    format!("Duplicate candidate key {:?}: declare each candidate key only once in this review.", candidate.key())).into());
            }
        }
        let belief_candidates: std::collections::HashSet<&str> = self
            .candidates
            .iter()
            .filter_map(|candidate| match candidate {
                Candidate::Belief { key, .. } => Some(key.as_str()),
                Candidate::Pattern { .. } => None,
            })
            .collect();
        let target_path = |collection: &str, index: usize, endpoint: &str| {
            vec![
                Segment::Key("review".into()),
                Segment::Key(collection.into()),
                Segment::Index(index),
                Segment::Key(endpoint.into()),
                Segment::Key("candidate_key".into()),
            ]
        };
        let validate_target = |target: &BeliefTarget, path: Vec<Segment>| -> Result<()> {
            if let BeliefTarget::Candidate { candidate_key } = target {
                if !belief_candidates.contains(candidate_key.as_str()) {
                    return Err(RequestCorrection::candidate_target(path,
                        format!("Candidate belief key {candidate_key:?} must be declared by a belief candidate in this review; a pattern key cannot be used as a belief target.")).into());
                }
            }
            Ok(())
        };
        for (index, feedback) in self.candidate_feedback.iter().enumerate() {
            crate::graph::Probability::new(feedback.weight)?;
            validate_target(
                &feedback.target,
                target_path("candidate_feedback", index, "target"),
            )?;
        }
        let mut assessment_keys = std::collections::HashSet::new();
        for (index, assessment) in self.assessments.iter().enumerate() {
            assessment.validate().map_err(|error| {
                RequestCorrection::prefix(
                    error,
                    &[
                        Segment::Key("review".into()),
                        Segment::Key("assessments".into()),
                        Segment::Index(index),
                    ],
                )
            })?;
            validate_target(
                &assessment.target,
                target_path("assessments", index, "target"),
            )?;
            let path = vec![
                Segment::Key("review".into()),
                Segment::Key("assessments".into()),
                Segment::Index(index),
            ];
            if !assessment_keys.insert((
                serde_json::to_string(&assessment.target)?,
                &assessment.scope,
                &assessment.rubric,
            )) {
                return Err(RequestCorrection::review_conflict(path, Code::Duplicate,
                    format!("Assessment at index {index} repeats the same target, scope and rubric."),
                    "Submit one assessment for this target, scope and rubric; reconcile the repeated entries against the recorded evidence before resubmitting.").into());
            }
            let candidate_overlap = self
                .candidate_feedback
                .iter()
                .any(|f| f.target == assessment.target)
                || self
                    .candidate_links
                    .iter()
                    .any(|l| l.from == assessment.target || l.to == assessment.target);
            let existing_overlap = match assessment.target {
                BeliefTarget::Existing { belief_id } => {
                    self.feedback.iter().any(|f| f.belief_id == belief_id)
                        || self
                            .links
                            .iter()
                            .any(|l| l.to_id == belief_id || l.from_id == belief_id)
                }
                _ => false,
            };
            if candidate_overlap || existing_overlap {
                return Err(RequestCorrection::review_conflict(path, Code::UnsupportedCombination,
                    format!("Assessment at index {index} targets a belief also named in feedback, candidate_feedback, links or candidate_links. This would count the same incident through both contribution formats."),
                    "Choose one contribution format for this target: keep its typed assessments and remove the overlapping legacy entries, or revise the review to use only the intended legacy contributions for that target. Preserve the evidence and explain the chosen interpretation.").into());
            }
        }
        for (index, link) in self.candidate_links.iter().enumerate() {
            crate::graph::Probability::new(link.weight)?;
            validate_target(&link.from, target_path("candidate_links", index, "from"))?;
            validate_target(&link.to, target_path("candidate_links", index, "to"))?;
        }
        let mut link_keys = std::collections::HashSet::new();
        for (index, link) in self.links.iter().enumerate() {
            crate::graph::Probability::new(link.weight)?;
            let path = vec![
                Segment::Key("review".into()),
                Segment::Key("links".into()),
                Segment::Index(index),
            ];
            if link.from_id == link.to_id {
                return Err(RequestCorrection::review_conflict(path, Code::UnsupportedCombination,
                    format!("Relationship at index {index} points from belief {} back to itself.", link.from_id),
                    "Use two distinct beliefs returned by list_beliefs, or omit the relationship if no relationship between different beliefs was intended.").into());
            }
            let (a, b) = if link.relation == EdgeType::Contradicts && link.from_id > link.to_id {
                (link.to_id, link.from_id)
            } else {
                (link.from_id, link.to_id)
            };
            if !link_keys.insert((a, b, link.relation.as_str())) {
                return Err(RequestCorrection::review_conflict(path, Code::Duplicate,
                    format!("Relationship at index {index} repeats {} between beliefs {a} and {b}; reversing a contradiction does not make another relationship.", link.relation.as_str()),
                    "Submit each relationship once. Reconcile its repeated weights against the evidence; do not count a reversed contradiction twice.").into());
            }
        }
        let mut seen = std::collections::HashSet::new();
        for (index, f) in self.feedback.iter().enumerate() {
            crate::graph::Probability::new(f.weight)?;
            if !seen.insert(f.belief_id) {
                return Err(RequestCorrection::review_conflict(
                    vec![Segment::Key("review".into()), Segment::Key("feedback".into()), Segment::Index(index)], Code::Duplicate,
                    format!("Feedback at index {index} repeats belief {}; one incident cannot supply multiple legacy feedback entries for that belief.", f.belief_id),
                    "Submit one feedback entry for this belief. Reconcile its verdict and weight against the recorded evidence before resubmitting.").into());
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExperienceState {
    pub experience: Experience,
    pub revision: i64,
    pub review_revision: i64,
    pub reviewed_revision: i64,
    /// Resolved identities for candidates declared by the active review.
    #[serde(default, skip_serializing_if = "std::collections::HashMap::is_empty")]
    pub candidate_ids: std::collections::HashMap<String, Uuid>,
    /// PostgreSQL-assigned identities for experience-local learning item keys.
    #[serde(default, skip_serializing_if = "std::collections::HashMap::is_empty")]
    pub item_ids: std::collections::HashMap<String, Uuid>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CandidateProvenance {
    pub experience_id: Uuid,
    pub candidate_key: String,
    pub kind: String,
    pub active: bool,
    pub retired: bool,
}
#[derive(Debug, Clone, Serialize)]
pub struct PatternResult {
    pub pattern: Pattern,
    pub successes: usize,
    pub failures: usize,
    pub unknown: usize,
    /// Beta(1,1) with one observation per distinct experience, not asserted rate.
    pub observed_success_probability: f64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub candidate_provenance: Option<CandidateProvenance>,
}
#[derive(Debug, Serialize)]
pub struct LearningContext {
    pub beliefs: Vec<Belief>,
    pub patterns: Vec<PatternResult>,
    pub assessments: Vec<serde_json::Value>,
    pub assessments_truncated: bool,
}

impl crate::MimirService {
    pub async fn lesson_assessment(
        &self,
        project: &str,
        belief_id: Uuid,
        scope: &str,
        rubric: &str,
    ) -> Result<serde_json::Value> {
        self.store
            .lesson_assessment(project, belief_id, scope, rubric)
            .await
    }
    pub async fn lesson_assessment_history(
        &self,
        project: &str,
        belief_id: Uuid,
        scope: &str,
        rubric: &str,
        offset: usize,
        limit: crate::Selection,
    ) -> Result<serde_json::Value> {
        self.store
            .lesson_assessment_history(project, belief_id, scope, rubric, offset, limit)
            .await
    }
    pub async fn record_experience(
        &self,
        experience: &Experience,
        expected_revision: i64,
    ) -> Result<ExperienceState> {
        self.store
            .record_experience(experience, expected_revision)
            .await
    }
    pub async fn review_experience(
        &self,
        review: &Review,
        expected_review_revision: i64,
    ) -> Result<ExperienceState> {
        let Some((project, candidates)) = self
            .store
            .review_preparation_candidates(review, expected_review_revision)
            .await?
        else {
            // The transaction reconstructs the original answer without
            // contacting an embedding backend on an exact replay.
            return self
                .store
                .review_experience(review, expected_review_revision)
                .await;
        };
        let mut prepared = std::collections::HashMap::new();
        for (index, candidate) in candidates {
            if let Candidate::Belief {
                key,
                content,
                memory_type,
            } = candidate
            {
                let value = self
                    .prepare_belief(&content, 0.5, 0.0, Some(&project), memory_type, None)
                    .await
                    .map_err(|error| {
                        match error.downcast_ref::<crate::preparation::PreparationRequired>() {
                            Some(decision) => decision.for_review_candidate(index, &key).into(),
                            None => error,
                        }
                    })?;
                prepared.insert(key, value);
            }
        }
        self.store
            .review_experience_prepared(review, expected_review_revision, &prepared)
            .await
    }
    pub async fn get_experience(&self, id: Uuid) -> Result<Option<ExperienceState>> {
        self.store.get_experience(id).await
    }
    pub async fn learning_review(&self, id: Uuid) -> Result<serde_json::Value> {
        self.store.learning_review(id).await
    }
    pub async fn experience_history(&self, id: Uuid) -> Result<serde_json::Value> {
        self.store.experience_history(id).await
    }
    pub async fn pending_experiences(
        &self,
        project: Option<&str>,
        limit: crate::Selection,
    ) -> Result<Vec<ExperienceState>> {
        self.store
            .list_experiences_excluding(project, true, limit, &[])
            .await
    }
    pub async fn pending_experiences_excluding(
        &self,
        project: Option<&str>,
        limit: crate::Selection,
        excluded: &[Uuid],
    ) -> Result<Vec<ExperienceState>> {
        self.store
            .list_experiences_excluding(project, true, limit, excluded)
            .await
    }
    pub async fn add_pattern_in_project(
        &self,
        situation: &str,
        approach: &str,
        success_rate: f64,
        project: Option<&str>,
    ) -> Result<Pattern> {
        let mut pattern = Pattern::new(situation.into(), approach.into(), success_rate)?;
        pattern.project = project.map(str::to_owned);
        self.store.insert_pattern(&pattern).await?;
        Ok(pattern)
    }
    /// Retrieve relevant procedures with observed results alongside beliefs.
    /// Relevance comes first; outcome estimates break ties between equally
    /// relevant procedures. A retrieval never counts as a successful use.
    pub async fn query_learning_context(
        &self,
        context: &str,
        project: &str,
        limit: crate::Selection,
    ) -> Result<LearningContext> {
        self.learning_context_after_beliefs(context, project, limit, || async { Ok(()) })
            .await
    }

    pub(crate) async fn learning_context_after_beliefs<F, W>(
        &self,
        context: &str,
        project: &str,
        limit: crate::Selection,
        after_beliefs: F,
    ) -> Result<LearningContext>
    where
        F: FnOnce() -> W,
        W: std::future::Future<Output = Result<()>>,
    {
        ensure!(!project.trim().is_empty(), "project must be explicit");
        let mut client = self.store.snapshot_connection().await;
        let tx = crate::store::snapshot_transaction(&mut client).await?;
        let beliefs = self
            .relevant_on(tx.client(), context, limit, Some(project), None, || async {
                Ok(())
            })
            .await?;
        after_beliefs().await?;
        let terms: std::collections::HashSet<_> = context
            .split(|c: char| !c.is_alphanumeric())
            .filter(|t| !t.is_empty())
            .map(str::to_lowercase)
            .collect();
        let mut ranked = Vec::new();
        for pattern in self
            .store
            .patterns_by_project_on(tx.client(), project)
            .await?
        {
            let tokens: std::collections::HashSet<_> = pattern
                .situation
                .split(|c: char| !c.is_alphanumeric())
                .filter(|t| !t.is_empty())
                .map(str::to_lowercase)
                .collect();
            let hits = terms.intersection(&tokens).count();
            if hits > 0 {
                let result = self
                    .store
                    .pattern_outcomes_on(tx.client(), pattern, project)
                    .await?;
                ranked.push((hits, result));
            }
        }
        ranked.sort_by(|(a, x), (b, y)| {
            b.cmp(a)
                .then_with(|| {
                    y.observed_success_probability
                        .total_cmp(&x.observed_success_probability)
                })
                .then_with(|| x.pattern.id.cmp(&y.pattern.id))
        });
        let (assessments, assessments_truncated) = self
            .store
            .assessments_for_beliefs_on(
                tx.client(),
                project,
                &beliefs.iter().map(|b| b.id).collect::<Vec<_>>(),
            )
            .await?;
        if let Some(count) = limit {
            ranked.truncate(count.get());
        }
        let result = LearningContext {
            beliefs,
            patterns: ranked.into_iter().map(|(_, p)| p).collect(),
            assessments,
            assessments_truncated,
        };
        tx.commit().await?;
        Ok(result)
    }
}

impl crate::MimirService {
    /// Exposes both the existing reasoning graph and the active observations
    /// behind learned evidence. The review page links to immutable history.
    pub async fn explain_belief(
        &self,
        id: Uuid,
        offset: usize,
        limit: crate::Selection,
    ) -> Result<serde_json::Value> {
        self.store.explain_belief_snapshot(id, offset, limit).await
    }
}

#[cfg(test)]
mod review_validation_tests {
    use super::*;

    #[test]
    fn candidate_references_require_belief_declarations_in_the_same_review() {
        let mut review = Review {
            experience_id: Uuid::new_v4(),
            experience_revision: 1,
            reviewer: "judge".into(),
            rationale: "review evidence".into(),
            feedback: vec![],
            links: vec![],
            superseded_beliefs: vec![],
            candidates: vec![],
            candidate_feedback: vec![CandidateFeedback {
                target: BeliefTarget::Candidate {
                    candidate_key: "claim".into(),
                },
                verdict: Verdict::Support,
                weight: 0.8,
            }],
            candidate_links: vec![],
            assessments: vec![],
            extracted_items: vec![],
            source_coverage: vec![],
        };
        fn missing_target(review: &Review, collection: &str, endpoint: &str) {
            let error = review.validate().unwrap_err();
            let correction = error
                .downcast_ref::<RequestCorrection>()
                .expect("request correction");
            let issue = &correction.correction().issues()[0];
            assert_eq!(issue.fault().code, Code::MissingReference);
            assert_eq!(
                issue.fault().path,
                vec![
                    Segment::Key("review".into()),
                    Segment::Key(collection.into()),
                    Segment::Index(0),
                    Segment::Key(endpoint.into()),
                    Segment::Key("candidate_key".into())
                ]
            );
            assert!(issue.expected().contains("belief candidate"));
            assert!(issue.suggested_correction().contains("list_beliefs"));
        }
        missing_target(&review, "candidate_feedback", "target");

        review.candidates.push(Candidate::Pattern {
            key: "claim".into(),
            situation: "situation".into(),
            approach: "approach".into(),
        });
        missing_target(&review, "candidate_feedback", "target");

        review.candidates[0] = Candidate::Belief {
            key: "claim".into(),
            content: "supported claim".into(),
            memory_type: crate::graph::MemoryType::Experiential,
        };
        review.validate().unwrap();

        review.candidate_feedback.clear();
        review.candidate_links.push(CandidateLink {
            from: BeliefTarget::Existing {
                belief_id: Uuid::new_v4(),
            },
            to: BeliefTarget::Candidate {
                candidate_key: "missing".into(),
            },
            relation: EdgeType::Supports,
            weight: 0.7,
        });
        missing_target(&review, "candidate_links", "to");
        review.candidate_links[0].to = BeliefTarget::Candidate {
            candidate_key: "claim".into(),
        };
        review.validate().unwrap();
    }
}
