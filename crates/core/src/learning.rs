//! Outcome evidence is distinct from an agent's asserted belief confidence.
//! Reviews interpret observations; success alone never proves a belief true.
use crate::graph::{Belief, EdgeType, Pattern};
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
        crate::assessment::validate_items(&self.learning_items)?;
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
        ensure!(
            !key.trim().is_empty() && key == key.trim(),
            "candidate key must be a nonempty trimmed string"
        );
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
        crate::assessment::validate_items(&self.extracted_items)?;
        ensure!(
            self.experience_revision > 0,
            "experience_revision must be positive"
        );
        ensure!(
            !self.reviewer.trim().is_empty() && !self.rationale.trim().is_empty(),
            "reviewer and rationale are required"
        );
        let mut candidate_keys = std::collections::HashSet::new();
        for candidate in &self.candidates {
            candidate.validate()?;
            ensure!(
                candidate_keys.insert(candidate.key()),
                "duplicate candidate key"
            );
        }
        let belief_candidates: std::collections::HashSet<&str> = self
            .candidates
            .iter()
            .filter_map(|candidate| match candidate {
                Candidate::Belief { key, .. } => Some(key.as_str()),
                Candidate::Pattern { .. } => None,
            })
            .collect();
        let validate_target = |target: &BeliefTarget| -> Result<()> {
            if let BeliefTarget::Candidate { candidate_key } = target {
                if !belief_candidates.contains(candidate_key.as_str()) {
                    return Err(crate::validation::Refusal::undeclared_candidate().into());
                }
            }
            Ok(())
        };
        for feedback in &self.candidate_feedback {
            crate::graph::Probability::new(feedback.weight)?;
            validate_target(&feedback.target)?;
        }
        let mut assessment_keys = std::collections::HashSet::new();
        for assessment in &self.assessments {
            assessment.validate()?;
            validate_target(&assessment.target)?;
            ensure!(
                assessment_keys.insert((
                    serde_json::to_string(&assessment.target)?,
                    &assessment.scope,
                    &assessment.rubric
                )),
                "duplicate incident assessment"
            );
            ensure!(
                !self
                    .candidate_feedback
                    .iter()
                    .any(|f| f.target == assessment.target),
                "typed and legacy feedback overlap"
            );
            if let BeliefTarget::Existing { belief_id } = assessment.target {
                ensure!(
                    !self.feedback.iter().any(|f| f.belief_id == belief_id)
                        && !self
                            .links
                            .iter()
                            .any(|l| l.to_id == belief_id || l.from_id == belief_id),
                    "typed and legacy evidence overlap"
                );
            }
            ensure!(
                !self
                    .candidate_links
                    .iter()
                    .any(|l| l.from == assessment.target || l.to == assessment.target),
                "typed and legacy evidence overlap"
            );
        }
        for link in &self.candidate_links {
            crate::graph::Probability::new(link.weight)?;
            validate_target(&link.from)?;
            validate_target(&link.to)?;
        }
        let mut link_keys = std::collections::HashSet::new();
        for link in &self.links {
            crate::graph::Probability::new(link.weight)?;
            ensure!(link.from_id != link.to_id, "self links are not permitted");
            let (a, b) = if link.relation == EdgeType::Contradicts && link.from_id > link.to_id {
                (link.to_id, link.from_id)
            } else {
                (link.from_id, link.to_id)
            };
            ensure!(
                link_keys.insert((a, b, link.relation.as_str())),
                "duplicate relationship"
            );
        }
        let mut seen = std::collections::HashSet::new();
        for f in &self.feedback {
            crate::graph::Probability::new(f.weight)?;
            ensure!(
                seen.insert(f.belief_id),
                "one assessment per belief per experience"
            );
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
        limit: usize,
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
        self.store
            .review_experience(review, expected_review_revision)
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
        limit: usize,
    ) -> Result<Vec<ExperienceState>> {
        self.store.list_experiences(project, true, limit).await
    }
    pub async fn pending_experiences_excluding(
        &self,
        project: Option<&str>,
        limit: usize,
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
        ensure!(!project.trim().is_empty(), "project must be explicit");
        let beliefs = self
            .query_relevant(context, limit, Some(project), None)
            .await?;
        let terms: std::collections::HashSet<_> = context
            .split(|c: char| !c.is_alphanumeric())
            .filter(|t| !t.is_empty())
            .map(str::to_lowercase)
            .collect();
        let mut ranked = Vec::new();
        for pattern in self.list_patterns(Some(project)).await? {
            let tokens: std::collections::HashSet<_> = pattern
                .situation
                .split(|c: char| !c.is_alphanumeric())
                .filter(|t| !t.is_empty())
                .map(str::to_lowercase)
                .collect();
            let hits = terms.intersection(&tokens).count();
            if hits > 0 {
                let result = self.store.pattern_outcomes(pattern, project).await?;
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
            .assessments_for_beliefs(project, &beliefs.iter().map(|b| b.id).collect::<Vec<_>>())
            .await?;
        if let Some(count) = limit {
            ranked.truncate(count.get());
        }
        Ok(LearningContext {
            beliefs,
            patterns: ranked.into_iter().map(|(_, p)| p).collect(),
            assessments,
            assessments_truncated,
        })
    }
}

impl crate::MimirService {
    /// Exposes both the existing reasoning graph and the active observations
    /// behind learned evidence. The review page links to immutable history.
    pub async fn explain_belief(
        &self,
        id: Uuid,
        offset: usize,
        limit: usize,
    ) -> Result<serde_json::Value> {
        let belief = self
            .get_belief(id)
            .await?
            .ok_or_else(|| anyhow::anyhow!("belief not found"))?;
        let incoming = self.store.get_incoming_edges(&[id]).await?;
        let parents: Vec<_> = incoming.iter().map(|(from,to,relation,weight,mean)|serde_json::json!({
            "from_id":from,"to_id":to,"relation":relation,"weight":weight.value(),"source_probability":mean
        })).collect();
        let reviews = self.store.reviews_for_belief(id, offset, limit).await?;
        let candidate_provenance = self.store.candidate_provenance(id).await?;
        let independent_provenance = self.store.independent_provenance(id).await?;
        Ok(
            serde_json::json!({"belief":belief,"incoming_edges":parents,"learning":reviews,"candidate_provenance":candidate_provenance,"independent_provenance":independent_provenance}),
        )
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
        let undeclared = "candidate belief reference must be declared in this review";
        assert!(review
            .validate()
            .unwrap_err()
            .to_string()
            .contains(undeclared));

        review.candidates.push(Candidate::Pattern {
            key: "claim".into(),
            situation: "situation".into(),
            approach: "approach".into(),
        });
        assert!(review
            .validate()
            .unwrap_err()
            .to_string()
            .contains(undeclared));

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
        assert!(review
            .validate()
            .unwrap_err()
            .to_string()
            .contains(undeclared));
        review.candidate_links[0].to = BeliefTarget::Candidate {
            candidate_key: "claim".into(),
        };
        review.validate().unwrap();
    }
}
