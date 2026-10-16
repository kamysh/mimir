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
}
impl Experience {
    pub fn validate(&self) -> Result<()> {
        ensure!(!self.project.trim().is_empty(), "project must be explicit");
        ensure!(
            !self.context.trim().is_empty() && !self.action.trim().is_empty(),
            "context and action are required"
        );
        ensure!(
            self.evidence.len() <= 32 && self.belief_ids.len() <= 64,
            "too many evidence references or beliefs"
        );
        ensure!(
            self.outcome == Outcome::Unknown || self.evidence.iter().any(|e| !e.trim().is_empty()),
            "a known outcome requires evidence"
        );
        ensure!(
            serde_json::to_vec(self)?.len() <= 65536,
            "experience exceeds 64 KiB"
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
}
impl Review {
    pub fn validate(&self) -> Result<()> {
        ensure!(
            self.experience_revision > 0,
            "experience_revision must be positive"
        );
        ensure!(
            !self.reviewer.trim().is_empty() && !self.rationale.trim().is_empty(),
            "reviewer and rationale are required"
        );
        ensure!(
            self.feedback.len() <= 64 && self.superseded_beliefs.len() <= 64,
            "review has too many targets"
        );
        ensure!(self.links.len() <= 64, "too many links");
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
        ensure!(
            serde_json::to_vec(self)?.len() <= 65536,
            "review exceeds 64 KiB"
        );
        Ok(())
    }
}
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExperienceState {
    pub experience: Experience,
    pub revision: i64,
    pub review_revision: i64,
    pub reviewed_revision: i64,
}
#[derive(Debug, Clone, Serialize)]
pub struct PatternResult {
    pub pattern: Pattern,
    pub successes: usize,
    pub failures: usize,
    pub unknown: usize,
    /// Beta(1,1) with one observation per distinct experience, not asserted rate.
    pub observed_success_probability: f64,
}
#[derive(Debug, Serialize)]
pub struct LearningContext {
    pub beliefs: Vec<Belief>,
    pub patterns: Vec<PatternResult>,
}

impl crate::MimirService {
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
        limit: usize,
    ) -> Result<LearningContext> {
        ensure!((1..=20).contains(&limit), "limit must be in 1..=20");
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
        Ok(LearningContext {
            beliefs,
            patterns: ranked.into_iter().take(limit).map(|(_, p)| p).collect(),
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
        Ok(serde_json::json!({"belief":belief,"incoming_edges":parents,"learning":reviews}))
    }
}
