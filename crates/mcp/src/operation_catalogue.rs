//! Closed registrations for the existing public tools. Argument admission and
//! operation-journal binding follow separately; Input is the current raw JSON.
use anyhow::{anyhow, ensure, Result};
use mimir_core::MimirService;
use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet};

pub type Input = Value;

/// Stable names for actual business publication sites, not every SQL query in
/// a transaction. Instrumentation and native/spec comparison follow in #88.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CommitSite {
    BeliefPublication,
    BeliefVectorPublication,
    EvidencePublication,
    BeliefDeletion,
    ProjectBeliefDeletion,
    ProjectPatternDeletion,
    BeliefVectorDeletion,
    ChunkDeletion,
    ChunkVectorDeletion,
    ProjectLearningDeletion,
    PatternPublication,
    PatternDeletion,
    EdgePublication,
    ContradictionPublication,
    Propagation,
    Decay,
    DocumentReplacement,
    DocumentDeletion,
    ExperiencePublication,
    ReviewPublication,
}

impl CommitSite {
    pub fn name(self) -> &'static str {
        match self {
            Self::BeliefPublication => "store.insert_belief_with_provenance",
            Self::BeliefVectorPublication => "store.insert_belief_embedding",
            Self::EvidencePublication => "store.insert_evidence",
            Self::BeliefDeletion => "store.delete_belief",
            Self::ProjectBeliefDeletion => "store.delete_project.beliefs",
            Self::ProjectPatternDeletion => "store.delete_project.patterns",
            Self::BeliefVectorDeletion => "store.delete_belief_embeddings",
            Self::ChunkDeletion => "store.delete_document_chunks",
            Self::ChunkVectorDeletion => "store.delete_chunk_embeddings",
            Self::ProjectLearningDeletion => "store.delete_learning_project",
            Self::PatternPublication => "store.insert_pattern",
            Self::PatternDeletion => "store.delete_pattern",
            Self::EdgePublication => "store.insert_edge",
            Self::ContradictionPublication => "store.insert_contradicts",
            Self::Propagation => "store.propagate_locked",
            Self::Decay => "store.decay_locked",
            Self::DocumentReplacement => "store.replace_document",
            Self::DocumentDeletion => "store.clear_document",
            Self::ExperiencePublication => "store.record_experience",
            Self::ReviewPublication => "store.review_experience",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CommitBoundary {
    pub site: CommitSite,
    /// A reachable site can repeat for selected rows/groundings. This records
    /// control flow; it imposes no execution count or work limit.
    pub may_repeat: bool,
}
const fn once(site: CommitSite) -> CommitBoundary {
    CommitBoundary {
        site,
        may_repeat: false,
    }
}
const fn repeated(site: CommitSite) -> CommitBoundary {
    CommitBoundary {
        site,
        may_repeat: true,
    }
}

macro_rules! operations {
    (graph { $($graph:ident => $graph_name:literal [$($graph_boundary:expr),* $(,)?]),* $(,)? }
     learning { $($learning:ident => $learning_name:literal [$($learning_boundary:expr),* $(,)?]),* $(,)? }) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub enum GraphOperation { $($graph),* }
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub enum LearningOperation { $($learning),* }
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub enum Operation { Graph(GraphOperation), Learning(LearningOperation) }
        impl Operation {
            pub const ALL: &'static [Self] = &[$(Self::Graph(GraphOperation::$graph)),*, $(Self::Learning(LearningOperation::$learning)),*];
            pub fn name(self) -> &'static str {
                match self { $(Self::Graph(GraphOperation::$graph) => $graph_name),*, $(Self::Learning(LearningOperation::$learning) => $learning_name),* }
            }
            pub fn committed_boundaries(self) -> &'static [CommitBoundary] {
                match self {
                    $(Self::Graph(GraphOperation::$graph) => { const PLAN: &[CommitBoundary] = &[$($graph_boundary),*]; PLAN }),*,
                    $(Self::Learning(LearningOperation::$learning) => { const PLAN: &[CommitBoundary] = &[$($learning_boundary),*]; PLAN }),*
                }
            }
            async fn call(self, service: &MimirService, input: &Input) -> Result<Value> {
                match self {
                    Self::Graph(operation) => super::handle_graph_call(service, operation, input).await,
                    Self::Learning(operation) => super::learning::call(service, operation, input).await,
                }
            }
        }
    };
}

use CommitSite::*;
operations! {
    graph {
        InsertBelief => "insert_belief" [once(BeliefPublication), once(BeliefVectorPublication), repeated(EvidencePublication)],
        DeleteBelief => "delete_belief" [once(BeliefDeletion)],
        DeleteProject => "delete_project" [once(ProjectBeliefDeletion), once(ProjectPatternDeletion), once(BeliefVectorDeletion), once(ChunkDeletion), once(ChunkVectorDeletion), once(ProjectLearningDeletion)],
        DeletePattern => "delete_pattern" [once(PatternDeletion)],
        InsertPattern => "insert_pattern" [once(PatternPublication)],
        RecordSupport => "record_support" [once(EdgePublication)],
        RecordCause => "record_cause" [once(EdgePublication)],
        RecordDefeat => "record_defeat" [once(EdgePublication), once(Propagation)],
        RecordContradiction => "record_contradiction" [once(ContradictionPublication)],
        GetBelief => "get_belief" [],
        ListBeliefs => "list_beliefs" [],
        ListPatterns => "list_patterns" [],
        GetContradictions => "get_contradictions" [],
        DecayAll => "decay_all" [once(Decay)],
        SweepExpiredDefeated => "sweep_expired_defeated" [repeated(BeliefDeletion)],
        QueryRelevant => "query_relevant" [],
        AddEvidence => "add_evidence" [once(EvidencePublication)],
        GetEvidence => "get_evidence" [],
        PropagateFrom => "propagate_from" [once(Propagation)],
        QueryIntervention => "query_intervention" [],
        LoadDocument => "load_document" [once(DocumentReplacement), repeated(EvidencePublication)],
        QueryDocument => "query_document" [],
        ClearDocument => "clear_document" [once(DocumentDeletion)]
    }
    learning {
        LearningCapabilities => "learning_capabilities" [],
        GetLessonAssessment => "get_lesson_assessment" [],
        LessonAssessmentHistory => "lesson_assessment_history" [],
        ExplainBelief => "explain_belief" [],
        GetLearningReview => "get_learning_review" [],
        RecordExperience => "record_experience" [once(ExperiencePublication)],
        PendingExperiences => "pending_experiences" [],
        ReviewExperience => "review_experience" [once(ReviewPublication)],
        GetExperience => "get_experience" [],
        ExperienceHistory => "experience_history" [],
        QueryLearningContext => "query_learning_context" []
    }
}

pub struct RegisteredOperation {
    handler: Operation,
    descriptor: Value,
}
impl RegisteredOperation {
    pub fn handler(&self) -> Operation {
        self.handler
    }
    pub fn input_schema(&self) -> &Value {
        &self.descriptor["inputSchema"]
    }
    pub fn committed_boundaries(&self) -> &'static [CommitBoundary] {
        self.handler.committed_boundaries()
    }
    pub async fn call(&self, service: &MimirService, input: &Input) -> Result<Value> {
        if let Some(correction) = super::admission::arguments(self.input_schema(), input) {
            return Ok(serde_json::to_value(correction)?);
        }
        self.handler.call(service, input).await
    }
}

pub struct Catalogue {
    entries: Vec<RegisteredOperation>,
}
impl Catalogue {
    pub fn new(descriptors: Value) -> Result<Self> {
        let descriptions = descriptors
            .as_array()
            .ok_or_else(|| anyhow!("compiled tool descriptions must be an array"))?;
        let available: BTreeMap<_, _> = Operation::ALL
            .iter()
            .map(|operation| (operation.name(), *operation))
            .collect();
        ensure!(
            available.len() == Operation::ALL.len(),
            "duplicate compiled operation name"
        );
        let mut seen = BTreeSet::new();
        let mut entries = Vec::new();
        for descriptor in descriptions {
            let name = descriptor["name"]
                .as_str()
                .ok_or_else(|| anyhow!("compiled tool description is missing its name"))?;
            ensure!(
                seen.insert(name),
                "duplicate compiled tool description: {name}"
            );
            let handler = available
                .get(name)
                .ok_or_else(|| anyhow!("unregistered compiled tool: {name}"))?;
            ensure!(
                descriptor["inputSchema"].is_object(),
                "compiled tool {name} has no input schema"
            );
            let mut descriptor = descriptor.clone();
            super::admission::close_objects(&mut descriptor["inputSchema"]);
            entries.push(RegisteredOperation {
                handler: *handler,
                descriptor,
            });
        }
        for name in available.keys() {
            ensure!(
                seen.contains(name),
                "registered operation has no advertised input: {name}"
            );
        }
        Ok(Self { entries })
    }
    pub fn entries(&self) -> &[RegisteredOperation] {
        &self.entries
    }
    pub fn advertised(&self) -> Value {
        Value::Array(
            self.entries
                .iter()
                .map(|entry| entry.descriptor.clone())
                .collect(),
        )
    }
    pub fn get(&self, name: &str) -> Option<&RegisteredOperation> {
        self.entries
            .iter()
            .find(|entry| entry.handler.name() == name)
    }
    pub async fn call(&self, service: &MimirService, name: &str, input: &Input) -> Result<Value> {
        match self.get(name) {
            Some(operation) => operation.call(service, input).await,
            None => Ok(serde_json::to_value(super::admission::unknown_tool(
                name,
                &self
                    .entries
                    .iter()
                    .map(|entry| entry.handler().name().to_owned())
                    .collect::<Vec<_>>(),
            ))?),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn actual_entries_preserve_all_advertised_schemas_and_order() {
        let descriptions = super::super::tools_list();
        let catalogue = Catalogue::new(descriptions.clone()).unwrap();
        assert_eq!(catalogue.advertised(), descriptions);
        assert_eq!(catalogue.entries().len(), Operation::ALL.len());
        for entry in catalogue.entries() {
            assert_eq!(
                entry.input_schema(),
                &descriptions
                    .as_array()
                    .unwrap()
                    .iter()
                    .find(|description| description["name"] == entry.handler().name())
                    .unwrap()["inputSchema"]
            );
            let mut sites = BTreeSet::new();
            for boundary in entry.committed_boundaries() {
                assert!(sites.insert(boundary.site.name()));
            }
        }
        assert!(catalogue.get("unregistered_tool").is_none());
    }

    #[test]
    fn missing_duplicate_and_unregistered_descriptions_are_rejected() {
        let original = super::super::tools_list();
        let mut missing = original.clone();
        missing.as_array_mut().unwrap().pop();
        assert!(Catalogue::new(missing).is_err());
        let mut duplicate = original.clone();
        duplicate.as_array_mut().unwrap().push(original[0].clone());
        assert!(Catalogue::new(duplicate).is_err());
        let mut unknown = original.clone();
        unknown
            .as_array_mut()
            .unwrap()
            .push(json!({"name":"unregistered_tool","inputSchema":{}}));
        assert!(Catalogue::new(unknown).is_err());
        let mut no_input = original;
        no_input[0].as_object_mut().unwrap().remove("inputSchema");
        assert!(Catalogue::new(no_input).is_err());
    }
}
