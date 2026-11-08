//! Closed operation names and commit boundaries shared by core storage and MCP.
//! Descriptors, argument admission and handler dispatch remain in their owners.

/// Stable names for actual business publication sites, not every SQL query in
/// a transaction. Instrumentation and native/spec comparison follow in #88.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CommitSite {
    EmbeddingOwnerReservation,
    BeliefPublication,
    BeliefVectorPublication,
    EvidencePublication,
    BeliefDeletion,
    ProjectDeletion,
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
            Self::EmbeddingOwnerReservation => "store.reserve_belief_preparation",
            Self::BeliefPublication => "store.publish_prepared_belief",
            Self::BeliefVectorPublication => "store.insert_belief_embedding",
            Self::EvidencePublication => "store.insert_evidence",
            Self::BeliefDeletion => "store.delete_belief",
            Self::ProjectDeletion => "store.delete_project",
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
        }
    };
}

use CommitSite::*;
operations! {
    graph {
        InsertBelief => "insert_belief" [once(EmbeddingOwnerReservation), once(BeliefPublication)],
        DeleteBelief => "delete_belief" [once(BeliefDeletion)],
        DeleteProject => "delete_project" [once(ProjectDeletion)],
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
