//! Closed operation names and commit boundaries shared by core storage and MCP.
//! Descriptors, argument admission and handler dispatch remain in their owners.

/// Stable names for actual business publication sites, not every SQL query in
/// a transaction. Instrumentation and native/spec comparison follow in #88.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CommitSite {
    OperationReservation,
    OperationCancellation,
    EmbeddingOwnerReservation,
    BeliefPublication,
    BeliefVectorPublication,
    EvidencePublication,
    EvidenceRemoval,
    BeliefDeletion,
    ProjectDeletion,
    PatternPublication,
    PatternDeletion,
    EdgePublication,
    ContradictionPublication,
    Propagation,
    Decay,
    DocumentPreparation,
    DocumentReplacement,
    DocumentDeletion,
    ExperiencePublication,
    ReviewPublication,
}

impl CommitSite {
    pub fn name(self) -> &'static str {
        match self {
            Self::OperationReservation => "store.reserve_operation",
            Self::OperationCancellation => "store.cancel_operation",
            Self::EmbeddingOwnerReservation => "store.reserve_belief_preparation",
            Self::BeliefPublication => "store.publish_prepared_belief",
            Self::BeliefVectorPublication => "store.insert_belief_embedding",
            Self::EvidencePublication => "store.insert_evidence",
            Self::EvidenceRemoval => "store.delete_evidence",
            Self::BeliefDeletion => "store.delete_belief",
            Self::ProjectDeletion => "store.delete_project",
            Self::PatternPublication => "store.insert_pattern",
            Self::PatternDeletion => "store.delete_pattern",
            Self::EdgePublication => "store.insert_edge",
            Self::ContradictionPublication => "store.insert_contradicts",
            Self::Propagation => "store.propagate_locked",
            Self::Decay => "store.decay_locked",
            Self::DocumentPreparation => "store.prepare_document",
            Self::DocumentReplacement => "store.replace_document",
            Self::DocumentDeletion => "store.clear_document",
            Self::ExperiencePublication => "store.record_experience",
            Self::ReviewPublication => "store.review_experience_prepared",
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
     learning { $($learning:ident => $learning_name:literal [$($learning_boundary:expr),* $(,)?]),* $(,)? }
     control { $($control:ident => $control_name:literal [$($control_boundary:expr),* $(,)?]),* $(,)? }) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub enum GraphOperation { $($graph),* }
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub enum LearningOperation { $($learning),* }
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub enum ControlOperation { $($control),* }
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub enum Operation { Graph(GraphOperation), Learning(LearningOperation), Control(ControlOperation) }
        impl Operation {
            pub const ALL: &'static [Self] = &[$(Self::Graph(GraphOperation::$graph)),*, $(Self::Learning(LearningOperation::$learning)),*, $(Self::Control(ControlOperation::$control)),*];
            pub fn name(self) -> &'static str {
                match self { $(Self::Graph(GraphOperation::$graph) => $graph_name),*, $(Self::Learning(LearningOperation::$learning) => $learning_name),*, $(Self::Control(ControlOperation::$control) => $control_name),* }
            }
            pub fn committed_boundaries(self) -> &'static [CommitBoundary] {
                match self {
                    $(Self::Graph(GraphOperation::$graph) => { const PLAN: &[CommitBoundary] = &[$($graph_boundary),*]; PLAN }),*,
                    $(Self::Learning(LearningOperation::$learning) => { const PLAN: &[CommitBoundary] = &[$($learning_boundary),*]; PLAN }),*,
                    $(Self::Control(ControlOperation::$control) => { const PLAN: &[CommitBoundary] = &[$($control_boundary),*]; PLAN }),*
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
        SweepExpiredDefeated => "sweep_expired_defeated" [once(BeliefDeletion)],
        QueryRelevant => "query_relevant" [],
        AddEvidence => "add_evidence" [once(EvidencePublication)],
        GetEvidence => "get_evidence" [],
        PropagateFrom => "propagate_from" [once(Propagation)],
        QueryIntervention => "query_intervention" [],
        LoadDocument => "load_document" [once(DocumentPreparation), once(DocumentReplacement)],
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
        ReviewExperience => "review_experience" [repeated(EmbeddingOwnerReservation), once(ReviewPublication)],
        GetExperience => "get_experience" [],
        ExperienceHistory => "experience_history" [],
        QueryLearningContext => "query_learning_context" []
    }
    control {
        ReserveOperation => "reserve_operation" [once(OperationReservation)],
        OperationOutcome => "operation_outcome" [],
        CancelOperation => "cancel_operation" [once(OperationCancellation)]
    }
}

/// The shared write dispatcher accepts only a declared business writer.
/// Controls have their own reservation/readback/cancellation protocol.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RegisteredWrite {
    operation: Operation,
}
impl RegisteredWrite {
    pub fn operation(self) -> Operation {
        self.operation
    }
}
impl Operation {
    pub fn registered_write(self) -> Option<RegisteredWrite> {
        match self {
            Self::Control(_) => None,
            Self::Graph(_) | Self::Learning(_) => (!self.committed_boundaries().is_empty())
                .then_some(RegisteredWrite { operation: self }),
        }
    }
}

/// Library operations have checked plans without becoming advertised MCP tools.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RegisteredOperation {
    Tool(Operation),
    DeleteEvidence,
    Reembed,
}

impl RegisteredOperation {
    pub fn named(name: &str) -> Option<Self> {
        Operation::ALL
            .iter()
            .copied()
            // Controls own their concrete reservation/readback/cancellation
            // certificates; they are not business plans executed under a
            // second operation token.
            .find(|operation| {
                !matches!(operation, Operation::Control(_)) && operation.name() == name
            })
            .map(Self::Tool)
            .or_else(|| (name == "delete_evidence").then_some(Self::DeleteEvidence))
            .or_else(|| (name == "reembed").then_some(Self::Reembed))
    }

    pub fn name(self) -> &'static str {
        match self {
            Self::Tool(operation) => operation.name(),
            Self::DeleteEvidence => "delete_evidence",
            Self::Reembed => "reembed",
        }
    }

    pub fn committed_boundaries(self) -> &'static [CommitBoundary] {
        match self {
            Self::Tool(operation) => operation.committed_boundaries(),
            Self::DeleteEvidence => {
                const PLAN: &[CommitBoundary] = &[once(EvidenceRemoval)];
                PLAN
            }
            Self::Reembed => {
                const PLAN: &[CommitBoundary] = &[repeated(BeliefVectorPublication)];
                PLAN
            }
        }
    }
}
