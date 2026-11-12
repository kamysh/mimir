//! Closed public operation registry. Every registered tool must have a handler
//! in the exhaustive dispatcher; tests check that schemas advertise this set.
macro_rules! operations {
    ($($variant:ident => $wire:literal),+ $(,)?) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub enum Operation { $($variant),+ }
        impl Operation {
            #[cfg(test)]
            pub const ALL: &'static [Self] = &[$(Self::$variant),+];
            pub fn parse(name: &str) -> Option<Self> {
                match name { $($wire => Some(Self::$variant),)+ _ => None }
            }
            pub fn wire(self) -> &'static str { match self { $(Self::$variant => $wire),+ } }
        }
    }
}
operations! {
    InsertBelief => "insert_belief", DeleteBelief => "delete_belief",
    DeleteProject => "delete_project", DeletePattern => "delete_pattern",
    InsertPattern => "insert_pattern", RecordSupport => "record_support",
    RecordCause => "record_cause", RecordDefeat => "record_defeat",
    RecordContradiction => "record_contradiction", GetBelief => "get_belief",
    ListBeliefs => "list_beliefs", ListPatterns => "list_patterns",
    GetContradictions => "get_contradictions", DecayAll => "decay_all",
    SweepExpiredDefeated => "sweep_expired_defeated", QueryRelevant => "query_relevant",
    AddEvidence => "add_evidence", GetEvidence => "get_evidence",
    PropagateFrom => "propagate_from", QueryIntervention => "query_intervention",
    LoadDocument => "load_document", QueryDocument => "query_document",
    ClearDocument => "clear_document", ExplainBelief => "explain_belief",
    RecordExperience => "record_experience", ReviewExperience => "review_experience",
    GetLearningReview => "get_learning_review", GetExperience => "get_experience",
    ExperienceHistory => "experience_history", PendingExperiences => "pending_experiences",
    QueryLearningContext => "query_learning_context", LearningCapabilities => "learning_capabilities",
    GetLessonAssessment => "get_lesson_assessment", LessonAssessmentHistory => "lesson_assessment_history",
}
