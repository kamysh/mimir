//! Structured refusals governed by Mimir.FaultWire and Mimir.McpErrors.
//! Only known validation failures may use this envelope. Database/transport
//! failures remain unclassified: they do not establish that nothing committed.
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum Segment {
    Key(String),
    Index(usize),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Code {
    EmptyText,
    TextTooLong,
    TooMany,
    Duplicate,
    MissingReference,
    WrongActor,
    QuotationMismatch,
    StaleRevision,
    WrongIdentity,
    InvalidNumber,
    InvalidInterval,
    MissingEvidence,
    UnsupportedCombination,
    MalformedInput,
    MissingField,
    UnknownField,
    WrongType,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Fault {
    pub path: Vec<Segment>,
    pub code: Code,
    pub message: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RefusalKind {
    InvalidInput,
    CandidateConflict,
    UndeclaredCandidate,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Refusal {
    pub kind: RefusalKind,
    pub fault: Fault,
}

impl Refusal {
    pub fn candidate_conflict() -> Self {
        Self {
            kind: RefusalKind::CandidateConflict,
            fault: Fault {
                path: vec![Segment::Key("candidates".into())],
                code: Code::WrongIdentity,
                message: "candidate key has a different declaration".into(),
            },
        }
    }

    pub fn undeclared_candidate() -> Self {
        Self {
            kind: RefusalKind::UndeclaredCandidate,
            fault: Fault {
                path: vec![Segment::Key("candidates".into())],
                code: Code::MissingReference,
                message: "candidate belief reference must be declared in this review".into(),
            },
        }
    }
    pub fn invalid(code: Code, path: Vec<Segment>, message: impl Into<String>) -> Self {
        Self {
            kind: RefusalKind::InvalidInput,
            fault: Fault {
                path,
                code,
                message: message.into(),
            },
        }
    }

    /// Call only around a pure validator, before attempting mutation.
    pub fn validation(error: anyhow::Error) -> anyhow::Error {
        if error.downcast_ref::<Self>().is_some()
            || error.is::<crate::interaction::RequestCorrection>()
        {
            return error;
        }
        Self::invalid(Code::MalformedInput, vec![], error.to_string()).into()
    }

    pub fn from_mcp(error: &serde_json::Value) -> Option<Self> {
        if error["code"].as_i64() != Some(-32000) {
            return None;
        }
        mimir_json::from_value(error.get("data")?.clone()).ok()
    }
}

impl std::fmt::Display for Refusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.fault.message)
    }
}
impl std::error::Error for Refusal {}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn serialized_source_quote_failure_is_located_and_survives_mcp_round_trip() {
        let id = uuid::Uuid::new_v4();
        let experience: crate::learning::Experience = mimir_json::from_value(json!({
            "id":id,"project":"citation-fixture","context":"serialized source",
            "action":"review quoted suggestion","outcome":"unknown","source":"agent_report",
            "evidence":["record/1"],"source_records":[{"source_ref":"record/1","actor":"agent",
                "provenance":"agent_report","text":"{\"message\":\"Check first\\nThen proceed\"}"}]
        }))
        .unwrap();
        let mut review: crate::learning::Review = mimir_json::from_value(json!({
            "experience_id":id,"experience_revision":1,"reviewer":"fixture","rationale":"untried suggestion",
            "extracted_items":[{"id":uuid::Uuid::new_v4(),"kind":"suggestion","actor":"agent",
                "source_ref":"record/1","statement":"Check first\nThen proceed","conditions":"untried"}],
            "source_coverage":[{"source_ref":"record/1","status":"unresolved","reason":"No outcome yet"}]
        })).unwrap();
        let error = crate::learning_sources::validate_review(&review, &experience).unwrap_err();
        let failure = error.downcast_ref::<Refusal>().unwrap();
        assert_eq!(failure.fault.code, Code::QuotationMismatch);
        assert_eq!(
            failure.fault.path,
            vec![
                Segment::Key("extracted_items".into()),
                Segment::Index(0),
                Segment::Key("statement".into())
            ]
        );
        let wire = json!({"code":-32000,"message":failure.to_string(),"data":failure});
        assert_eq!(Refusal::from_mcp(&wire).as_ref(), Some(failure));
        assert!(failure.fault.message.contains("record/1"));
        review.extracted_items[0].statement = "Check first\\nThen proceed".into();
        crate::learning_sources::validate_review(&review, &experience).unwrap();
    }

    #[test]
    fn recorded_actor_refusal_locates_nested_speaker_and_survives_mcp_round_trip() {
        let id = uuid::Uuid::new_v4();
        let mut experience: crate::learning::Experience = mimir_json::from_value(json!({
            "id":id,"project":"actor-fixture","context":"nested source authorship",
            "action":"extract source-bound suggestions","outcome":"unknown","source":"agent_report",
            "evidence":["event/0","wrapped/1"],
            "source_records":[
                {"source_ref":"event/0","actor":"agent","provenance":"agent_report","text":"Proceed carefully."},
                {"source_ref":"wrapped/1","actor":"controller","provenance":"tool_result",
                 "text":"{\"actor\":\"agent\",\"message\":\"Check first.\"}"}
            ]
        })).unwrap();
        let allocated = uuid::Uuid::new_v4();
        let mut review: crate::learning::Review = mimir_json::from_value(json!({
            "experience_id":id,"experience_revision":1,"reviewer":"fixture","rationale":"unobserved suggestions",
            "extracted_items":[
                {"id":uuid::Uuid::new_v4(),"key":"careful","kind":"suggestion","actor":"agent",
                 "source_ref":"event/0","statement":"Proceed carefully.","conditions":"untried"},
                {"id":allocated,"key":"check-first","kind":"suggestion","actor":"agent",
                 "source_ref":"wrapped/1","statement":"Check first.","conditions":"nested suggestion"}
            ],
            "source_coverage":[
                {"source_ref":"event/0","status":"unresolved","reason":"No outcome yet"},
                {"source_ref":"wrapped/1","status":"unresolved","reason":"No outcome yet"}
            ]
        })).unwrap();
        let error = crate::learning_sources::validate_review(&review, &experience).unwrap_err();
        let failure = error.downcast_ref::<Refusal>().unwrap();
        assert_eq!(failure.fault.code, Code::WrongActor);
        assert_eq!(
            failure.fault.path,
            vec![
                Segment::Key("extracted_items".into()),
                Segment::Index(1),
                Segment::Key("actor".into())
            ]
        );
        for expected in [
            "check-first",
            "wrapped/1",
            "expected \"controller\"",
            "received \"agent\"",
        ] {
            assert!(failure.fault.message.contains(expected));
        }
        assert!(
            !failure.fault.message.contains(&allocated.to_string()),
            "tentative UUID must not replace the stable key in correction feedback"
        );
        let wire = json!({"code":-32000,"message":failure.to_string(),"data":failure});
        assert_eq!(Refusal::from_mcp(&wire).as_ref(), Some(failure));
        review.extracted_items[1].actor = "controller".into();
        crate::learning_sources::validate_review(&review, &experience).unwrap();
        // A matching actor must not suppress the independent identity guard.
        experience
            .learning_items
            .push(review.extracted_items[1].clone());
        let conflict = crate::learning_sources::validate_review(&review, &experience).unwrap_err();
        let failure = conflict.downcast_ref::<Refusal>().unwrap();
        assert_eq!(failure.fault.code, Code::Duplicate);
        assert_eq!(
            failure.fault.path,
            vec![
                Segment::Key("extracted_items".into()),
                Segment::Index(1),
                Segment::Key("id".into())
            ]
        );
    }

    #[test]
    fn unclassified_errors_never_claim_validation_or_rollback() {
        assert!(
            Refusal::from_mcp(&json!({"code":-32000,"message":"database password=secret"}))
                .is_none()
        );
        let r = Refusal::candidate_conflict();
        assert!(Refusal::from_mcp(&json!({"code":-32001,"data":r})).is_none());
        assert!(Refusal::from_mcp(&json!({"code":-32000,"data":{"kind":"invalid_input","fault":{"path":[],"code":"future_code","message":"unknown"}}})).is_none());
    }
}
