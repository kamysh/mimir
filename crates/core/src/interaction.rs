//! Shared pre-execution correction responses for ordinary clients and the judge.
//! Governed by Mimir.McpErrors.AgentCorrection. Do not construct these around an
//! uncertain database outcome: they explicitly certify no business changes.
use crate::validation::{Code, Fault, Segment};
use anyhow::{ensure, Result};
use serde::{Deserialize, Deserializer, Serialize};

const INSTRUCTION: &str = "Correct the indicated fields and retry. If a required value is not known, ask the user instead of guessing.";

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Location {
    Request,
    Arguments,
    Configuration,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CorrectionItem {
    location: Location,
    fault: Fault,
    expected: String,
    suggested_correction: String,
}

impl CorrectionItem {
    pub fn new(
        location: Location,
        fault: Fault,
        expected: String,
        suggested_correction: String,
    ) -> Result<Self> {
        let item = Self {
            location,
            fault,
            expected,
            suggested_correction,
        };
        item.validate()?;
        Ok(item)
    }

    pub fn missing_argument(path: Vec<Segment>, expected: String) -> Result<Self> {
        Self::new(Location::Arguments, Fault {
            path, code: Code::MissingField, message: "A required field is missing.".into(),
        }, expected, "Provide the missing value from the task context. If it is not known, ask the user; do not invent a value.".into())
    }

    pub fn unknown_argument(path: Vec<Segment>, accepted_fields: &[String]) -> Result<Self> {
        let expected = if accepted_fields.is_empty() {
            "This tool accepts no argument fields.".into()
        } else {
            format!(
                "Use only the advertised fields: {}.",
                serde_json::to_string(accepted_fields)?
            )
        };
        Self::new(Location::Arguments, Fault {
            path, code: Code::UnknownField, message: "This field is not accepted by the tool.".into(),
        }, expected, "Remove this field. If another field was intended, use the tool schema and preserve the intended meaning.".into())
    }

    pub fn fault(&self) -> &Fault {
        &self.fault
    }

    pub fn invalid_uuid(path: Vec<Segment>) -> Self {
        Self::new(
            Location::Arguments,
            Fault { path, code: Code::MalformedInput,
                message: "The supplied identifier is not a valid UUID.".into() },
            "A UUID returned by Mimir for the intended record, in a form accepted by the tool's UUID parser.".into(),
            "Copy the stored UUID from the relevant Mimir lookup result. For a new record, omit the ID only if this tool explicitly assigns it. If the intended record is unknown, ask the user. Do not invent an identifier.".into(),
        ).expect("UUID corrections identify the field and explain the repair")
    }
    pub fn location(&self) -> Location {
        self.location
    }
    pub fn expected(&self) -> &str {
        &self.expected
    }
    pub fn suggested_correction(&self) -> &str {
        &self.suggested_correction
    }

    fn validate(&self) -> Result<()> {
        ensure!(
            !self.fault.message.trim().is_empty(),
            "a correction must explain what was wrong"
        );
        ensure!(
            !self.expected.trim().is_empty(),
            "a correction must describe the expected input"
        );
        ensure!(
            !self.suggested_correction.trim().is_empty(),
            "a correction must suggest how to proceed"
        );
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
enum Status {
    NeedsInput,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
enum BusinessChanges {
    None,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
enum NextAction {
    CorrectRequestOrAskUser,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct WireResponse {
    status: Status,
    business_changes: BusinessChanges,
    next_action: NextAction,
    message: String,
    issues: Vec<CorrectionItem>,
}

/// A normal tool result requesting correction before business mutation.
/// An unclassified service error cannot be converted into this type implicitly.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(transparent)]
pub struct NeedsInput(WireResponse);

impl NeedsInput {
    pub fn new(first: CorrectionItem, rest: Vec<CorrectionItem>) -> Result<Self> {
        let mut issues = vec![first];
        issues.extend(rest);
        Self::checked(WireResponse {
            status: Status::NeedsInput,
            business_changes: BusinessChanges::None,
            next_action: NextAction::CorrectRequestOrAskUser,
            message: INSTRUCTION.into(),
            issues,
        })
    }

    pub fn issues(&self) -> &[CorrectionItem] {
        &self.0.issues
    }
    pub fn message(&self) -> &str {
        &self.0.message
    }

    fn checked(wire: WireResponse) -> Result<Self> {
        ensure!(
            !wire.issues.is_empty(),
            "a correction response must identify at least one issue"
        );
        ensure!(
            !wire.message.trim().is_empty(),
            "a correction response must explain the next action"
        );
        for issue in &wire.issues {
            issue.validate()?;
        }
        Ok(Self(wire))
    }
}

impl<'de> Deserialize<'de> for NeedsInput {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> std::result::Result<Self, D::Error> {
        let wire = WireResponse::deserialize(deserializer)?;
        Self::checked(wire).map_err(serde::de::Error::custom)
    }
}

/// A known pre-publication refusal. Only a check before business writes may
/// construct this error; arbitrary database errors cannot be converted into it.
#[derive(Debug)]
pub struct RequestCorrection {
    correction: NeedsInput,
}

pub(crate) const RECORD_REVISION_READBACK: &str = "Call get_experience with the same experience ID to read its current revision, and experience_history if the changes need inspection. Compare the stored content with the intended correction before resubmitting with the current expected_revision. Keep the same incident ID; do not blindly overwrite newer work or invent a revision.";
pub(crate) const REVIEW_REVISION_READBACK: &str = "Call get_experience and get_learning_review with the same experience ID to read the current source, source revision and review revision. Inspect experience_history if needed. Re-evaluate the review against that source before resubmitting review.experience_revision and expected_review_revision. Do not blindly overwrite another review or invent revision values.";

impl RequestCorrection {
    pub(crate) fn learning_context_project() -> Self {
        let issue = CorrectionItem::new(
            Location::Arguments,
            Fault {
                path: vec![Segment::Key("project".into())],
                code: Code::EmptyText,
                message: "The supplied project is blank or contains only whitespace.".into(),
            },
            "The explicit, nonblank project for the intended learning context.".into(),
            "Supply the intended project from the task context and retry. If it is not known, ask the user. Do not invent a project or substitute an unrelated one.".into(),
        )
        .expect("the project correction identifies its field and repair");
        Self {
            correction: NeedsInput::new(issue, vec![]).expect("explained project correction"),
        }
    }

    pub(crate) fn local_key(path: Vec<Segment>, code: Code, message: String) -> Self {
        let issue = CorrectionItem::new(Location::Arguments, Fault { path, code, message },
            "A nonempty stable local key, with no leading or trailing whitespace. Spaces inside a key are allowed. Each key appears once in its declaration or reference list.".into(),
            "For existing work, call get_experience and get_learning_review with the same experience ID and copy the saved key exactly. For new work, supply a nonempty key with no whitespace at either end. Submit each key once in this list. Ask the user if the intended key or item is uncertain. Do not silently trim, rename, invent an identity, or create another incident to bypass this correction.".into())
            .expect("local key correction identifies its field and repair");
        Self {
            correction: NeedsInput::new(issue, vec![]).expect("explained local key correction"),
        }
    }

    pub(crate) fn review_conflict(
        path: Vec<Segment>,
        code: Code,
        message: String,
        repair: &str,
    ) -> Self {
        let issue = CorrectionItem::new(Location::Arguments, Fault { path, code, message },
            "One assessment per target, scope and rubric; one relationship per endpoint pair and kind; one feedback entry per belief. A target cannot receive both typed assessments and legacy contributions in the same review, and a relationship cannot point to itself.".into(),
            format!("{repair} Keep the same experience ID and source revision. If the intended evidence or relationship is uncertain, ask the user. Do not invent an assessment, silently discard conflicting evidence, or create another incident to bypass this correction."))
            .expect("review conflict includes its affected field and repair");
        Self {
            correction: NeedsInput::new(issue, vec![]).expect("explained review conflict"),
        }
    }

    /// Called only around the pure source validator before publication.
    pub(crate) fn review_source(error: anyhow::Error) -> anyhow::Error {
        let refusal = match error.downcast::<crate::validation::Refusal>() {
            Ok(refusal) => refusal,
            Err(error) => return error,
        };
        let recognized = match (refusal.fault.code, refusal.fault.path.as_slice()) {
            (Code::UnsupportedCombination, []) => true,
            (Code::UnsupportedCombination, [Segment::Key(collection)]) => {
                collection == "source_coverage" || collection == "extracted_items"
            }
            (Code::MissingReference | Code::Duplicate, [Segment::Key(collection)]) => {
                collection == "source_coverage"
            }
            (
                Code::MissingReference,
                [Segment::Key(collection), Segment::Index(_), Segment::Key(leaf)],
            ) => {
                (collection == "source_coverage" || collection == "extracted_items")
                    && leaf == "source_ref"
            }
            (
                Code::WrongActor,
                [Segment::Key(collection), Segment::Index(_), Segment::Key(leaf)],
            ) => collection == "extracted_items" && leaf == "actor",
            (
                Code::QuotationMismatch,
                [Segment::Key(collection), Segment::Index(_), Segment::Key(leaf)],
            ) => collection == "extracted_items" && leaf == "statement",
            _ => false,
        };
        if !recognized {
            return refusal.into();
        }
        let mut fault = refusal.fault;
        fault.path.insert(0, Segment::Key("review".into()));
        let issue = CorrectionItem::new(Location::Arguments, fault,
            "Exactly one coverage record per stored source, and extracted items quoting that source's literal text with its recorded actor. Source reviews use typed assessments rather than legacy contributions.".into(),
            "Call get_experience with the same experience ID and read its source_records. Use their exact source_ref and actor; copy a contiguous quotation without decoding or changing literal backslashes, JSON escapes or whitespace. Account for every source once in source_coverage with a reason and honest complete or unresolved status. Use typed assessments for source reviews. Ask the user if evidence or the intended interpretation is unknown. Do not invent quotes, actors, coverage or outcomes.".into())
            .expect("source correction retains complete guidance");
        Self {
            correction: NeedsInput::new(issue, vec![]).expect("explained source correction"),
        }
        .into()
    }

    pub(crate) fn review_retention(message: String) -> Self {
        let issue = CorrectionItem::new(Location::Arguments,
            Fault { path: vec![Segment::Key("review".into()),Segment::Key("extracted_items".into())], code: Code::MissingReference, message },
            "A review correction retains every original extracted item's assigned identity, source, actor, exact quotation and kind. Interpretation may change and new items may be added.".into(),
            "Call get_learning_review and experience_history with the same experience ID. Retain all original extracted items using their saved IDs or stable item keys and original source, actor, statement and kind. Put revised interpretation in conditions, predictions or assessment rationale. Ask the user if the intended correction is uncertain. Do not omit an original item, invent its identity or rewrite the quoted evidence.".into())
            .expect("review retention correction retains complete guidance");
        Self {
            correction: NeedsInput::new(issue, vec![])
                .expect("explained review retention correction"),
        }
    }

    pub(crate) fn source_retention(path: Vec<Segment>, code: Code, message: String) -> Self {
        let issue = CorrectionItem::new(Location::Arguments, Fault { path, code, message },
            "An experience keeps its original project and every original source record unchanged. Corrections append a separate source record.".into(),
            "Call get_experience and experience_history with the same experience ID. Copy the original project and source records, including actor, provenance, text and recorded_at; append a separate correction record when needed. Ask the user if the original evidence or intended project is uncertain. Do not rewrite, omit or invent original evidence, or move the existing experience to another project.".into())
            .expect("source retention correction retains complete guidance");
        Self {
            correction: NeedsInput::new(issue, vec![])
                .expect("explained source retention correction"),
        }
    }

    pub(crate) fn candidate_declaration(path: Vec<Segment>, code: Code, message: String) -> Self {
        let issue = CorrectionItem::new(Location::Arguments, Fault { path, code, message },
            "Each candidate key names one unchanged belief or pattern declaration in this experience. Declare it once; a deleted key cannot be published again.".into(),
            "Call get_learning_review and experience_history with the same experience ID to inspect the original declaration and assigned ID. Reuse that declaration on retry. If different knowledge was intended, ask the user which declaration or new stable key is appropriate. Do not silently rename a candidate, duplicate it, or recreate a deleted candidate.".into())
            .expect("candidate declaration correction retains complete guidance");
        Self {
            correction: NeedsInput::new(issue, vec![]).expect("explained declaration correction"),
        }
    }

    pub(crate) fn candidate_target(path: Vec<Segment>, message: String) -> Self {
        let issue = CorrectionItem::new(Location::Arguments,
            Fault { path, code: Code::MissingReference, message },
            "A key declared by a belief candidate in this review, or an existing belief_id target. A pattern candidate is not a belief target.".into(),
            "Declare the intended belief candidate once with its stable key, or use an existing belief_id returned by list_beliefs. If the intended target is uncertain, ask the user. Do not invent a key or UUID, or treat a pattern as a belief.".into())
            .expect("candidate target correction retains complete guidance");
        Self {
            correction: NeedsInput::new(issue, vec![]).expect("explained candidate target"),
        }
    }
    pub(crate) fn learning_item(path: Vec<Segment>, code: Code, message: String) -> Self {
        let issue = CorrectionItem::new(Location::Arguments, Fault { path, code, message },
            "A new learning item with a stable local key and no supplied ID, or an existing item owned by this experience with its original source and actor. Assessment item keys must resolve within that experience.".into(),
            "Call get_experience and get_learning_review with the same experience ID; use experience_history to inspect prior item keys, assigned IDs and recorded authorship. For a new item, supply its stable local key and omit id so PostgreSQL assigns it. Reuse the returned mapping on retries. If the intended item is unknown, ask the user. Do not invent or silently replace an ID, change source_ref or actor, or create another observation to bypass the conflict.".into())
            .expect("item identity correction retains exact field and readback");
        Self {
            correction: NeedsInput::new(issue, vec![]).expect("explained item identity correction"),
        }
    }

    pub(crate) fn prefix(error: anyhow::Error, prefix: &[Segment]) -> anyhow::Error {
        match error.downcast::<Self>() {
            Err(error) => error,
            Ok(refusal) => {
                let mut issues = refusal.correction.issues().iter().map(|issue| {
                    let mut fault = issue.fault().clone();
                    let mut path = prefix.to_vec();
                    path.extend(fault.path);
                    fault.path = path;
                    CorrectionItem::new(
                        issue.location(),
                        fault,
                        issue.expected().into(),
                        issue.suggested_correction().into(),
                    )
                    .expect("prefixing a checked issue preserves its guidance")
                });
                let first = issues.next().expect("checked correction has an issue");
                Self {
                    correction: NeedsInput::new(first, issues.collect())
                        .expect("checked prefixed correction"),
                }
                .into()
            }
        }
    }
    pub(crate) fn belief_reference(path: Vec<Segment>, code: Code, message: String) -> Self {
        let issue = CorrectionItem::new(Location::Arguments, Fault { path, code, message },
            "A currently stored fact or experiential belief owned by the experience's exact project; global and working beliefs are not learning targets.".into(),
            "Use list_beliefs or query_learning_context for the stated project, inspect the returned project's value and memory type, and select the intended project-owned belief. If the intended reference or project is uncertain, ask the user. Do not invent an ID, move a belief, change the project, or change its memory type to bypass this check.".into())
            .expect("learning reference has complete field and repair guidance");
        Self {
            correction: NeedsInput::new(issue, vec![]).expect("explained learning reference"),
        }
    }

    pub(crate) fn pattern_reference(path: Vec<Segment>, code: Code, message: String) -> Self {
        let issue = CorrectionItem::new(Location::Arguments, Fault { path, code, message },
            "A currently stored pattern belonging to the experience project, or an untagged global pattern.".into(),
            "Use list_patterns for the experience project and inspect the returned pattern. Select the intended permitted pattern, omit the optional pattern reference only if no pattern was used, or ask the user. Do not invent an ID or move a pattern between projects.".into())
            .expect("pattern reference has complete field and repair guidance");
        Self {
            correction: NeedsInput::new(issue, vec![]).expect("explained pattern reference"),
        }
    }
    pub(crate) fn stale_revision(path: Vec<Segment>, message: String, readback: &str) -> Self {
        let issue = CorrectionItem::new(
            Location::Arguments,
            Fault {
                path,
                code: Code::StaleRevision,
                message,
            },
            "The current revision returned by Mimir for the same stored experience and review."
                .into(),
            readback.into(),
        )
        .expect("revision refusals identify the field and exact readback");
        Self {
            correction: NeedsInput::new(issue, vec![]).expect("explained revision refusal"),
        }
    }
    pub(crate) fn missing_reference(field: &str, message: String, lookup: &str) -> Self {
        let issue = CorrectionItem::new(
            Location::Arguments,
            Fault {
                path: vec![Segment::Key(field.into())],
                code: Code::MissingReference,
                message,
            },
            "An identifier of the intended record that is currently stored in Mimir.".into(),
            lookup.into(),
        )
        .expect("reference refusals retain field and lookup guidance");
        Self {
            correction: NeedsInput::new(issue, vec![]).expect("explained reference refusal"),
        }
    }

    pub fn correction(&self) -> &NeedsInput {
        &self.correction
    }
}

impl std::fmt::Display for RequestCorrection {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(&self.correction.issues()[0].fault().message)
    }
}
impl std::error::Error for RequestCorrection {}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn response() -> NeedsInput {
        NeedsInput::new(
            CorrectionItem::missing_argument(
                vec![Segment::Key("project".into())],
                "The actual project name for this work.".into(),
            )
            .unwrap(),
            vec![CorrectionItem::unknown_argument(
                vec![Segment::Key("project_name".into())],
                &["project".into(), "context".into()],
            )
            .unwrap()],
        )
        .unwrap()
    }

    #[test]
    fn missing_and_unknown_fields_share_an_actionable_non_success_response() {
        let response = response();
        let wire = serde_json::to_value(&response).unwrap();
        assert_eq!(wire["status"], "needs_input");
        assert_eq!(wire["business_changes"], "none");
        assert_eq!(wire["next_action"], "correct_request_or_ask_user");
        assert_eq!(wire["issues"][0]["location"], "arguments");
        assert_eq!(wire["issues"][0]["fault"]["path"], json!(["project"]));
        assert_eq!(wire["issues"][0]["fault"]["code"], "missing_field");
        assert_eq!(wire["issues"][1]["fault"]["code"], "unknown_field");
        assert!(response
            .message()
            .contains("ask the user instead of guessing"));
        assert!(wire["issues"][0].get("value").is_none());
        assert!(wire.get("result").is_none());
        assert_eq!(
            serde_json::from_value::<NeedsInput>(wire).unwrap(),
            response
        );
    }

    #[test]
    fn incomplete_or_uncertain_outcomes_cannot_decode_as_no_change_corrections() {
        let original = serde_json::to_value(response()).unwrap();
        for (path, value) in [
            (vec!["issues"], json!([])),
            (vec!["status"], json!("success")),
            (vec!["business_changes"], json!("unknown")),
            (vec!["next_action"], json!("retry_unchanged")),
            (vec!["message"], json!("")),
        ] {
            let mut wire = original.clone();
            wire[path[0]] = value;
            assert!(serde_json::from_value::<NeedsInput>(wire).is_err());
        }
        let mut wire = original.clone();
        wire["issues"][0]["expected"] = json!("");
        assert!(serde_json::from_value::<NeedsInput>(wire).is_err());
        let mut wire = original;
        wire["issues"][0]
            .as_object_mut()
            .unwrap()
            .remove("suggested_correction");
        assert!(serde_json::from_value::<NeedsInput>(wire).is_err());
    }

    #[test]
    fn all_diagnostics_and_full_explanations_survive_transport() {
        let mut first = response().issues()[0].clone();
        first.fault.message = "complete explanation; ".repeat(8193);
        let remaining: Vec<_> = (0..2049)
            .map(|index| {
                CorrectionItem::missing_argument(
                    vec![
                        Segment::Key("items".into()),
                        Segment::Index(index),
                        Segment::Key("source_ref".into()),
                    ],
                    "A reference to the actual supporting source.".into(),
                )
                .unwrap()
            })
            .collect();
        let response = NeedsInput::new(first, remaining).unwrap();
        let decoded: NeedsInput =
            serde_json::from_slice(&serde_json::to_vec(&response).unwrap()).unwrap();
        assert_eq!(decoded, response);
        assert_eq!(decoded.issues().len(), 2050);
        assert_eq!(
            decoded.issues().last().unwrap().fault.path[1],
            Segment::Index(2048)
        );
    }
}
