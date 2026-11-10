use super::operation_catalogue::LearningOperation;
use anyhow::{anyhow, Result};
use mimir_core::MimirService;
use serde_json::{json, Value};

pub(super) fn indexed_support_schema() -> Value {
    json!({"type":"array","description":"For each supporting indexed passage, copy its actual chunk ID, document path and exact quotation, and explain why those words support this belief. These citations record sources without changing probability; do not supply a weight. Similarity only ranks suggestions and does not establish support. If support is missing or unclear, open the user dialog before publication.","items":{
        "type":"object","additionalProperties":false,"properties":{
            "chunk_id":{"type":"string","format":"uuid","description":"Actual chunk ID returned by query_document; never invent an ID."},
            "document_path":{"type":"string","description":"Exact indexed document path returned with that chunk; nonblank."},
            "quotation":{"type":"string","description":"Exact, nonblank, contiguous supporting passage copied from the indexed chunk."},
            "explanation":{"type":"string","description":"The submitting agent's nonblank explanation of why this passage supports the claim. This is an inspectable assertion, not server verification of truth."}
        },"required":["chunk_id","document_path","quotation","explanation"]}})
}

pub fn tools() -> Vec<Value> {
    let uuid = json!({"type":"string","format":"uuid"});
    let feedback = json!({"type":"object","additionalProperties":false,"properties":{
        "belief_id":uuid,"verdict":{"enum":["support","defeat"]},"weight":{"type":"number","minimum":0,"maximum":1}},"required":["belief_id","verdict","weight"]});
    let link = json!({"type":"object","additionalProperties":false,"properties":{
        "from_id":uuid,"to_id":uuid,"relation":{"enum":["Supports","Defeats","Causes","Contradicts"]},"weight":{"type":"number","minimum":0,"maximum":1}},"required":["from_id","to_id","relation","weight"]});
    let target = json!({"oneOf":[
        {"type":"object","additionalProperties":false,"properties":{"belief_id":uuid},"required":["belief_id"]},
        {"type":"object","additionalProperties":false,"properties":{"candidate_key":{"type":"string","minLength":1}},"required":["candidate_key"]}
    ]});
    let candidate = json!({"oneOf":[
        {"type":"object","additionalProperties":false,"properties":{"kind":{"const":"belief"},"key":{"type":"string","minLength":1,"description":"Stable local key: nonempty, with no leading or trailing whitespace. Internal spaces are allowed. Reuse the exact key on retries; declare each key once."},"content":{"type":"string","minLength":1},"memory_type":{"enum":["Fact","Experiential"]},"grounding":indexed_support_schema()},"description":"Every new belief candidate requires nonempty grounding citations before publication. An exact retry of a candidate already committed by an older version preserves its original declaration without adding new fields.","required":["kind","key","content"]},
        {"type":"object","additionalProperties":false,"properties":{"kind":{"const":"pattern"},"key":{"type":"string","minLength":1,"description":"Stable local key: nonempty, with no leading or trailing whitespace. Internal spaces are allowed. Reuse the exact key on retries; declare each key once."},"situation":{"type":"string","minLength":1},"approach":{"type":"string","minLength":1}},"required":["kind","key","situation","approach"]}
    ]});
    let axis = |minimum| json!({"type":"object","additionalProperties":false,"properties":{"value":{"type":["number","null"],"minimum":minimum,"maximum":1},"weight":{"type":"number","minimum":0,"maximum":1}},"required":["value","weight"]});
    let assessment = json!({"type":"object","additionalProperties":false,"properties":{
        "target":target,"scope":{"type":"string","minLength":1},"rubric":{"type":"string","minLength":1},
        "correctness":axis(0),"usefulness":axis(-1),"rationale":{"type":"string","minLength":1},
        "evidence_indices":{"type":"array","description":"Zero-based indices into experience.evidence for this source revision. When source_records is empty or absent, cite the evidence strings using experience.source as their provenance; user_feedback/tool_result may support weight without source_records. Otherwise evidence[i] references source_records[i], whose provenance applies. Positive weight requires relevant cited observed evidence; agent reports alone carry zero observed weight.","items":{"type":"integer","minimum":0}},
        "item_ids":{"type":"array","items":uuid},
        "item_keys":{"type":"array","items":{"type":"string","minLength":1},"description":"Experience-local item keys, resolved to PostgreSQL-assigned item_ids before storing this assessment. Every key must be nonempty and have no whitespace at either end. Internal spaces are allowed. Use each key once and copy saved keys exactly; keys are never silently trimmed or renamed."}},"required":["target","scope","rubric","correctness","usefulness","rationale","evidence_indices"]});
    let prediction = json!({"type":"object","additionalProperties":false,"properties":{
        "quantity":{"type":"string"},"value":{"type":"number"},"unit":{"type":"string"},"probability":{"type":["number","null"],"minimum":0,"maximum":1},
        "lower":{"type":["number","null"]},"upper":{"type":["number","null"]},"horizon":{"type":"string"},"recorded_at":{"type":"string"},"inferred":{"type":"boolean"}},
        "required":["quantity","value","unit","horizon","recorded_at","inferred"]});
    let item = json!({"type":"object","additionalProperties":false,"properties":{
        "id":{"type":"string","format":"uuid","description":"Existing PostgreSQL-assigned UUID, only for readback/correction. Omit for a new item; never invent a UUID."},
        "key":{"type":"string","minLength":1,"description":"Stable experience-local key: nonempty, with no leading or trailing whitespace; internal spaces are allowed. Required for new items, whose persistent UUID is generated by PostgreSQL. Reuse the exact key on retries and corrections, and declare each key once."},
        "kind":{"enum":["estimate","decision","suggestion"]},"source_ref":{"type":"string"},"actor":{"type":"string"},"statement":{"type":"string"},"conditions":{"type":"string"},"predictions":{"type":"array","items":prediction}},
        "anyOf":[{"required":["key"]},{"required":["id"]}],
        "required":["kind","source_ref","actor","statement","conditions"]});
    let source = json!({"type":"object","additionalProperties":false,"properties":{"source_ref":{"type":"string"},"actor":{"type":"string"},"provenance":{"enum":["agent_report","user_feedback","tool_result"]},"text":{"type":"string"},"recorded_at":{"type":["string","null"]}},"required":["source_ref","actor","provenance","text"]});
    let coverage = json!({"type":"object","additionalProperties":false,"properties":{"source_ref":{"type":"string"},"status":{"enum":["complete","unresolved"]},"reason":{"type":"string","minLength":1}},"required":["source_ref","status","reason"]});
    vec![
        json!({"name":"get_learning_review","description":"Read current source coverage and extracted items atomically. A null review means pending; unresolved coverage is not complete extraction.","inputSchema":{"type":"object","properties":{"id":uuid},"required":["id"]}}),
        json!({"name":"learning_capabilities","description":"Read the installed typed learning contract and assessment model version.","inputSchema":{"type":"object","properties":{},"additionalProperties":false}}),
        json!({"name":"get_lesson_assessment","description":"Get separate numeric correctness and usefulness for an explicit lesson, applicability scope and benefit rubric. Uses current review versions only; never grants authority. Values are uncalibrated and distinct from generic graph probability.","inputSchema":{"type":"object","properties":{"project":{"type":"string"},"belief_id":uuid,"scope":{"type":"string"},"rubric":{"type":"string"}},"required":["project","belief_id","scope","rubric"]}}),
        json!({"name":"lesson_assessment_history","description":"Read immutable assessment contributions with active/stale status and exact experience/review revisions. Omit limit for all matches, or supply a positive count. Evidence indices address that experience version.","inputSchema":{"type":"object","properties":{"project":{"type":"string"},"belief_id":uuid,"scope":{"type":"string"},"rubric":{"type":"string"},"offset":{"type":"integer","minimum":0},"limit":{"type":"integer","minimum":1,"description":"Positive result count; omit for all remaining matches. Zero is invalid."}},"required":["project","belief_id","scope","rubric"]}}),
        json!({"name":"explain_belief","description":"Inspect the belief's incoming reasoning edges and active evidence-backed reviews. Omit limit for all matches, or supply a positive count. Follow experience_id with get_experience or experience_history for observations and past revisions. This explains provenance, not causal identification.","inputSchema":{"type":"object","properties":{"id":uuid,"offset":{"type":"integer","minimum":0,"default":0},"limit":{"type":"integer","minimum":1,"description":"Positive result count; omit for all remaining matches. Zero is invalid."}},"required":["id"]}}),
        json!({"name":"record_experience","description":"Record one observed action and outcome for incremental LLM review. Use a stable UUID for the same incident, expected_revision=0 to create, or the returned revision to correct it. Do not also insert a standalone conclusion from this same incident; review-owned candidates avoid that duplicate prior. Exact retries do not duplicate evidence. ToolResult/UserFeedback are caller-reported provenance, not server verification. A correction invalidates the old review and retracts its effects atomically.","inputSchema":{"type":"object","properties":{
            "expected_revision":{"type":"integer","minimum":0},
            "experience":{"type":"object","additionalProperties":false,"properties":{
                "id":uuid,"project":{"type":"string","minLength":1,"description":"Nonblank original project; a correction cannot move the incident."},"context":{"type":"string","minLength":1,"description":"Nonblank observed context."},"action":{"type":"string","minLength":1,"description":"Nonblank observed action."},
                "outcome":{"enum":["success","failure","unknown"]},"source":{"enum":["tool_result","user_feedback","agent_report"]},
                "evidence":{"type":"array","items":{"type":"string"}},
                "belief_ids":{"type":"array","items":uuid},"pattern_id":{"type":["string","null"],"format":"uuid"},"learning_items":{"type":"array","items":item},"source_records":{"type":"array","items":source}},
                "required":["id","project","context","action","outcome","source","evidence"]}},"required":["experience","expected_revision"]}}),
        json!({"name":"pending_experiences","description":"Get the oldest new or changed experiences awaiting LLM review. Incremental work: successful review removes that exact version; failed/stale submissions leave it pending. A judge may temporarily exclude deferred IDs; an empty filtered array does not prove the whole queue is empty. No claim or lease; concurrent reviewers use revision checks.","inputSchema":{"type":"object","properties":{"project":{"type":"string"},"limit":{"type":"integer","minimum":1,"description":"Optional positive result count; omit to return all matching pending experiences."},"exclude_ids":{"type":"array","items":uuid}}}}),
        json!({"name":"review_experience","description":"Apply one atomic, revision-checked review. Every new belief candidate requires a complete embedding and support from an indexed, project-compatible document before any part of the review is committed. If preparation is unavailable, open a user dialog using the normal needs_input response; stored experience evidence alone is not indexed-document grounding. Declare candidates with stable keys; the response maps keys to PostgreSQL-issued UUIDs. Candidate creation is not an observed successful use. Existing UUID-only reviews remain valid. Corrections retract owned evidence and links while retaining candidate identity and independent work.","inputSchema":{"type":"object","properties":{
            "expected_review_revision":{"type":"integer","minimum":0},
            "review":{"type":"object","additionalProperties":false,"properties":{
                "experience_id":uuid,"experience_revision":{"type":"integer","minimum":1},"reviewer":{"type":"string"},"rationale":{"type":"string"},
                "assessments":{"type":"array","items":assessment},"extracted_items":{"type":"array","items":item},"source_coverage":{"type":"array","items":coverage},
                "feedback":{"type":"array","items":feedback},"links":{"type":"array","items":link},
                "superseded_beliefs":{"type":"array","items":uuid},
                "candidates":{"type":"array","items":candidate},
                "candidate_feedback":{"type":"array","items":{"type":"object","additionalProperties":false,"properties":{"target":target,"verdict":{"enum":["support","defeat"]},"weight":{"type":"number","minimum":0,"maximum":1}},"required":["target","verdict","weight"]}},
                "candidate_links":{"type":"array","items":{"type":"object","additionalProperties":false,"properties":{"from":target,"to":target,"relation":{"enum":["Supports","Defeats","Causes","Contradicts"]},"weight":{"type":"number","minimum":0,"maximum":1}},"required":["from","to","relation","weight"]}}},"required":["experience_id","experience_revision","reviewer","rationale"]}},"required":["review","expected_review_revision"]}}),
        json!({"name":"get_experience","description":"Inspect current experience and revision tokens for safe correction or review.","inputSchema":{"type":"object","properties":{"id":uuid},"required":["id"]}}),
        json!({"name":"experience_history","description":"Inspect immutable experience and review versions, including superseded judgments and their rationale.","inputSchema":{"type":"object","properties":{"id":uuid},"required":["id"]}}),
        json!({"name":"query_learning_context","description":"Retrieve relevant beliefs and situation-matched procedures with observed outcome counts and Beta(1,1) estimates. The retrieval field explains whether belief semantic matching was performed, its actual cause when unavailable, matching used, result coverage and next step. Procedure matching is lexical. Agent reports and unknown outcomes are not measured success; counts use current experience versions in this project only. Retrieval is not successful use.","inputSchema":{"type":"object","properties":{"context":{"type":"string"},"project":{"type":"string","description":"The explicit, nonblank project for the intended context. If it is unknown, ask the user rather than guessing."},"limit":{"type":"integer","minimum":1,"description":"Positive result count; omit for all matching records. Zero is invalid."}},"required":["context","project"]}}),
    ]
}
fn required<'a>(args: &'a Value, key: &str) -> Result<&'a Value> {
    args.get(key).ok_or_else(|| anyhow!("missing '{key}'"))
}
fn text<'a>(args: &'a Value, key: &str) -> Result<&'a str> {
    required(args, key)?
        .as_str()
        .ok_or_else(|| anyhow!("'{key}' must be a string"))
}
fn page_selection(
    args: &Value,
) -> std::result::Result<(usize, mimir_core::Selection), mimir_core::interaction::NeedsInput> {
    let offset = args
        .get("offset")
        .map(super::admission::page_offset)
        .transpose()?
        .unwrap_or(0);
    Ok((offset, super::admission::selection(args, "limit")?))
}
pub async fn call(svc: &MimirService, operation: LearningOperation, args: &Value) -> Result<Value> {
    Ok(match operation {
        LearningOperation::LearningCapabilities => {
            json!({"contract_version":3,"source_coverage":true,"assessment_model_version":1,"typed_learning_items":true,"revision_owned_assessments":true,"legacy_graph_probability_unchanged":true})
        }
        LearningOperation::GetLessonAssessment => {
            svc.lesson_assessment(
                text(args, "project")?,
                text(args, "belief_id")?.parse()?,
                text(args, "scope")?,
                text(args, "rubric")?,
            )
            .await?
        }
        LearningOperation::LessonAssessmentHistory => {
            let (offset, limit) = match page_selection(args) {
                Ok(page) => page,
                Err(correction) => return Ok(mimir_json::to_value(correction)?),
            };
            svc.lesson_assessment_history(
                text(args, "project")?,
                text(args, "belief_id")?.parse()?,
                text(args, "scope")?,
                text(args, "rubric")?,
                offset,
                limit,
            )
            .await?
        }
        LearningOperation::ExplainBelief => {
            let (offset, limit) = match page_selection(args) {
                Ok(page) => page,
                Err(correction) => return Ok(mimir_json::to_value(correction)?),
            };
            svc.explain_belief(text(args, "id")?.parse()?, offset, limit)
                .await?
        }
        LearningOperation::RecordExperience | LearningOperation::ReviewExperience =>
            anyhow::bail!("Use this declared writer through execute_registered_write with its original operation token"),
        LearningOperation::GetLearningReview => {
            svc.learning_review(text(args, "id")?.parse()?).await?
        }
        LearningOperation::GetExperience => {
            mimir_json::to_value(svc.get_experience(text(args, "id")?.parse()?).await?)?
        }
        LearningOperation::ExperienceHistory => {
            svc.experience_history(text(args, "id")?.parse()?).await?
        }
        LearningOperation::PendingExperiences => mimir_json::to_value(
            svc.pending_experiences_excluding(
                args.get("project")
                    .map(|_| text(args, "project"))
                    .transpose()?,
                match super::admission::selection(args, "limit") {
                    Ok(selection) => selection,
                    Err(correction) => return Ok(mimir_json::to_value(correction)?),
                },
                &args
                    .get("exclude_ids")
                    .map(mimir_json::decode_ref::<Vec<uuid::Uuid>>)
                    .transpose()?
                    .unwrap_or_default(),
            )
            .await?,
        )?,
        LearningOperation::QueryLearningContext => mimir_json::to_value(
            svc.query_learning_context(
                text(args, "context")?,
                text(args, "project")?,
                match super::admission::selection(args, "limit") {
                    Ok(selection) => selection,
                    Err(correction) => return Ok(mimir_json::to_value(correction)?),
                },
            )
            .await?,
        )?,
    })
}
