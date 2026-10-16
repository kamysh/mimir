use anyhow::{anyhow, Result};
use mimir_core::MimirService;
use serde_json::{json, Value};

pub fn tools() -> Vec<Value> {
    let uuid = json!({"type":"string","format":"uuid"});
    let feedback = json!({"type":"object","additionalProperties":false,"properties":{
        "belief_id":uuid,"verdict":{"enum":["support","defeat"]},"weight":{"type":"number","minimum":0,"maximum":1}},"required":["belief_id","verdict","weight"]});
    let link = json!({"type":"object","additionalProperties":false,"properties":{
        "from_id":uuid,"to_id":uuid,"relation":{"enum":["Supports","Defeats","Causes","Contradicts"]},"weight":{"type":"number","minimum":0,"maximum":1}},"required":["from_id","to_id","relation","weight"]});
    let target = json!({"oneOf":[
        {"type":"object","additionalProperties":false,"properties":{"belief_id":uuid},"required":["belief_id"]},
        {"type":"object","additionalProperties":false,"properties":{"candidate_key":{"type":"string","minLength":1,"maxLength":128}},"required":["candidate_key"]}
    ]});
    let candidate = json!({"oneOf":[
        {"type":"object","additionalProperties":false,"properties":{"kind":{"const":"belief"},"key":{"type":"string","minLength":1,"maxLength":128},"content":{"type":"string","minLength":1},"memory_type":{"enum":["Fact","Experiential"]}},"required":["kind","key","content"]},
        {"type":"object","additionalProperties":false,"properties":{"kind":{"const":"pattern"},"key":{"type":"string","minLength":1,"maxLength":128},"situation":{"type":"string","minLength":1},"approach":{"type":"string","minLength":1}},"required":["kind","key","situation","approach"]}
    ]});
    vec![
        json!({"name":"explain_belief","description":"Inspect the belief's incoming reasoning edges and a bounded page of active evidence-backed reviews. Follow experience_id with get_experience or experience_history for observations and past revisions. This explains provenance, not causal identification.","inputSchema":{"type":"object","properties":{"id":uuid,"offset":{"type":"integer","minimum":0,"default":0},"limit":{"type":"integer","minimum":1,"maximum":20,"default":10}},"required":["id"]}}),
        json!({"name":"record_experience","description":"Record one observed action and outcome for incremental LLM review. Use a stable UUID for the same incident, expected_revision=0 to create, or the returned revision to correct it. Do not also insert a standalone conclusion from this same incident; review-owned candidates avoid that duplicate prior. Exact retries do not duplicate evidence. ToolResult/UserFeedback are caller-reported provenance, not server verification. A correction invalidates the old review and retracts its effects atomically.","inputSchema":{"type":"object","properties":{
            "expected_revision":{"type":"integer","minimum":0},
            "experience":{"type":"object","additionalProperties":false,"properties":{
                "id":uuid,"project":{"type":"string"},"context":{"type":"string"},"action":{"type":"string"},
                "outcome":{"enum":["success","failure","unknown"]},"source":{"enum":["tool_result","user_feedback","agent_report"]},
                "evidence":{"type":"array","items":{"type":"string"},"maxItems":32},
                "belief_ids":{"type":"array","items":uuid,"maxItems":64},"pattern_id":{"type":["string","null"]}},
                "required":["id","project","context","action","outcome","source","evidence"]}},"required":["experience","expected_revision"]}}),
        json!({"name":"pending_experiences","description":"Get the oldest new or changed experiences awaiting LLM review. Bounded incremental work: successful review removes that exact version; failed/stale submissions leave it pending. A judge may temporarily exclude deferred IDs; an empty filtered array does not prove the whole queue is empty. No claim or lease; concurrent reviewers use revision checks.","inputSchema":{"type":"object","properties":{"project":{"type":"string"},"limit":{"type":"integer","minimum":1,"maximum":100,"default":10},"exclude_ids":{"type":"array","items":uuid,"maxItems":1000}}}}),
        json!({"name":"review_experience","description":"Apply one atomic, revision-checked review. Declare new belief/pattern candidates with stable keys; the response maps keys to server UUIDs. Candidate creation is not an observed successful use. Existing UUID-only reviews remain valid. Corrections retract owned evidence and links while retaining candidate identity and independent work.","inputSchema":{"type":"object","properties":{
            "expected_review_revision":{"type":"integer","minimum":0},
            "review":{"type":"object","additionalProperties":false,"properties":{
                "experience_id":uuid,"experience_revision":{"type":"integer","minimum":1},"reviewer":{"type":"string"},"rationale":{"type":"string"},
                "feedback":{"type":"array","items":feedback,"maxItems":64},"links":{"type":"array","items":link,"maxItems":64},
                "superseded_beliefs":{"type":"array","items":uuid,"maxItems":64},
                "candidates":{"type":"array","items":candidate,"maxItems":64},
                "candidate_feedback":{"type":"array","items":{"type":"object","additionalProperties":false,"properties":{"target":target,"verdict":{"enum":["support","defeat"]},"weight":{"type":"number","minimum":0,"maximum":1}},"required":["target","verdict","weight"]},"maxItems":64},
                "candidate_links":{"type":"array","items":{"type":"object","additionalProperties":false,"properties":{"from":target,"to":target,"relation":{"enum":["Supports","Defeats","Causes","Contradicts"]},"weight":{"type":"number","minimum":0,"maximum":1}},"required":["from","to","relation","weight"]},"maxItems":64}},"required":["experience_id","experience_revision","reviewer","rationale"]}},"required":["review","expected_review_revision"]}}),
        json!({"name":"get_experience","description":"Inspect current experience and revision tokens for safe correction or review.","inputSchema":{"type":"object","properties":{"id":uuid},"required":["id"]}}),
        json!({"name":"experience_history","description":"Inspect immutable experience and review versions, including superseded judgments and their rationale.","inputSchema":{"type":"object","properties":{"id":uuid},"required":["id"]}}),
        json!({"name":"query_learning_context","description":"Retrieve relevant beliefs and situation-matched procedures with outcome counts and Beta(1,1) success estimates. Agent reports and unknown outcomes do not count as measured success. Counts include current experience versions in this project only; retrieval is not successful use. Pattern matching is lexical; beliefs use existing hybrid retrieval.","inputSchema":{"type":"object","properties":{"context":{"type":"string"},"project":{"type":"string"},"limit":{"type":"integer","minimum":1,"maximum":20,"default":5}},"required":["context","project"]}}),
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
fn integer(args: &Value, key: &str) -> Result<i64> {
    required(args, key)?
        .as_i64()
        .ok_or_else(|| anyhow!("'{key}' must be an integer"))
}
fn limit(args: &Value, default: usize) -> Result<usize> {
    args.get("limit")
        .map(|x| {
            x.as_u64()
                .and_then(|n| usize::try_from(n).ok())
                .ok_or_else(|| anyhow!("limit must be a nonnegative integer"))
        })
        .unwrap_or(Ok(default))
}
pub async fn call(svc: &MimirService, name: &str, args: &Value) -> Result<Value> {
    Ok(match name {
        "explain_belief" => {
            svc.explain_belief(
                text(args, "id")?.parse()?,
                args.get("offset")
                    .map(|v| {
                        v.as_u64()
                            .and_then(|n| usize::try_from(n).ok())
                            .ok_or_else(|| anyhow!("offset must be nonnegative"))
                    })
                    .transpose()?
                    .unwrap_or(0),
                limit(args, 10)?,
            )
            .await?
        }
        "record_experience" => serde_json::to_value(
            svc.record_experience(
                &serde_json::from_value(required(args, "experience")?.clone())?,
                integer(args, "expected_revision")?,
            )
            .await?,
        )?,
        "review_experience" => serde_json::to_value(
            svc.review_experience(
                &serde_json::from_value(required(args, "review")?.clone())?,
                integer(args, "expected_review_revision")?,
            )
            .await?,
        )?,
        "get_experience" => {
            serde_json::to_value(svc.get_experience(text(args, "id")?.parse()?).await?)?
        }
        "experience_history" => svc.experience_history(text(args, "id")?.parse()?).await?,
        "pending_experiences" => serde_json::to_value(
            svc.pending_experiences_excluding(
                args.get("project")
                    .map(|_| text(args, "project"))
                    .transpose()?,
                limit(args, 10)?,
                &args
                    .get("exclude_ids")
                    .map(|ids| serde_json::from_value::<Vec<uuid::Uuid>>(ids.clone()))
                    .transpose()?
                    .unwrap_or_default(),
            )
            .await?,
        )?,
        "query_learning_context" => serde_json::to_value(
            svc.query_learning_context(
                text(args, "context")?,
                text(args, "project")?,
                limit(args, 5)?,
            )
            .await?,
        )?,
        _ => anyhow::bail!("unknown learning tool"),
    })
}
