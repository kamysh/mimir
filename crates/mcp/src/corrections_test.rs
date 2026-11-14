//! Correction dialogue for missing graph references (312) and stale review
//! revisions (94): a refused review explains the repair and commits nothing;
//! the same MCP connection accepts the corrected request afterwards.
#[allow(dead_code)]
#[allow(clippy::duplicate_mod)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;

use super::handle_tool_call;
use anyhow::{ensure, Result};
use mimir_core::{config::Config, graph::MemoryType, MimirService};
use serde_json::{json, Value};
use uuid::Uuid;

fn experience(id: Uuid, project: &str) -> Value {
    json!({"id":id,"project":project,"context":"stale keyboard layout process","action":"observe","outcome":"unknown","source":"agent_report","evidence":["event/1"]})
}

fn review(experience_id: Uuid, expected_review_revision: i64, feedback: Value) -> Value {
    json!({"review":{"experience_id":experience_id,"experience_revision":1,"reviewer":"correction-fixture","rationale":"verify correction dialogue","extracted_items":[],"source_coverage":[],"feedback":feedback},"expected_review_revision":expected_review_revision})
}

#[tokio::test]
async fn missing_references_and_stale_revisions_are_correctable() -> Result<()> {
    let service = MimirService::connect(&Config {
        database: isolation::fixture().database_config(),
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
        retirement: None,
    })
    .await?;
    let project = format!("corrections-{}", Uuid::new_v4());
    let experience_id = Uuid::new_v4();
    handle_tool_call(
        &service,
        "record_experience",
        &json!({"experience":experience(experience_id, &project),"expected_revision":0}),
    )
    .await?;
    let belief = service
        .add_belief_in_project(
            "correction fixture belief",
            0.8,
            0.8,
            &project,
            MemoryType::Fact,
        )
        .await?;

    // 312: a review referencing a belief that does not exist is refused with
    // the repair path, commits nothing, and the same connection stays usable.
    let missing = handle_tool_call(
        &service,
        "review_experience",
        &review(
            experience_id,
            0,
            json!([{"belief_id":Uuid::new_v4(),"verdict":"support","weight":0.5}]),
        ),
    )
    .await;
    let refusal = missing.expect_err("missing belief reference must be refused");
    let message = refusal.to_string();
    ensure!(
        message.contains("was not found"),
        "missing-reference refusal must name the problem: {message}"
    );
    ensure!(
        message.contains("resubmit"),
        "missing-reference refusal must offer a repair path: {message}"
    );
    ensure!(
        handle_tool_call(
            &service,
            "get_learning_review",
            &json!({"id":experience_id})
        )
        .await?["review"]
            .is_null(),
        "a refused review must commit nothing"
    );

    // The corrected review (existing belief) succeeds on the same connection.
    let corrected = handle_tool_call(
        &service,
        "review_experience",
        &review(
            experience_id,
            0,
            json!([{"belief_id":belief.id,"verdict":"support","weight":0.5}]),
        ),
    )
    .await?;
    ensure!(
        corrected["review_revision"] == 1,
        "corrected review must publish: {corrected}"
    );

    // 94: reusing the old expected review revision is stale and explained;
    // reading the current revision and resubmitting succeeds.
    let stale = handle_tool_call(
        &service,
        "review_experience",
        &review(experience_id, 0, json!([])),
    )
    .await;
    let stale_error = stale.expect_err("stale review revision must be refused");
    let stale_message = stale_error.to_string();
    ensure!(
        stale_message.contains("stale"),
        "stale revision refusal must say so: {stale_message}"
    );
    ensure!(
        stale_message.contains("current is 1"),
        "stale revision refusal must name the current revision: {stale_message}"
    );
    let retried = handle_tool_call(
        &service,
        "review_experience",
        &review(experience_id, 1, json!([])),
    )
    .await?;
    ensure!(
        retried["review_revision"] == 2,
        "resubmission with the current revision must succeed: {retried}"
    );

    // 342: malformed local keys are refused before allocation, with the
    // repair named, and nothing is stored.
    let malformed_id = Uuid::new_v4();
    let malformed = json!({"id":malformed_id,"project":project,"context":"key validation","action":"observe","outcome":"unknown","source":"agent_report","evidence":["event/2"],
        "source_records":[{"source_ref":"event/2","actor":"agent","provenance":"agent_report","text":"I suggest checking twice."}],
        "learning_items":[{"key":" padded-key ","kind":"suggestion","source_ref":"event/2","actor":"agent","statement":"I suggest checking twice.","conditions":"untried"}]});
    let refused = handle_tool_call(
        &service,
        "record_experience",
        &json!({"experience":malformed,"expected_revision":0}),
    )
    .await;
    let key_error = refused.expect_err("malformed local key must be refused");
    ensure!(
        key_error
            .to_string()
            .contains("item key must be a nonempty trimmed string"),
        "malformed key refusal must name the repair: {key_error}"
    );
    ensure!(
        handle_tool_call(&service, "get_experience", &json!({"id":malformed_id}))
            .await?
            .is_null(),
        "a refused experience must not be stored"
    );
    Ok(())
}
