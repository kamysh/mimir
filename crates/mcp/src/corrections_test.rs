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

fn experience(project: &str) -> Value {
    json!({"project":project,"context":"stale keyboard layout process","action":"observe","outcome":"unknown","source":"agent_report","evidence":["event/1"]})
}

fn review(experience_id: Uuid, expected_review_revision: i64, feedback: Value) -> Value {
    json!({"review":{"experience_id":experience_id,"experience_revision":1,"reviewer":"correction-fixture","rationale":"verify correction dialogue","extracted_items":[],"source_coverage":[],"feedback":feedback},"expected_review_revision":expected_review_revision})
}

#[ignore = "requires MIMIR_TEST_ROOT isolated fixture"]
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
    let saved = handle_tool_call(
        &service,
        "record_experience",
        &json!({"experience":experience(&project),"expected_revision":0}),
    )
    .await?;
    let experience_id: Uuid = serde_json::from_value(saved["experience"]["id"].clone())?;
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
    let malformed = json!({"project":project,"context":"key validation","action":"observe","outcome":"unknown","source":"agent_report","evidence":["event/2"],
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
        service
            .select_pending_experiences(Some(&project), None, &[])
            .await?
            .is_empty(),
        "a refused experience must not be stored"
    );
    Ok(())
}

fn sourced_experience(project: &str) -> Value {
    json!({"project":project,"context":"sourced observation","action":"observe","outcome":"unknown","source":"agent_report","evidence":["event/9"],
        "source_records":[{"source_ref":"event/9","actor":"agent","provenance":"agent_report","text":"The lock waits for a slow statement."}]})
}

fn sourced_review(experience_id: Uuid, items: Value) -> Value {
    json!({"review":{"experience_id":experience_id,"experience_revision":1,"reviewer":"correction-fixture","rationale":"verify source admission",
        "extracted_items":items,
        "source_coverage":[{"source_ref":"event/9","status":"unresolved","reason":"later outcome"}],
        "feedback":[],"candidate_feedback":[],"links":[],"candidate_links":[]},"expected_review_revision":0})
}

/// 319: source/actor/quotation mistakes are explained at the exact field
/// before any embedding or publication, with copy-the-source guidance.
#[ignore = "requires MIMIR_TEST_ROOT isolated fixture"]
#[tokio::test]
async fn source_actor_and_quotation_mistakes_are_explained() -> Result<()> {
    let service = MimirService::connect(&Config {
        database: isolation::fixture().database_config(),
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
        retirement: None,
    })
    .await?;
    let project = format!("sources-{}", Uuid::new_v4());
    let saved = handle_tool_call(
        &service,
        "record_experience",
        &json!({"experience":sourced_experience(&project),"expected_revision":0}),
    )
    .await?;
    let experience_id: Uuid = serde_json::from_value(saved["experience"]["id"].clone())?;

    let wrong_actor = sourced_review(
        experience_id,
        json!([{"key":"actor-item","kind":"suggestion","source_ref":"event/9","actor":"someone_else","statement":"The lock waits for a slow statement.","conditions":"untried"}]),
    );
    let error = handle_tool_call(&service, "review_experience", &wrong_actor)
        .await
        .expect_err("actor mismatch must be refused");
    ensure!(
        error.to_string().contains("extracted_items[0].actor"),
        "actor refusal must locate the field: {error}"
    );

    let wrong_quote = sourced_review(
        experience_id,
        json!([{"key":"quote-item","kind":"suggestion","source_ref":"event/9","actor":"agent","statement":"a paraphrase, not a quote","conditions":"untried"}]),
    );
    let error = handle_tool_call(&service, "review_experience", &wrong_quote)
        .await
        .expect_err("quotation mismatch must be refused");
    ensure!(
        error.to_string().contains("extracted_items[0].statement"),
        "quotation refusal must locate the field: {error}"
    );

    ensure!(
        handle_tool_call(
            &service,
            "get_learning_review",
            &json!({"id":experience_id})
        )
        .await?["review"]
            .is_null(),
        "refused reviews must commit nothing"
    );
    Ok(())
}

/// 336/314: candidate feedback naming a candidate this review never declared
/// is refused as a conflict, with the stable key identified.
#[ignore = "requires MIMIR_TEST_ROOT isolated fixture"]
#[tokio::test]
async fn undeclared_candidate_references_are_refused() -> Result<()> {
    let service = MimirService::connect(&Config {
        database: isolation::fixture().database_config(),
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
        retirement: None,
    })
    .await?;
    let project = format!("candidates-{}", Uuid::new_v4());
    let saved = handle_tool_call(
        &service,
        "record_experience",
        &json!({"experience":sourced_experience(&project),"expected_revision":0}),
    )
    .await?;
    let experience_id: Uuid = serde_json::from_value(saved["experience"]["id"].clone())?;

    let undeclared = json!({"review":{"experience_id":experience_id,"experience_revision":1,"reviewer":"correction-fixture","rationale":"undeclared candidate",
        "extracted_items":[],"source_coverage":[{"source_ref":"event/9","status":"unresolved","reason":"untried"}],
        "candidate_feedback":[{"target":{"candidate_key":"ghost"},"verdict":"support","weight":0.5}]},"expected_review_revision":0});
    let error = handle_tool_call(&service, "review_experience", &undeclared)
        .await
        .expect_err("undeclared candidate reference must be refused");
    ensure!(
        error
            .to_string()
            .contains("must be declared in this review"),
        "undeclared candidate refusal must identify the conflict: {error}"
    );
    ensure!(
        handle_tool_call(
            &service,
            "get_learning_review",
            &json!({"id":experience_id})
        )
        .await?["review"]
            .is_null(),
        "refused reviews must commit nothing"
    );
    Ok(())
}

/// 315: completed review answers stay readable after the candidate belief
/// they created is deleted — ordinary stored history, not replay machinery.
#[ignore = "requires MIMIR_TEST_ROOT isolated fixture"]
#[tokio::test]
async fn review_history_stays_readable_after_candidate_deletion() -> Result<()> {
    struct Provider;
    impl mimir_core::embed::EmbeddingProvider for Provider {
        fn embed<'a>(&'a self, texts: &'a [String]) -> mimir_core::embed::EmbedFuture<'a> {
            Box::pin(async move { Ok(vec![vec![1.0, 0.0]; texts.len()]) })
        }
    }
    let service = MimirService::connect(&Config {
        database: isolation::fixture().database_config(),
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
        retirement: None,
    })
    .await?
    .with_embedding_provider(Box::new(Provider));

    let project = format!("history-{}", Uuid::new_v4());
    let document = std::env::temp_dir().join(format!("mimir-315-{}.md", Uuid::new_v4()));
    std::fs::write(&document, "# Fixture\n\nthe supporting passage text\n")?;
    service
        .load_document(&document.to_string_lossy(), Some(&project))
        .await?;
    let passage = service
        .query_document("supporting passage", Some(&project), 1)
        .await?;
    ensure!(!passage.is_empty(), "fixture passage must be indexed");
    let passage_id = Uuid::parse_str(&passage[0].id)?;

    let saved = handle_tool_call(
        &service,
        "record_experience",
        &json!({"experience":sourced_experience(&project),"expected_revision":0}),
    )
    .await?;
    let experience_id: Uuid = serde_json::from_value(saved["experience"]["id"].clone())?;
    let reviewed = handle_tool_call(
        &service,
        "review_experience",
        &json!({"review":{"experience_id":experience_id,"experience_revision":1,"reviewer":"history-fixture","rationale":"publish one candidate",
            "extracted_items":[],"source_coverage":[{"source_ref":"event/9","status":"unresolved","reason":"untried"}],
            "candidates":[{"kind":"belief","key":"history-candidate","content":"A stored lesson","memory_type":"Fact","supporting_passage_id":passage_id}]},"expected_review_revision":0}),
    )
    .await?;
    let candidate_id = Uuid::parse_str(
        reviewed["candidate_ids"]["history-candidate"]
            .as_str()
            .unwrap_or_default(),
    )?;

    ensure!(
        service.delete_belief(candidate_id).await?,
        "fixture candidate must be deletable"
    );
    ensure!(
        !handle_tool_call(
            &service,
            "get_learning_review",
            &json!({"id":experience_id})
        )
        .await?["review"]
            .is_null(),
        "the completed review must stay readable after candidate deletion"
    );
    let history =
        handle_tool_call(&service, "experience_history", &json!({"id":experience_id})).await?;
    ensure!(
        history["reviews"]
            .as_array()
            .is_some_and(|rs| !rs.is_empty()),
        "review history must stay readable after candidate deletion: {history}"
    );
    Ok(())
}

/// 317/318: corrections cannot move an experience to another project, drop
/// original source records, or re-extract an already-recorded original item;
/// each refusal names the valid repair.
#[ignore = "requires MIMIR_TEST_ROOT isolated fixture"]
#[tokio::test]
async fn protected_originals_are_explained_on_correction() -> Result<()> {
    let service = MimirService::connect(&Config {
        database: isolation::fixture().database_config(),
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
        retirement: None,
    })
    .await?;
    let project = format!("protected-{}", Uuid::new_v4());
    let original = json!({"project":project,"context":"protected observation","action":"observe","outcome":"unknown","source":"agent_report","evidence":["event/7"],
        "source_records":[{"source_ref":"event/7","actor":"agent","provenance":"agent_report","text":"The original statement."}],
        "learning_items":[{"key":"original-item","kind":"suggestion","source_ref":"event/7","actor":"agent","statement":"The original statement.","conditions":"untried"}]});
    let saved = handle_tool_call(
        &service,
        "record_experience",
        &json!({"experience":original,"expected_revision":0}),
    )
    .await?;
    let experience_id: Uuid = serde_json::from_value(saved["experience"]["id"].clone())?;
    let recorded =
        handle_tool_call(&service, "get_experience", &json!({"id":experience_id})).await?;
    let recorded_item_id = Uuid::parse_str(
        recorded["experience"]["learning_items"][0]["id"]
            .as_str()
            .unwrap_or_default(),
    )?;

    // 317: moving the experience to another project is refused.
    let moved = serde_json::from_value::<serde_json::Value>(serde_json::to_value(
        json!({"id":experience_id,"project":"some-other-project","context":"protected observation","action":"observe","outcome":"unknown","source":"agent_report","evidence":["event/7"],
            "source_records":[{"source_ref":"event/7","actor":"agent","provenance":"agent_report","text":"The original statement."}],
            "learning_items":[{"id":recorded_item_id,"key":"original-item","kind":"suggestion","source_ref":"event/7","actor":"agent","statement":"The original statement.","conditions":"untried"}]}),
    )?)?;
    let error = handle_tool_call(
        &service,
        "record_experience",
        &json!({"experience":moved,"expected_revision":1}),
    )
    .await
    .expect_err("moving an experience to another project must be refused");
    ensure!(
        error
            .to_string()
            .contains("experience project is immutable"),
        "project change refusal must be explicit: {error}"
    );

    // 317: dropping the original source record is refused.
    let dropped = json!({"id":experience_id,"project":project,"context":"protected observation","action":"observe","outcome":"unknown","source":"agent_report","evidence":["event/8"],
        "source_records":[{"source_ref":"event/8","actor":"agent","provenance":"user_feedback","text":"A later correction."}],
        "learning_items":[{"id":recorded_item_id,"key":"original-item","kind":"suggestion","source_ref":"event/7","actor":"agent","statement":"The original statement.","conditions":"untried"}]});
    let error = handle_tool_call(
        &service,
        "record_experience",
        &json!({"experience":dropped,"expected_revision":1}),
    )
    .await
    .expect_err("dropping original source records must be refused");
    ensure!(
        error
            .to_string()
            .contains("source corrections must retain original records"),
        "source-drop refusal must name the repair: {error}"
    );

    // 318: re-extracting an already-recorded original item id in a review is
    // refused with guidance to reference it in the assessment instead.
    let review = json!({"review":{"experience_id":experience_id,"experience_revision":1,"reviewer":"protected-fixture","rationale":"rewrite original",
        "extracted_items":[{"id":recorded_item_id,"key":"original-item","kind":"suggestion","source_ref":"event/7","actor":"agent","statement":"The original statement.","conditions":"untried"}],
        "source_coverage":[{"source_ref":"event/7","status":"unresolved","reason":"untried"}]},"expected_review_revision":0});
    let error = handle_tool_call(&service, "review_experience", &review)
        .await
        .expect_err("reusing a recorded item id must be refused");
    ensure!(
        error
            .to_string()
            .contains("must be allocated and distinct from existing"),
        "rewritten-original refusal must identify the conflict: {error}"
    );
    Ok(())
}
