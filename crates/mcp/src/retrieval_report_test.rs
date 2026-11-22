//! query_relevant / query_learning_context reply shape: the retrieval report
//! (context, beliefs, semantic_search) replaces the bare list, omitted limits
//! select all matches, and an explicit zero is refused before execution.
//! Uses the real MCP tool dispatcher and a disposable AGE database.
#[allow(dead_code)] // Shared guard exposes helpers for several test targets.
#[allow(clippy::duplicate_mod)] // Same shared guard as learning_cycle_test.
#[path = "../../../tests/support/isolation.rs"]
mod isolation;

use super::{handle_tool_call, tools_list};
use anyhow::{ensure, Result};
use mimir_core::{config::Config, graph::MemoryType, MimirService};
use serde_json::json;

#[ignore = "requires MIMIR_TEST_ROOT isolated fixture"]
#[tokio::test]
async fn evidence_preserves_the_search_and_returns_ranked_passages() -> Result<()> {
    let database = isolation::fixture().database_config();
    let store = mimir_core::store::AgeStore::new(
        mimir_core::db::connect(&database).await?,
        database.dbname.clone(),
    )?;
    let service = MimirService::connect(&Config {
        database,
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
        retirement: None,
    })
    .await?;
    let term = format!("citation-test-{}", uuid::Uuid::new_v4().simple());
    let fact = service
        .add_belief_in_project(&term, 0.9, 0.6, &term, MemoryType::Fact)
        .await?;
    let lesson = service
        .add_belief_in_project(&term, 0.4, 0.6, &term, MemoryType::Experiential)
        .await?;
    let shared = store
        .insert_document_chunk(&mimir_core::documents::DocumentChunk::new(
            "evidence.md".into(),
            vec!["Shared section".into()],
            "  shared passage  ".into(),
            None,
            Some(term.clone()),
        ))
        .await?;
    let stronger = store
        .insert_document_chunk(&mimir_core::documents::DocumentChunk::new(
            "evidence.md".into(),
            vec!["Other section".into()],
            "stronger passage".into(),
            None,
            Some(term.clone()),
        ))
        .await?;
    service.add_evidence(lesson.id, shared.id, 0.0).await?;
    service.add_evidence(lesson.id, stronger.id, 0.25).await?;
    service.add_evidence(fact.id, shared.id, 0.5).await?;

    let mut args =
        json!({"context": term, "project": term, "prefer_type": "experiential", "limit": 1});
    let plain = handle_tool_call(&service, "query_relevant", &args).await?;
    args["include_evidence"] = json!(true);
    args["evidence_per_belief"] = json!(1);
    let bounded = handle_tool_call(&service, "query_relevant", &args).await?;
    let expected_id = json!(lesson.id);
    ensure!(plain["beliefs"][0]["id"] == expected_id);
    ensure!(bounded["beliefs"][0]["id"] == expected_id);
    ensure!(bounded["context"] == plain["context"]);
    ensure!(bounded["semantic_search"] == plain["semantic_search"]);

    let sources =
        handle_tool_call(&service, "get_evidence", &json!({"belief_id": lesson.id})).await?;
    ensure!(sources.as_array().map(Vec::len) == Some(2));
    ensure!(sources[0]["chunk_id"] == json!(stronger.id));
    ensure!(
        sources[1]
            == json!({
                "chunk_id": shared.id, "document_path": "evidence.md", "section_path": ["Shared section"],
                "snippet": "shared passage", "weight": 0.0
            })
    );
    ensure!(bounded["beliefs"][0]["evidence"] == json!([sources[0]]));

    let all = handle_tool_call(
        &service,
        "query_relevant",
        &json!({"context": term, "project": term, "prefer_type": "experiential", "include_evidence": true}),
    ).await?;
    ensure!(all["beliefs"][0]["id"] == expected_id);
    ensure!(all["beliefs"][0]["evidence"] == sources);
    ensure!(all["beliefs"][1]["id"] == json!(fact.id));
    ensure!(all["beliefs"][1]["evidence"][0]["chunk_id"] == json!(shared.id));
    ensure!(all["beliefs"][1]["evidence"][0]["weight"] == json!(0.5));
    Ok(())
}

#[ignore = "requires MIMIR_TEST_ROOT isolated fixture"]
#[tokio::test]
async fn query_relevant_reports_semantic_search_and_selects_all_by_default() -> Result<()> {
    let service = MimirService::connect(&Config {
        database: isolation::fixture().database_config(),
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
        retirement: None,
    })
    .await?;
    let term = format!("retrieval-report-{}", uuid::Uuid::new_v4().simple());
    let project = format!("retrieval-{}", uuid::Uuid::new_v4().simple());
    for i in 0..12 {
        service
            .add_belief_in_project(
                &format!("{term} belief {i}"),
                0.6,
                0.6,
                &project,
                MemoryType::Fact,
            )
            .await?;
    }

    // Omitted limit: all twelve matching beliefs, in the report envelope.
    let report = handle_tool_call(
        &service,
        "query_relevant",
        &json!({"context": term, "project": project}),
    )
    .await?;
    ensure!(
        report["context"] == term,
        "report must carry the query context"
    );
    ensure!(
        report["beliefs"].as_array().map(Vec::len) == Some(12),
        "omitted limit must return every matching belief, got {}",
        report["beliefs"]
    );
    // No embedding provider is configured: the degraded lexical result must
    // say semantic search was not performed, not silently look complete.
    ensure!(
        report["semantic_search"]["status"] == "unavailable",
        "semantic_search must be reported, got {}",
        report["semantic_search"]
    );
    ensure!(
        report["semantic_search"]["cause"] == "not_configured",
        "unexpected unavailable cause: {}",
        report["semantic_search"]
    );
    ensure!(
        !report["semantic_search"]["reason"]
            .as_str()
            .unwrap_or_default()
            .is_empty()
            && !report["semantic_search"]["next_action"]
                .as_str()
                .unwrap_or_default()
                .is_empty(),
        "unavailable report must explain why and what to do next"
    );

    // Positive limit still bounds the page.
    let bounded = handle_tool_call(
        &service,
        "query_relevant",
        &json!({"context": term, "project": project, "limit": 3}),
    )
    .await?;
    ensure!(
        bounded["beliefs"].as_array().map(Vec::len) == Some(3),
        "limit=3 must return exactly three beliefs, got {}",
        bounded["beliefs"]
    );

    // Explicit zero is refused before execution with correction guidance.
    let refusal = handle_tool_call(
        &service,
        "query_relevant",
        &json!({"context": term, "project": project, "limit": 0}),
    )
    .await
    .expect_err("zero limit must be rejected");
    ensure!(
        refusal
            .downcast_ref::<mimir_core::validation::Refusal>()
            .is_some(),
        "zero limit refusal must be an actionable Refusal: {refusal:?}"
    );

    // Grounded variant keeps the same envelope and per-belief evidence arrays.
    let grounded = handle_tool_call(
        &service,
        "query_relevant",
        &json!({"context": term, "project": project, "include_evidence": true}),
    )
    .await?;
    ensure!(
        grounded["beliefs"].as_array().map(Vec::len) == Some(12),
        "grounded omitted limit must return all beliefs"
    );
    ensure!(
        grounded["beliefs"]
            .as_array()
            .unwrap()
            .iter()
            .all(|b| b.get("evidence").is_some()),
        "grounded beliefs must carry evidence arrays"
    );
    ensure!(
        grounded["semantic_search"]["status"] == "unavailable",
        "grounded report must carry semantic availability"
    );

    // Learning context carries the same semantic availability signal.
    let context = handle_tool_call(
        &service,
        "query_learning_context",
        &json!({"context": term, "project": project}),
    )
    .await?;
    ensure!(
        context["beliefs"].as_array().map(Vec::len) == Some(12),
        "learning context without limit must retrieve all beliefs, got {}",
        context["beliefs"]
    );
    ensure!(
        context["semantic_search"]["status"] == "unavailable",
        "learning context must report semantic availability, got {}",
        context["semantic_search"]
    );

    // The advertised schema no longer hides default caps.
    let tools = tools_list();
    let query_relevant = tools
        .as_array()
        .unwrap()
        .iter()
        .find(|t| t["name"] == "query_relevant")
        .expect("query_relevant advertised");
    ensure!(
        query_relevant["inputSchema"]["properties"]["limit"]
            .get("default")
            .is_none(),
        "query_relevant limit must have no hidden default"
    );
    let learning = tools
        .as_array()
        .unwrap()
        .iter()
        .find(|t| t["name"] == "query_learning_context")
        .expect("query_learning_context advertised");
    ensure!(
        learning["inputSchema"]["properties"]["limit"]
            .get("default")
            .is_none(),
        "query_learning_context limit must have no hidden default"
    );
    Ok(())
}
