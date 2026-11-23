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
use mimir_core::{
    config::Config,
    embed::{EmbedFuture, EmbeddingProvider},
    graph::MemoryType,
    store::AgeStore,
    MimirService,
};
use serde_json::json;

struct StaticEmbedding(Option<Vec<Vec<f32>>>);

impl EmbeddingProvider for StaticEmbedding {
    fn embed<'a>(&'a self, texts: &'a [String]) -> EmbedFuture<'a> {
        Box::pin(async move {
            ensure!(texts.len() == 1 && !texts[0].trim().is_empty());
            self.0
                .clone()
                .ok_or_else(|| anyhow::anyhow!("test embedding service unavailable"))
        })
    }
}

fn fixture_config() -> Config {
    Config {
        database: isolation::fixture().database_config(),
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
        retirement: None,
    }
}

#[ignore = "requires MIMIR_TEST_ROOT isolated fixture"]
#[tokio::test]
async fn learning_context_ranks_procedures_and_groups_assessments_in_belief_order() -> Result<()> {
    let service = MimirService::connect(&fixture_config()).await?;
    let project = format!("context{}", uuid::Uuid::new_v4().simple());
    let first = service
        .add_belief_in_project(
            &format!("{project} alpha"),
            0.6,
            0.5,
            &project,
            MemoryType::Fact,
        )
        .await?;
    let second = service
        .add_belief_in_project(
            &format!("{project} beta"),
            0.6,
            0.5,
            &project,
            MemoryType::Fact,
        )
        .await?;
    let local = service
        .add_pattern_in_project(
            &format!("{project} alpha beta"),
            "check local evidence",
            0.5,
            Some(&project),
        )
        .await?;
    let global = service
        .add_pattern_in_project(&project.to_uppercase(), "check global evidence", 0.5, None)
        .await?;
    service
        .add_pattern_in_project(
            &format!("{project} alpha beta"),
            "different project",
            0.5,
            Some("foreign-context"),
        )
        .await?;
    service
        .add_pattern_in_project(
            &format!("{project}suffix"),
            "nonmatching term",
            0.5,
            Some(&project),
        )
        .await?;

    let recorded = handle_tool_call(
        &service,
        "record_experience",
        &json!({"experience": {
            "context": project, "project": project, "action": "verify both lessons",
            "source": "tool_result", "outcome": "success", "evidence": ["both checks passed"],
            "belief_ids": [first.id, second.id], "pattern_id": global.id
        }, "expected_revision": 0}),
    )
    .await?;
    let assessments = [first.id, second.id].map(|id| {
        json!({
            "target": {"belief_id": id}, "scope": "selection", "rubric": "test",
            "correctness": {"value": 1.0, "weight": 1.0},
            "usefulness": {"value": 1.0, "weight": 1.0},
            "evidence_indices": [0], "rationale": "verified both checks"
        })
    });
    handle_tool_call(
        &service,
        "review_experience",
        &json!({"review": {
            "experience_id": recorded["experience"]["id"], "experience_revision": 1,
            "reviewer": "fixture", "rationale": "store the observed outcome",
            "assessments": assessments
        }, "expected_review_revision": 0}),
    )
    .await?;

    for (word, expected) in [
        ("alpha", [first.id, second.id]),
        ("beta", [second.id, first.id]),
    ] {
        let context = format!("{project} {word}");
        let reply = handle_tool_call(
            &service,
            "query_learning_context",
            &json!({"context": context, "project": project}),
        )
        .await?;
        ensure!(reply["semantic_search"]["cause"] == "not_configured");
        ensure!(reply["beliefs"].as_array().map(Vec::len) == Some(2));
        ensure!(reply["assessments"].as_array().map(Vec::len) == Some(2));
        for (index, id) in expected.into_iter().enumerate() {
            ensure!(reply["beliefs"][index]["id"] == json!(id));
            ensure!(reply["assessments"][index]["belief_id"] == json!(id));
        }
        ensure!(reply["assessments_truncated"] == false);
        ensure!(reply["patterns"].as_array().map(Vec::len) == Some(2));
        ensure!(reply["patterns"][0]["pattern"]["id"] == json!(local.id));
        ensure!(reply["patterns"][1]["pattern"]["id"] == json!(global.id));
        ensure!(reply["patterns"][1]["successes"] == 1);
        let limited = handle_tool_call(
            &service,
            "query_learning_context",
            &json!({"context": context, "project": project, "limit": 1}),
        )
        .await?;
        for key in ["beliefs", "patterns", "assessments"] {
            ensure!(
                limited[key] == json!([reply[key][0]]),
                "unexpected limited {key}"
            );
        }
    }

    let refusal = handle_tool_call(
        &service,
        "query_learning_context",
        &json!({"context": project, "project": " \t"}),
    )
    .await
    .expect_err("blank project requires correction");
    let refusal = refusal
        .downcast_ref::<mimir_core::validation::Refusal>()
        .ok_or_else(|| anyhow::anyhow!("expected a structured correction"))?;
    ensure!(refusal.fault.code == mimir_core::validation::Code::EmptyText);
    ensure!(serde_json::to_value(&refusal.fault.path)? == json!(["project"]));
    Ok(())
}

#[ignore = "requires MIMIR_TEST_ROOT isolated fixture"]
#[tokio::test]
async fn belief_search_applies_the_count_after_ranking_all_eligible_vectors() -> Result<()> {
    let config = fixture_config();
    let store = AgeStore::new(
        mimir_core::db::connect(&config.database).await?,
        config.database.dbname.clone(),
    )?;
    let service = MimirService::connect(&config).await?;
    let term = format!("semantic-ranking-{}", uuid::Uuid::new_v4().simple());
    let target = service
        .add_belief_in_project(&term, 0.9, 0.5, &term, MemoryType::Fact)
        .await?;
    store
        .insert_belief_embedding(target.id, &[0.0, 1.0])
        .await?;
    for i in 0..20 {
        let closer = service
            .add_belief_in_project(
                &format!("nearby vector {i}"),
                0.5,
                0.5,
                &term,
                MemoryType::Fact,
            )
            .await?;
        store
            .insert_belief_embedding(closer.id, &[1.0, 0.0])
            .await?;
    }
    let working = service
        .add_belief_in_project(&term, 0.9, 0.5, &term, MemoryType::Working)
        .await?;
    store
        .insert_belief_embedding(working.id, &[1.0, 0.0])
        .await?;
    let zero = service
        .add_belief_in_project("zero vector", 0.5, 0.5, &term, MemoryType::Fact)
        .await?;
    store.insert_belief_embedding(zero.id, &[0.0, 0.0]).await?;
    let service =
        service.with_embedding_provider(Box::new(StaticEmbedding(Some(vec![vec![1.0, 0.0]]))));

    let all = handle_tool_call(
        &service,
        "query_relevant",
        &json!({"context": term, "project": term}),
    )
    .await?;
    ensure!(all["semantic_search"]["status"] == "performed");
    ensure!(all["beliefs"].as_array().map(Vec::len) == Some(21));
    ensure!(all["beliefs"][0]["id"] == json!(target.id));
    for scope in [Some(term.as_str()), None] {
        let mut args = json!({"context": term, "limit": 1});
        if let Some(project) = scope {
            args["project"] = json!(project);
        }
        let bounded = handle_tool_call(&service, "query_relevant", &args).await?;
        ensure!(bounded["beliefs"] == json!([all["beliefs"][0]]));
        ensure!(bounded["semantic_search"] == all["semantic_search"]);
    }
    Ok(())
}

#[ignore = "requires MIMIR_TEST_ROOT isolated fixture"]
#[tokio::test]
async fn belief_search_explains_unavailable_semantics_and_keeps_lexical_matches() -> Result<()> {
    let config = fixture_config();
    let service = MimirService::connect(&config).await?;
    let term = format!("semantic-unavailable-{}", uuid::Uuid::new_v4().simple());
    let belief = service
        .add_belief_in_project(&term, 0.6, 0.5, &term, MemoryType::Fact)
        .await?;
    for response in [
        Some(vec![]),
        Some(vec![vec![1.0], vec![1.0]]),
        Some(vec![vec![0.0]]),
        Some(vec![vec![f32::NAN]]),
        None,
    ] {
        let expected = if response.is_some() {
            "invalid_provider_reply"
        } else {
            "provider_failure"
        };
        let service = MimirService::connect(&config)
            .await?
            .with_embedding_provider(Box::new(StaticEmbedding(response)));
        let reply = handle_tool_call(
            &service,
            "query_relevant",
            &json!({"context": term, "project": term, "include_evidence": true}),
        )
        .await?;
        ensure!(reply["beliefs"][0]["id"] == json!(belief.id));
        ensure!(reply["semantic_search"]["status"] == "unavailable");
        ensure!(reply["semantic_search"]["cause"] == expected);
        ensure!(reply["semantic_search"]["reason"]
            .as_str()
            .is_some_and(|reason| !reason.is_empty()));
        ensure!(reply["semantic_search"]["next_action"]
            .as_str()
            .is_some_and(|action| !action.is_empty()));
    }
    let blank = handle_tool_call(
        &service.with_embedding_provider(Box::new(StaticEmbedding(None))),
        "query_relevant",
        &json!({"context": " \t\n", "project": term}),
    )
    .await?;
    ensure!(blank["beliefs"] == json!([]));
    ensure!(blank["semantic_search"]["cause"] == "unsupported_content");
    Ok(())
}

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
    let service = MimirService::connect(&fixture_config()).await?;
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
