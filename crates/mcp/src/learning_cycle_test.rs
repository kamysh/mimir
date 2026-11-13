//! Rust replacement for the old Python MCP learning-cycle check.
//! Uses the real MCP tool dispatcher and a disposable AGE database.
#[allow(dead_code)] // Shared guard exposes helpers for several test targets.
#[path = "../../../tests/support/isolation.rs"]
mod isolation;

use super::{handle_tool_call, tools_list};
use anyhow::{ensure, Result};
use mimir_core::{config::Config, MimirService};
use serde_json::json;
use uuid::Uuid;

#[tokio::test]
async fn candidate_review_retry_and_retrieval_through_mcp_tools() -> Result<()> {
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
    })
    .await?
    .with_embedding_provider(Box::new(Provider));
    let capabilities = handle_tool_call(&service, "learning_capabilities", &json!({})).await?;
    ensure!(
        capabilities["source_coverage"] == true,
        "missing source contract"
    );
    ensure!(
        capabilities["contract_version"] == 3,
        "PostgreSQL item allocation contract missing"
    );
    let source_id = Uuid::new_v4();
    let source = json!({"id":source_id,"project":"isolated-source-mcp","context":"source fixture","action":"extract all","outcome":"unknown","source":"agent_report","evidence":["event/1"],"source_records":[{"source_ref":"event/1","actor":"agent","provenance":"agent_report","text":"I suggest checking first."}]});
    handle_tool_call(
        &service,
        "record_experience",
        &json!({"experience":source,"expected_revision":0}),
    )
    .await?;
    ensure!(
        handle_tool_call(&service, "get_learning_review", &json!({"id":source_id})).await?
            ["review"]
            .is_null(),
        "new source must await review"
    );
    let receipt = json!({"experience_id":source_id,"experience_revision":1,"reviewer":"offline-fixture","rationale":"retain suggestion without inferred outcome","extracted_items":[{"key":"checking-first","kind":"suggestion","source_ref":"event/1","actor":"agent","statement":"I suggest checking first.","conditions":"untried"}],"source_coverage":[{"source_ref":"event/1","status":"unresolved","reason":"Untried suggestion requires later outcome"}]});
    let allocated = handle_tool_call(
        &service,
        "review_experience",
        &json!({"review":receipt,"expected_review_revision":0}),
    )
    .await?;
    let item_id = allocated["item_ids"]["checking-first"].clone();
    ensure!(
        item_id
            .as_str()
            .is_some_and(|id| Uuid::parse_str(id).is_ok()),
        "PostgreSQL item ID missing"
    );
    let replay = handle_tool_call(
        &service,
        "review_experience",
        &json!({"review":receipt,"expected_review_revision":0}),
    )
    .await?;
    ensure!(
        replay["item_ids"]["checking-first"] == item_id,
        "review retry reallocated the item"
    );
    ensure!(
        handle_tool_call(&service, "get_learning_review", &json!({"id":source_id})).await?
            ["review"]["source_coverage"][0]["status"]
            == "unresolved",
        "coverage receipt missing"
    );
    let tools = tools_list();
    for required in [
        "record_experience",
        "review_experience",
        "pending_experiences",
        "query_learning_context",
    ] {
        ensure!(
            tools
                .as_array()
                .unwrap()
                .iter()
                .any(|t| t["name"] == required),
            "learning tool is missing"
        );
    }
    ensure!(
        tools.as_array().unwrap().iter().any(|tool| {
            tool["name"] == "insert_belief"
                && tool["inputSchema"]["required"]
                    .as_array()
                    .is_some_and(|keys| keys.iter().any(|key| key == "provenance"))
        }),
        "insert_belief schema omits provenance"
    );
    let project = format!("mcp-learning-{}", Uuid::new_v4());
    let passage = mimir_core::documents::DocumentChunk::new(
        format!("/fixture/{project}.md"),
        vec![],
        "Restart stale keyboard layout process after checking configuration".into(),
        None,
        Some(project.clone()),
    );
    let fixture_db = isolation::fixture().database_config();
    let store = mimir_core::store::AgeStore::new(
        mimir_core::db::connect(&fixture_db).await?,
        fixture_db.dbname.clone(),
    )?;
    store
        .replace_document(
            &passage.document_path,
            std::slice::from_ref(&passage),
            &[vec![1.0, 0.0]],
        )
        .await?;
    let id = Uuid::new_v4();
    let foreign_project = format!("{project}-foreign");
    let foreign_passage = mimir_core::documents::DocumentChunk::new(
        format!("/fixture/{foreign_project}.md"),
        vec![],
        passage.content.clone(),
        None,
        Some(foreign_project.clone()),
    );
    store
        .replace_document(
            &foreign_passage.document_path,
            std::slice::from_ref(&foreign_passage),
            &[vec![1.0, 0.0]],
        )
        .await?;
    let foreign = service
        .publish_supported_belief(
            mimir_core::graph::Belief::new_in_project(
                passage.content.clone(),
                0.5,
                0.1,
                foreign_project.clone(),
            )?
            .with_memory_type(mimir_core::graph::MemoryType::Fact),
            None,
            foreign_passage.id,
        )
        .await?;
    let result: Result<()> = async {
        let experience = json!({
            "id":id,"project":project,"context":"stale keyboard indicator",
            "action":"restart layout process","outcome":"success","source":"tool_result",
            "evidence":["observed changed process and updated indicator"]
        });
        let first = handle_tool_call(
            &service,
            "record_experience",
            &json!({"experience":experience,"expected_revision":0}),
        )
        .await?;
        ensure!(first["revision"] == 1, "source was not recorded");
        ensure!(
            handle_tool_call(
                &service,
                "pending_experiences",
                &json!({"project":project,"limit":1})
            )
            .await?[0]["experience"]["id"]
                == id.to_string(),
            "source was not pending"
        );
        let review = json!({
            "experience_id":id,"experience_revision":1,"reviewer":"rust-fixture",
            "rationale":"one observed incident, one owned candidate",
            "candidates":[
                {"kind":"belief","key":"layout-lesson","content":"Restart stale keyboard layout process after checking configuration","memory_type":"Experiential","supporting_passage_id":passage.id},
                {"kind":"pattern","key":"layout-procedure","situation":"stale keyboard layout indicator","approach":"check config, restart, and verify"}
            ],
            "candidate_feedback":[{"target":{"candidate_key":"layout-lesson"},"verdict":"support","weight":0.75}]
        });
        let mut wrong_project = review.clone();
        wrong_project["assessments"] = json!([{
            "target":{"belief_id":foreign.id}, "scope":"keyboard-v1", "rubric":"benefit-v1",
            "correctness":{"value":1.0,"weight":1.0}, "usefulness":{"value":1.0,"weight":1.0},
            "evidence_indices":[0], "rationale":"scope refusal fixture"
        }]);
        let refused = handle_tool_call(&service, "review_experience", &json!({"review":wrong_project,"expected_review_revision":0}))
            .await.expect_err("a review changed another project's belief");
        let refusal = refused.downcast_ref::<mimir_core::validation::Refusal>().expect("wrong-project reference did not remain correctable input");
        ensure!(matches!(refusal.fault.code, mimir_core::validation::Code::WrongIdentity), "wrong-project reference lost its identity diagnostic");
        ensure!(refusal.fault.message.contains(&foreign.id.to_string()) && refusal.fault.message.contains(&project), "correction omitted the offending belief or expected project");
        ensure!(handle_tool_call(&service,"get_experience",&json!({"id":id})).await?["review_revision"] == 0, "rejected review was committed");
        ensure!(handle_tool_call(&service,"list_beliefs",&json!({"project":project})).await?.as_array().is_some_and(Vec::is_empty), "refused review left a belief candidate behind");
        ensure!(handle_tool_call(&service,"list_patterns",&json!({"project":project})).await?.as_array().is_some_and(Vec::is_empty), "refused review left a pattern candidate behind");
        let applied = handle_tool_call(
            &service,
            "review_experience",
            &json!({"review":review,"expected_review_revision":0}),
        )
        .await?;
        let belief_id = applied["candidate_ids"]["layout-lesson"].clone();
        let pattern_id = applied["candidate_ids"]["layout-procedure"].clone();
        ensure!(belief_id.is_string(), "candidate ID missing");
        let retry = handle_tool_call(
            &service,
            "review_experience",
            &json!({"review":review,"expected_review_revision":0}),
        )
        .await?;
        ensure!(
            retry["candidate_ids"]["layout-lesson"] == belief_id,
            "retry created another candidate"
        );
        ensure!(
            handle_tool_call(&service, "pending_experiences", &json!({"project":project}))
                .await?
                .as_array()
                .is_some_and(Vec::is_empty),
            "source remained pending"
        );
        let explanation =
            handle_tool_call(&service, "explain_belief", &json!({"id":belief_id})).await?;
        ensure!(
            explanation["candidate_provenance"]["experience_id"] == id.to_string(),
            "candidate lost incident provenance"
        );
        let context = handle_tool_call(
            &service,
            "query_learning_context",
            &json!({"project":project,"context":"stale keyboard layout process","limit":20}),
        )
        .await?;
        ensure!(
            context["beliefs"]
                .as_array()
                .is_some_and(|beliefs| beliefs.iter().any(|b| b["id"] == belief_id)),
            "later retrieval missed the candidate"
        );
        ensure!(
            context["patterns"].as_array().is_some_and(|patterns| patterns.iter().any(
                |pattern| pattern["pattern"]["id"] == pattern_id && pattern["successes"] == 0
            )),
            "retrieval alone counted as observed use"
        );
        let later_id = Uuid::new_v4();
        let mut later = json!({"id":later_id,"project":project,
            "context":"stale keyboard layout indicator",
            "action":"check config, restart, and verify",
            "outcome":"success","source":"tool_result",
            "evidence":["later process ID and indicator were verified"],
            "belief_ids":[belief_id],"pattern_id":pattern_id});
        handle_tool_call(&service, "record_experience",
            &json!({"experience":later,"expected_revision":0})).await?;
        let observed = handle_tool_call(&service,"query_learning_context",
            &json!({"project":project,"context":"stale keyboard layout indicator","limit":20})).await?;
        ensure!(observed["patterns"].as_array().is_some_and(|patterns| patterns.iter().any(
            |pattern| pattern["pattern"]["id"] == pattern_id && pattern["successes"] == 1
        )), "later observed use was not counted");
        later["outcome"] = json!("failure");
        later["source"] = json!("user_feedback");
        later["evidence"] = json!(["user corrected the later outcome"]);
        handle_tool_call(&service, "record_experience",
            &json!({"experience":later,"expected_revision":1})).await?;
        let corrected = handle_tool_call(&service,"query_learning_context",
            &json!({"project":project,"context":"stale keyboard layout indicator","limit":20})).await?;
        ensure!(corrected["patterns"].as_array().is_some_and(|patterns| patterns.iter().any(
            |pattern| pattern["pattern"]["id"] == pattern_id && pattern["successes"] == 0 && pattern["failures"] == 1
        )), "correction did not replace the later observed outcome");
        ensure!(handle_tool_call(&service,"learning_capabilities",&json!({})).await?["assessment_model_version"]==1,"missing assessment capability");
        let typed=json!({"experience_id":later_id,"experience_revision":2,"reviewer":"rust-fixture","rationale":"corrected later outcome",
            "assessments":[{"target":{"belief_id":belief_id},"scope":"keyboard-v1","rubric":"benefit-v1","correctness":{"value":0.0,"weight":1.0},"usefulness":{"value":-0.5,"weight":1.0},"evidence_indices":[0],"rationale":"explicit corrected observation"}]});
        handle_tool_call(&service,"review_experience",&json!({"review":typed,"expected_review_revision":0})).await?;
        let args=json!({"project":project,"belief_id":belief_id,"scope":"keyboard-v1","rubric":"benefit-v1"});
        let scores=handle_tool_call(&service,"get_lesson_assessment",&args).await?;
        ensure!((scores["scores"]["correctness"].as_f64().unwrap()-1.0/3.0).abs()<1e-12,"incorrect numeric assessment");
        ensure!(scores["scores"]["usefulness"]==-0.25,"incorrect benefit assessment");
        let history=handle_tool_call(&service,"lesson_assessment_history",&args).await?;
        ensure!(history["entries"][0]["active"]==true,"assessment history missing current contribution");
        let direct = json!({"content":"User requires a verification step", "probability":0.9,
            "confidence":0.5,"project":project});
        ensure!(
            handle_tool_call(&service, "insert_belief", &direct)
                .await
                .is_err(),
            "untagged direct belief was accepted"
        );
        let mut incident_labeled = direct.clone();
        incident_labeled["provenance"] = json!({"basis":"agent_report",
            "reference":"the queued incident"});
        ensure!(
            handle_tool_call(&service, "insert_belief", &incident_labeled)
                .await
                .is_err(),
            "incident report was accepted as independent provenance"
        );
        let mut independent = direct;
        independent["provenance"] = json!({"basis":"user_instruction",
            "reference":"fixture user requirement"});
        let missing_support = handle_tool_call(&service, "insert_belief", &independent)
            .await.expect_err("a belief without an indexed supporting passage was stored");
        ensure!(
            missing_support.downcast_ref::<mimir_core::validation::Refusal>()
                .is_some_and(|refusal| refusal.fault.path == vec![mimir_core::validation::Segment::Key("supporting_passage_id".into())]),
            "missing supporting passage did not explain the required correction"
        );
        independent["content"] = json!(passage.content);
        independent["supporting_passage_id"] = json!(passage.id);
        let published = handle_tool_call(&service, "insert_belief", &independent).await?;
        let stored = handle_tool_call(&service, "get_belief", &json!({"id":published["id"]})).await?;
        ensure!(stored["content"] == passage.content, "prepared direct belief was not published");
        Ok(())
    }
    .await;
    service.delete_project(&project).await?;
    service.delete_project(&foreign_project).await?;
    result
}
