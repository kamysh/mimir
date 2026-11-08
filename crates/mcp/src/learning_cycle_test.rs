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
async fn pending_selection_has_no_default_and_invalid_counts_request_correction() -> Result<()> {
    use mimir_core::learning::{Experience, ObservationSource, Outcome};
    let service = MimirService::connect(&Config {
        database: isolation::fixture().database_config(),
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
        retirement: None,
    })
    .await?;
    let project = format!("all-pending-{}", Uuid::new_v4());
    let other = format!("other-pending-{}", Uuid::new_v4());
    let result = async {
        for scope in std::iter::repeat_n(&project, 32).chain(std::iter::once(&other)) {
            let source = Experience {
                id: Uuid::new_v4(),
                project: scope.clone(),
                context: "selection fixture".into(),
                action: "verify complete pending selection".into(),
                outcome: Outcome::Unknown,
                source: ObservationSource::ToolResult,
                evidence: vec!["owned database fixture".into()],
                belief_ids: vec![],
                pattern_id: None,
                learning_items: vec![],
                source_records: vec![],
            };
            service.record_experience(&source, 0).await?;
        }
        let all =
            handle_tool_call(&service, "pending_experiences", &json!({"project":project})).await?;
        let rows = all
            .as_array()
            .ok_or_else(|| anyhow::anyhow!("pending rows missing"))?;
        ensure!(
            rows.len() == 32,
            "omitted count hid pending work: {}",
            rows.len()
        );
        ensure!(
            rows.iter()
                .all(|row| row["experience"]["project"] == project),
            "project filter changed"
        );
        let one = handle_tool_call(
            &service,
            "pending_experiences",
            &json!({"project":project,"limit":1}),
        )
        .await?;
        ensure!(
            one.as_array() == Some(&rows[..1].to_vec()),
            "positive selection changed ordering"
        );
        let largest = handle_tool_call(
            &service,
            "pending_experiences",
            &json!({"project":project,"limit":usize::MAX}),
        )
        .await?;
        ensure!(largest == all, "large positive selection was narrowed");
        let excluded = json!([rows[0]["experience"]["id"], rows[31]["experience"]["id"]]);
        let filtered = handle_tool_call(
            &service,
            "pending_experiences",
            &json!({"project":project,"exclude_ids":excluded}),
        )
        .await?;
        ensure!(
            filtered.as_array() == Some(&rows[1..31].to_vec()),
            "exclusion or ordering changed"
        );
        for invalid in [json!(0), json!(-1), json!(1.5), json!("2"), json!(null)] {
            let correction = handle_tool_call(
                &service,
                "pending_experiences",
                &json!({"project":project,"limit":invalid}),
            )
            .await?;
            ensure!(
                correction["status"] == "needs_input",
                "invalid count was not a correction: {correction}"
            );
            ensure!(
                correction["business_changes"] == "none",
                "read correction claimed a mutation"
            );
            ensure!(
                correction["issues"]
                    .as_array()
                    .is_some_and(|issues| !issues.is_empty()),
                "missing correction detail"
            );
        }
        ensure!(
            handle_tool_call(&service, "pending_experiences", &json!({"project":project})).await?
                == all,
            "selection changed pending records"
        );
        let tools = tools_list();
        let count = &tools
            .as_array()
            .unwrap()
            .iter()
            .find(|tool| tool["name"] == "pending_experiences")
            .unwrap()["inputSchema"]["properties"]["limit"];
        ensure!(
            count["minimum"] == 1 && count.get("default").is_none(),
            "schema still hides a default"
        );
        Ok(())
    }
    .await;
    let cleanup = service.delete_project(&project).await;
    let other_cleanup = service.delete_project(&other).await;
    cleanup?;
    other_cleanup?;
    result
}

#[tokio::test]
async fn candidate_review_retry_and_retrieval_through_mcp_tools() -> Result<()> {
    let service = MimirService::connect(&Config {
        database: isolation::fixture().database_config(),
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
        retirement: None,
    })
    .await?;
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
    let id = Uuid::new_v4();
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
                {"kind":"belief","key":"layout-lesson","content":"Restart stale keyboard layout process after checking configuration","memory_type":"Experiential"},
                {"kind":"pattern","key":"layout-procedure","situation":"stale keyboard layout indicator","approach":"check config, restart, and verify"}
            ],
            "candidate_feedback":[{"target":{"candidate_key":"layout-lesson"},"verdict":"support","weight":0.75}]
        });
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
        let inserted = handle_tool_call(&service, "insert_belief", &independent).await?;
        let direct_explanation = handle_tool_call(
            &service,
            "explain_belief",
            &json!({"id":inserted["id"]}),
        )
        .await?;
        ensure!(
            direct_explanation["independent_provenance"] == independent["provenance"],
            "direct belief lost independent provenance"
        );
        Ok(())
    }
    .await;
    service.delete_project(&project).await?;
    result
}
