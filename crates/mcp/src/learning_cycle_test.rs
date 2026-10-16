//! Rust replacement for the old Python MCP learning-cycle check.
//! Uses the real MCP tool dispatcher and a disposable AGE database.
use super::{handle_tool_call, tools_list};
use anyhow::{ensure, Result};
use mimir_core::{
    config::{Config, DatabaseConfig, SslMode},
    MimirService,
};
use serde_json::json;
use uuid::Uuid;

#[tokio::test]
async fn candidate_review_retry_and_retrieval_through_mcp_tools() -> Result<()> {
    let dbname = std::env::var("MIMIR_DBNAME")?;
    ensure!(
        dbname.starts_with("mimir_learning_test"),
        "test DB required"
    );
    let service = MimirService::connect(&Config {
        database: DatabaseConfig {
            host: std::env::var("MIMIR_HOST")?,
            port: std::env::var("MIMIR_PORT")?.parse()?,
            user: std::env::var("MIMIR_USER")?,
            dbname,
            password: None,
            pgpassfile: None,
            ssl_mode: SslMode::Disable,
            ssl_root_cert: None,
            ssl_client_cert: None,
            ssl_client_key: None,
        },
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
    })
    .await?;
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
