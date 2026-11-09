//! Check advertised selection and real paging through the actual MCP process.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;
use anyhow::{ensure, Result};
use mimir_core::{
    config::Config, db, graph::Belief, interaction::NeedsInput, store::AgeStore, MimirService,
};
use serde_json::{json, Value};
use std::process::Stdio;
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use uuid::Uuid;

#[tokio::test]
async fn positive_selection_has_no_ten_record_ceiling_and_zero_is_a_correction() -> Result<()> {
    let fixture = isolation::fixture();
    let cfg = Config {
        database: fixture.database_config(),
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
        retirement: None,
    };
    let service = MimirService::connect(&cfg).await?;
    let audit = db::connect(&cfg.database).await?;
    let project_id: Uuid = audit
        .query_one("SELECT gen_random_uuid()", &[])
        .await?
        .get(0);
    let project = format!("belief-page-{project_id}");
    let store = AgeStore::new(
        db::connect(&cfg.database).await?,
        cfg.database.dbname.clone(),
    )?;
    let mut owned = Vec::new();
    for n in 0..13 {
        let id: Uuid = audit
            .query_one("SELECT gen_random_uuid()", &[])
            .await?
            .get(0);
        let mut belief =
            Belief::new_in_project(format!("page selection {n}"), 0.8, 0.5, project.clone())?;
        belief.id = id;
        store.insert_belief(&belief).await?;
        owned.push(id.to_string());
    }
    let stderr_path = fixture
        .root
        .join(format!("belief-page-{project_id}.stderr"));
    let mut child = tokio::process::Command::new(&fixture.mcp)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(std::fs::File::create(stderr_path)?)
        .kill_on_drop(true)
        .spawn()?;
    let mut input = child.stdin.take().unwrap();
    let mut output = BufReader::new(child.stdout.take().unwrap());
    let requests = [
        (
            "catalogue",
            json!({"jsonrpc":"2.0","id":"catalogue","method":"tools/list"}),
        ),
        (
            "twelve",
            json!({"jsonrpc":"2.0","id":"twelve","method":"tools/call","params":{"name":"list_beliefs","arguments":{"project":project,"limit":12}}}),
        ),
        (
            "all",
            json!({"jsonrpc":"2.0","id":"all","method":"tools/call","params":{"name":"list_beliefs","arguments":{"project":project}}}),
        ),
        (
            "huge",
            json!({"jsonrpc":"2.0","id":"huge","method":"tools/call","params":{"name":"list_beliefs","arguments":{"project":project,"limit":u64::MAX}}}),
        ),
        (
            "huge-offset",
            json!({"jsonrpc":"2.0","id":"huge-offset","method":"tools/call","params":{"name":"list_beliefs","arguments":{"project":project,"limit":12,"offset":u64::MAX}}}),
        ),
        (
            "zero",
            json!({"jsonrpc":"2.0","id":"zero","method":"tools/call","params":{"name":"list_beliefs","arguments":{"project":project,"limit":0}}}),
        ),
        (
            "after-correction",
            json!({"jsonrpc":"2.0","id":"after-correction","method":"tools/call","params":{"name":"list_beliefs","arguments":{"project":project,"limit":12,"offset":12}}}),
        ),
        (
            "negative-offset",
            json!({"jsonrpc":"2.0","id":"negative-offset","method":"tools/call","params":{"name":"list_beliefs","arguments":{"project":project,"limit":12,"offset":-1}}}),
        ),
        (
            "missing-selection",
            json!({"jsonrpc":"2.0","id":"missing-selection","method":"tools/call","params":{"name":"list_beliefs","arguments":{"project":project,"offset":12}}}),
        ),
        (
            "after-offset-corrections",
            json!({"jsonrpc":"2.0","id":"after-offset-corrections","method":"tools/call","params":{"name":"list_beliefs","arguments":{"project":project,"limit":12,"offset":12}}}),
        ),
        (
            "retrieval-all",
            json!({"jsonrpc":"2.0","id":"retrieval-all","method":"tools/call","params":{"name":"query_relevant","arguments":{"context":"page selection","project":project}}}),
        ),
        (
            "retrieval-twelve",
            json!({"jsonrpc":"2.0","id":"retrieval-twelve","method":"tools/call","params":{"name":"query_relevant","arguments":{"context":"page selection","project":project,"limit":12}}}),
        ),
        (
            "learning-all",
            json!({"jsonrpc":"2.0","id":"learning-all","method":"tools/call","params":{"name":"query_learning_context","arguments":{"context":"page selection","project":project}}}),
        ),
        (
            "learning-twelve",
            json!({"jsonrpc":"2.0","id":"learning-twelve","method":"tools/call","params":{"name":"query_learning_context","arguments":{"context":"page selection","project":project,"limit":12}}}),
        ),
        (
            "retrieval-zero",
            json!({"jsonrpc":"2.0","id":"retrieval-zero","method":"tools/call","params":{"name":"query_relevant","arguments":{"context":"page selection","project":project,"limit":0}}}),
        ),
        (
            "document-zero",
            json!({"jsonrpc":"2.0","id":"document-zero","method":"tools/call","params":{"name":"query_document","arguments":{"context":"page selection","project":project,"limit":0}}}),
        ),
        (
            "learning-zero",
            json!({"jsonrpc":"2.0","id":"learning-zero","method":"tools/call","params":{"name":"query_learning_context","arguments":{"context":"page selection","project":project,"limit":0}}}),
        ),
        (
            "evidence-zero",
            json!({"jsonrpc":"2.0","id":"evidence-zero","method":"tools/call","params":{"name":"query_relevant","arguments":{"context":"page selection","project":project,"evidence_per_belief":0}}}),
        ),
        (
            "selection-string",
            json!({"jsonrpc":"2.0","id":"selection-string","method":"tools/call","params":{"name":"query_document","arguments":{"context":"page selection","project":project,"limit":"all"}}}),
        ),
        (
            "usable-after-retrieval-corrections",
            json!({"jsonrpc":"2.0","id":"usable-after-retrieval-corrections","method":"tools/call","params":{"name":"query_relevant","arguments":{"context":"page selection","project":project,"limit":12}}}),
        ),
    ];
    let mut first_page = Vec::new();
    for (name, message) in requests {
        input.write_all(format!("{message}\n").as_bytes()).await?;
        input.flush().await?;
        let mut line = String::new();
        ensure!(
            output.read_line(&mut line).await? != 0,
            "server exited during {name}"
        );
        let response: Value = mimir_json::from_str(&line)?;
        ensure!(
            response["id"] == name && response.get("error").is_none(),
            "request failed: {response}"
        );
        if name == "catalogue" {
            let descriptor = response["result"]["tools"]
                .as_array()
                .unwrap()
                .iter()
                .find(|t| t["name"] == "list_beliefs")
                .unwrap();
            ensure!(
                descriptor["inputSchema"]["properties"]["limit"]
                    .get("maximum")
                    .is_none(),
                "server still advertises a ceiling"
            );
            for tool in ["query_relevant", "query_document", "query_learning_context"] {
                let descriptor = response["result"]["tools"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .find(|entry| entry["name"] == tool)
                    .unwrap();
                let limit = &descriptor["inputSchema"]["properties"]["limit"];
                ensure!(
                    limit["minimum"] == 1 && limit.get("default").is_none(),
                    "hidden selection default in {tool}"
                );
            }
            continue;
        }
        let text = response["result"]["content"][0]["text"].as_str().unwrap();
        let result: Value = mimir_json::from_str(text)?;
        match name {
            "retrieval-zero" | "document-zero" | "learning-zero" | "evidence-zero"
            | "selection-string" => {
                let correction: NeedsInput = mimir_json::from_str(text)?;
                ensure!(
                    mimir_json::to_string(&correction)?.contains("omit"),
                    "selection correction lacks a repair: {result}"
                );
            }
            "retrieval-all" | "learning-all" => {
                let beliefs = if name == "learning-all" {
                    &result["beliefs"]
                } else {
                    &result
                };
                let ids = beliefs
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|b| b["id"].as_str().unwrap().to_owned())
                    .collect::<Vec<_>>();
                ensure!(
                    owned.iter().all(|id| ids.contains(id)),
                    "omitted retrieval selection lost matches"
                );
            }
            "retrieval-twelve" | "learning-twelve" | "usable-after-retrieval-corrections" => {
                let beliefs = if name == "learning-twelve" {
                    &result["beliefs"]
                } else {
                    &result
                };
                ensure!(
                    beliefs.as_array().unwrap().len() == 12,
                    "explicit selection was changed"
                );
            }
            "zero" | "negative-offset" | "missing-selection" => {
                let correction: NeedsInput = mimir_json::from_str(text)?;
                let issue = &correction.issues()[0];
                let (field, code) = match name {
                    "zero" => ("limit", mimir_core::validation::Code::InvalidNumber),
                    "negative-offset" => ("offset", mimir_core::validation::Code::InvalidNumber),
                    "missing-selection" => ("limit", mimir_core::validation::Code::MissingField),
                    _ => unreachable!(),
                };
                ensure!(
                    mimir_json::to_value(&issue.fault().path)? == json!([field])
                        && issue.fault().code == code
                );
                let guidance = format!("{} {}", issue.expected(), issue.suggested_correction());
                ensure!(
                    match name {
                        "zero" =>
                            guidance.contains("positive")
                                && guidance.contains("omit limit")
                                && guidance.contains("all matching"),
                        "negative-offset" =>
                            guidance.contains("nonnegative") || guidance.contains("at least 0"),
                        "missing-selection" => guidance.contains("positive limit"),
                        _ => unreachable!(),
                    },
                    "missing correction: {result}"
                );
            }
            "all" => {
                let ids = result
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|b| b["id"].as_str().unwrap().to_owned())
                    .collect::<Vec<_>>();
                ensure!(
                    owned.iter().all(|id| ids.contains(id)),
                    "omitted selection lost owned matches"
                );
            }
            "huge-offset" => ensure!(
                result["beliefs"].as_array().unwrap().is_empty(),
                "huge offset was not honored"
            ),
            "huge" => {
                let ids = result["beliefs"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|b| b["id"].as_str().unwrap().to_owned())
                    .collect::<Vec<_>>();
                ensure!(
                    owned.iter().all(|id| ids.contains(id)),
                    "large positive selection lost matches"
                );
            }
            "twelve" => {
                first_page = result["beliefs"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|b| b["id"].as_str().unwrap().to_owned())
                    .collect();
                ensure!(
                    first_page.len() == 12 && result["next_offset"] == 12,
                    "page was capped or next page missing: {result}"
                );
            }
            "after-correction" | "after-offset-corrections" => {
                let ids = result["beliefs"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|b| b["id"].as_str().unwrap().to_owned())
                    .collect::<Vec<_>>();
                ensure!(
                    !ids.is_empty() && ids.iter().all(|id| !first_page.contains(id)),
                    "paging did not continue after correction"
                );
            }
            _ => unreachable!(),
        }
    }
    drop(input);
    ensure!(child.wait().await?.success(), "server did not exit cleanly");
    service.delete_project(&project).await?;
    Ok(())
}
