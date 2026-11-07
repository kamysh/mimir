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
        let response: Value = serde_json::from_str(&line)?;
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
            continue;
        }
        let text = response["result"]["content"][0]["text"].as_str().unwrap();
        let result: Value = serde_json::from_str(text)?;
        match name {
            "zero" => {
                let correction: NeedsInput = serde_json::from_str(text)?;
                ensure!(
                    serde_json::to_string(&correction)?
                        .contains("omit limit to return all matching beliefs"),
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
            "after-correction" => {
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
