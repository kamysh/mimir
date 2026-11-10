//! Missing stored references are correctable, without partial graph changes.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;

use anyhow::{ensure, Result};
use mimir_core::{
    config::Config,
    db,
    documents::DocumentChunk,
    graph::MemoryType,
    interaction::NeedsInput,
    store::AgeStore,
    validation::{Code, Segment},
    MimirService,
};
use serde_json::{json, Value};
use std::process::Stdio;
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};

#[tokio::test]
async fn missing_references_ask_for_lookup_without_changes_and_keep_clients_usable() -> Result<()> {
    let fixture = isolation::fixture();
    let database = fixture.database_config();
    let client = db::connect(&database).await?;
    let identities = client
        .query_one(
            "SELECT gen_random_uuid(), gen_random_uuid(), gen_random_uuid()",
            &[],
        )
        .await?;
    let missing: uuid::Uuid = identities.get(0);
    let chunk_id: uuid::Uuid = identities.get(1);
    let suffix: uuid::Uuid = identities.get(2);
    let project = format!("reference-corrections-{suffix}");
    let belief = isolation::seed_belief_in_project(
        "retained reference fixture",
        0.5,
        0.1,
        &project,
        MemoryType::Fact,
    )
    .await?;
    let store = AgeStore::new(client, database.dbname.clone())?;
    let chunk = DocumentChunk::with_id(
        chunk_id,
        format!("/mimir-test/{project}.md"),
        vec![],
        "indexed passage fixture".into(),
        None,
        Some(project.clone()),
    );
    store.insert_document_chunk(&chunk).await?;
    let service = MimirService::connect(&Config {
        database,
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
        retirement: None,
    })
    .await?;
    let before = mimir_json::to_value(service.get_belief(belief.id).await?)?;
    let edge_counts = store.count_edges().await?;
    let stderr = std::fs::File::create(
        fixture
            .root
            .join(format!("reference-corrections-{suffix}.stderr")),
    )?;
    let mut child = tokio::process::Command::new(&fixture.mcp)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(stderr)
        .kill_on_drop(true)
        .spawn()?;
    let mut input = child.stdin.take().unwrap();
    let mut output = BufReader::new(child.stdout.take().unwrap());
    let checked = async {
        let mut cases = vec![];
        for tool in ["record_support", "record_cause", "record_defeat"] {
            cases.push((tool, json!({"from_id":missing,"to_id":belief.id,"weight":0.5}), "from_id"));
            cases.push((tool, json!({"from_id":belief.id,"to_id":missing,"weight":0.5}), "to_id"));
        }
        cases.push(("record_contradiction", json!({"id_a":missing,"id_b":belief.id,"weight":0.5}), "id_a"));
        cases.push(("record_contradiction", json!({"id_a":belief.id,"id_b":missing,"weight":0.5}), "id_b"));
        cases.push(("add_evidence", json!({"belief_id":belief.id,"chunk_id":missing}), "chunk_id"));
        cases.push(("add_evidence", json!({"belief_id":missing,"chunk_id":chunk_id}), "belief_id"));
        cases.push(("query_intervention", json!({"id":missing,"value":0.5}), "id"));
        let mut intervention = None;
        for (index, (name, mut arguments, field)) in cases.into_iter().enumerate() {
            if mimir_core::operation_catalogue::Operation::ALL.iter().any(|operation|operation.name()==name && operation.registered_write().is_some()) {
                arguments["operation_token"]=json!(service.reserve_operation(&format!("mcp-reference-{suffix}-{index}")).await?.operation_token);
            }
            let request = json!({"jsonrpc":"2.0","id":index,"method":"tools/call","params":{"name":name,"arguments":arguments}});
            input.write_all(format!("{request}\n").as_bytes()).await?;
            input.flush().await?;
            let mut line = String::new();
            ensure!(output.read_line(&mut line).await? != 0, "MCP stopped on {name}");
            let response: Value = mimir_json::from_str(&line)?;
            ensure!(response.get("error").is_none(), "{name} did not offer a correction: {response}");
            let decision: NeedsInput = mimir_json::from_str(response["result"]["content"][0]["text"].as_str().unwrap())?;
            let issue = &decision.issues()[0];
            ensure!(issue.fault().code == Code::MissingReference && issue.fault().path == vec![Segment::Key(field.into())]);
            ensure!(issue.suggested_correction().contains("query_") && issue.suggested_correction().contains("user"));
            if name == "add_evidence" {
                let cli_token=service.reserve_operation(&format!("cli-reference-{suffix}-{index}")).await?.operation_token.to_string();
                let cli = tokio::process::Command::new(env!("CARGO_BIN_EXE_mimir"))
                    .args(["evidence", "add", arguments["chunk_id"].as_str().unwrap(), arguments["belief_id"].as_str().unwrap()])
                    .args(["--operation-token",&cli_token])
                    .output().await?;
                ensure!(cli.status.success(), "CLI grounding did not offer a correction: {}", String::from_utf8_lossy(&cli.stderr));
                let cli_decision: NeedsInput = mimir_json::from_slice(&cli.stdout)?;
                ensure!(cli_decision == decision, "CLI and MCP disagree on grounding references");
            }
            ensure!(mimir_json::to_value(service.get_belief(belief.id).await?)? == before);
            ensure!(store.count_edges().await? == edge_counts);
            ensure!(service.evidence_for_belief(belief.id, None).await?.is_empty());
            if name == "query_intervention" { intervention = Some(decision); }
        }
        // The same validly formed but absent ID has the same CLI diagnosis.
        let cli = tokio::process::Command::new(env!("CARGO_BIN_EXE_mimir")).args(["intervene", &missing.to_string(), "0.5"]).output().await?;
        ensure!(cli.status.success(), "CLI did not offer a correction: {}", String::from_utf8_lossy(&cli.stderr));
        let decision: NeedsInput = mimir_json::from_slice(&cli.stdout)?;
        ensure!(decision == intervention.unwrap(), "CLI and MCP disagree on a missing reference");
        // Reads and idempotent deletion retain their advertised absence results.
        // The same MCP connection remains usable after every correction.
        for (name, expected) in [("get_belief", Value::Null), ("delete_belief", json!({"deleted":false}))] {
            let mut arguments=json!({"id":missing});
            if name=="delete_belief" {arguments["operation_token"]=json!(service.reserve_operation(&format!("missing-delete-{suffix}")).await?.operation_token);}
            let request = json!({"jsonrpc":"2.0","id":name,"method":"tools/call","params":{"name":name,"arguments":arguments}});
            input.write_all(format!("{request}\n").as_bytes()).await?;
            input.flush().await?;
            let mut line = String::new();
            ensure!(output.read_line(&mut line).await? != 0);
            let response: Value = mimir_json::from_str(&line)?;
            let result: Value = mimir_json::from_str(response["result"]["content"][0]["text"].as_str().unwrap())?;
            let business=if name=="delete_belief" {&result["result"]} else {&result};
            ensure!(business == &expected, "advertised absence meaning changed: {response}");
        }
        Ok::<_, anyhow::Error>(())
    }.await;
    drop(input);
    let stopped = child.wait().await?;
    let cleanup = service.delete_project(&project).await;
    checked?;
    ensure!(stopped.success());
    cleanup?;
    Ok(())
}
