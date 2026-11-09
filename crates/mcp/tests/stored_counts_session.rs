//! Corrupt stored counts offer a user dialog through the actual branch server.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;
use anyhow::{ensure, Result};
use mimir_core::{
    db,
    graph::{Edge, EdgeType, MemoryType},
    interaction::NeedsInput,
    store::AgeStore,
};
use serde_json::{json, Value};
use std::{io::Write, process::Stdio};
use tokio::io::{AsyncBufReadExt, AsyncReadExt, AsyncWriteExt, BufReader};

#[tokio::test]
async fn stored_count_problem_is_a_dialog_and_the_same_connection_recovers() -> Result<()> {
    let fixture = isolation::fixture();
    let cfg = fixture.database_config();
    let audit = db::connect(&cfg).await?;
    let key: uuid::Uuid = audit
        .query_one("SELECT gen_random_uuid()", &[])
        .await?
        .get(0);
    let project = format!("stored-count-mcp-{key}");
    let source =
        isolation::seed_belief_in_project("source", 0.8, 0.2, &project, MemoryType::Fact).await?;
    let target =
        isolation::seed_belief_in_project("target", 0.1, 0.2, &project, MemoryType::Fact).await?;
    let store = AgeStore::new(db::connect(&cfg).await?, cfg.dbname.clone())?;
    store
        .insert_edge(&Edge::new(source.id, target.id, EdgeType::Defeats, 1.0)?)
        .await?;
    audit.query(&format!("SELECT * FROM ag_catalog.cypher('{}', $$ MATCH (n:Belief {{id:'{}'}}) SET n.alpha0=-1.0 RETURN n.id $$) AS(id ag_catalog.agtype)",cfg.dbname,target.id),&[]).await?;
    let stderr = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(fixture.root.join(format!("stored-count-{key}.stderr")))?;
    let mut transcript = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(fixture.root.join(format!("stored-count-{key}.stdout")))?;
    let mut child = tokio::process::Command::new(env!("CARGO_BIN_EXE_mimir-mcp"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(stderr)
        .kill_on_drop(true)
        .spawn()?;
    let mut input = child.stdin.take().unwrap();
    let mut output = BufReader::new(child.stdout.take().unwrap());
    let checked:Result<()>=async {
        for (id,name,args) in [(1,"get_belief",json!({"id":target.id})),
            (2,"sweep_expired_defeated",json!({"project":project,"prob_threshold":0.3}))] {
            let request=json!({"jsonrpc":"2.0","id":id,"method":"tools/call","params":{"name":name,"arguments":args}});
            input.write_all(format!("{request}\n").as_bytes()).await?;input.flush().await?;
            let mut line=String::new();ensure!(output.read_line(&mut line).await?!=0,"server stopped before correction");
            transcript.write_all(line.as_bytes())?;transcript.flush()?;
            let response:Value=mimir_json::from_str(&line)?;
            ensure!(response["id"]==id && response.get("error").is_none() && !response["result"]["isError"].as_bool().unwrap_or(false),"{response}");
            let correction:NeedsInput=mimir_json::from_str(response["result"]["content"][0]["text"].as_str().unwrap())?;
            ensure!(correction.issues()[0].fault().message.contains(&target.id.to_string()));
            ensure!(correction.issues()[0].fault().message.contains("alpha0"));
            ensure!(correction.issues()[0].suggested_correction().contains("user"));
        }
        let count:i64=audit.query_one(&format!("SELECT count(*) FROM ag_catalog.cypher('{}', $$ MATCH (n:Belief) WHERE n.project='{project}' RETURN n.id $$) AS(id ag_catalog.agtype)",cfg.dbname),&[]).await?.get(0);
        ensure!(count==2,"diagnosis cannot delete the bad belief or the valid source");
        audit.query(&format!("SELECT * FROM ag_catalog.cypher('{}', $$ MATCH (n:Belief {{id:'{}'}}) SET n.alpha0={} RETURN n.id $$) AS(id ag_catalog.agtype)",cfg.dbname,target.id,target.alpha0),&[]).await?;
        input.write_all(format!("{}\n",json!({"jsonrpc":"2.0","id":3,"method":"tools/call","params":{"name":"get_belief","arguments":{"id":target.id}}})).as_bytes()).await?;input.flush().await?;
        let mut line=String::new();ensure!(output.read_line(&mut line).await?!=0);
        transcript.write_all(line.as_bytes())?;transcript.flush()?;
        let response:Value=mimir_json::from_str(&line)?;
        ensure!(response["id"]==3 && response.get("error").is_none());
        let value:Value=mimir_json::from_str(response["result"]["content"][0]["text"].as_str().unwrap())?;
        ensure!(value["id"]==target.id.to_string(),"the repaired belief remains available on the same connection: {value}");
        Ok(())
    }.await;
    drop(input);
    let mut remaining = Vec::new();
    output.read_to_end(&mut remaining).await?;
    transcript.write_all(&remaining)?;
    transcript.flush()?;
    let status = child.wait().await?;
    std::fs::write(
        fixture.root.join(format!("stored-count-{key}.exit")),
        format!("{status}\n"),
    )?;
    checked?;
    ensure!(status.success());
    store.delete_project(&project).await?;
    Ok(())
}
