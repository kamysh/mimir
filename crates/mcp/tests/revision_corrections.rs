//! Revision conflicts offer exact readback, without rewriting newer work.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;

use anyhow::{ensure, Result};
use mimir_core::{
    config::Config,
    db,
    interaction::NeedsInput,
    validation::{Code, Segment},
    MimirService,
};
use serde_json::{json, Value};
use std::process::Stdio;
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};

struct Client {
    child: tokio::process::Child,
    input: tokio::process::ChildStdin,
    output: BufReader<tokio::process::ChildStdout>,
    next_id: u64,
}
impl Client {
    async fn call(&mut self, name: &str, arguments: Value) -> Result<Value> {
        let request = json!({"jsonrpc":"2.0","id":self.next_id,"method":"tools/call","params":{"name":name,"arguments":arguments}});
        self.next_id += 1;
        self.input
            .write_all(format!("{request}\n").as_bytes())
            .await?;
        self.input.flush().await?;
        let mut line = String::new();
        ensure!(
            self.output.read_line(&mut line).await? != 0,
            "MCP stopped after {name}"
        );
        let response: Value = serde_json::from_str(&line)?;
        ensure!(
            response.get("error").is_none(),
            "{name} did not offer a normal result: {response}"
        );
        Ok(serde_json::from_str(
            response["result"]["content"][0]["text"].as_str().unwrap(),
        )?)
    }
}

fn correction(value: Value, path: &[&str], reads: &[&str]) -> Result<()> {
    let response: NeedsInput = serde_json::from_value(value)?;
    let issue = &response.issues()[0];
    ensure!(issue.fault().code == Code::StaleRevision);
    ensure!(
        issue.fault().path
            == path
                .iter()
                .map(|key| Segment::Key((*key).into()))
                .collect::<Vec<_>>()
    );
    for name in reads {
        ensure!(
            issue.suggested_correction().contains(name),
            "missing readback {name}"
        );
    }
    ensure!(
        issue.suggested_correction().contains("Do not")
            || issue.suggested_correction().contains("do not")
    );
    Ok(())
}

#[tokio::test]
async fn stale_revisions_offer_readback_and_preserve_history_and_exact_retries() -> Result<()> {
    let fixture = isolation::fixture();
    let database = fixture.database_config();
    let db = db::connect(&database).await?;
    let id: uuid::Uuid = db.query_one("SELECT gen_random_uuid()", &[]).await?.get(0);
    let project = format!("revision-corrections-{id}");
    let service = MimirService::connect(&Config {
        database,
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
        retirement: None,
    })
    .await?;
    let stderr = std::fs::File::create(
        fixture
            .root
            .join(format!("revision-corrections-{id}.stderr")),
    )?;
    let mut child = tokio::process::Command::new(&fixture.mcp)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(stderr)
        .kill_on_drop(true)
        .spawn()?;
    let input = child.stdin.take().unwrap();
    let output = BufReader::new(child.stdout.take().unwrap());
    let mut client = Client {
        child,
        input,
        output,
        next_id: 0,
    };
    let checked = async {
        let mut source = json!({"id":id,"project":project,"context":"revision fixture","action":"original observation","outcome":"unknown","source":"agent_report","evidence":["isolated fixture observation"]});
        correction(client.call("record_experience", json!({"experience":source,"expected_revision":1})).await?, &["expected_revision"], &["get_experience", "experience_history"])?;
        ensure!(service.get_experience(id).await?.is_none());
        let first = client.call("record_experience", json!({"experience":source,"expected_revision":0})).await?;
        ensure!(first["revision"] == 1);
        ensure!(client.call("record_experience", json!({"experience":source,"expected_revision":0})).await? == first, "exact create retry changed its result");
        source["action"] = json!("corrected observation");
        let second = client.call("record_experience", json!({"experience":source,"expected_revision":1})).await?;
        ensure!(second["revision"] == 2);
        let history = service.experience_history(id).await?;
        let mut stale = source.clone(); stale["action"] = json!("a competing stale correction");
        correction(client.call("record_experience", json!({"experience":stale,"expected_revision":1})).await?, &["expected_revision"], &["get_experience", "experience_history"])?;
        ensure!(service.experience_history(id).await? == history && service.get_experience(id).await?.unwrap().revision == 2);
        ensure!(client.call("get_experience", json!({"id":id})).await? == second);
        let mut review = json!({"experience_id":id,"experience_revision":1,"reviewer":"fixture","rationale":"no new beliefs or observed learning effects"});
        correction(client.call("review_experience", json!({"review":review,"expected_review_revision":0})).await?, &["review", "experience_revision"], &["get_experience", "get_learning_review", "experience_history"])?;
        ensure!(service.experience_history(id).await? == history);
        review["experience_revision"] = json!(2);
        let reviewed = client.call("review_experience", json!({"review":review,"expected_review_revision":0})).await?;
        ensure!(reviewed["review_revision"] == 1);
        let history = service.experience_history(id).await?;
        let mut changed = review.clone(); changed["rationale"] = json!("competing stale review");
        correction(client.call("review_experience", json!({"review":changed,"expected_review_revision":0})).await?, &["expected_review_revision"], &["get_experience", "get_learning_review"])?;
        ensure!(service.experience_history(id).await? == history, "refused review appended history or changed acknowledgement");
        let readback = client.call("get_learning_review", json!({"id":id})).await?;
        ensure!(readback["revision"] == 2 && readback["review_revision"] == 1 && readback["reviewed_revision"] == 2);
        ensure!(client.call("review_experience", json!({"review":review,"expected_review_revision":0})).await? == reviewed, "lost-reply retry did not return original review");
        ensure!(service.experience_history(id).await? == history);
        Ok::<_, anyhow::Error>(())
    }.await;
    drop(client.input);
    let stopped = client.child.wait().await?;
    let cleanup = service.delete_project(&project).await;
    checked?;
    ensure!(stopped.success());
    cleanup?;
    Ok(())
}
