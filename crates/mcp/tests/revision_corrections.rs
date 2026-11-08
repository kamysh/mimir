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
    fn start(id: uuid::Uuid) -> Result<Self> {
        let fixture = isolation::fixture();
        let stderr = std::fs::File::create(
            fixture
                .root
                .join(format!("learning-references-{id}.stderr")),
        )?;
        let mut child = tokio::process::Command::new(&fixture.mcp)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(stderr)
            .kill_on_drop(true)
            .spawn()?;
        let input = child.stdin.take().unwrap();
        let output = BufReader::new(child.stdout.take().unwrap());
        Ok(Self {
            child,
            input,
            output,
            next_id: 0,
        })
    }
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

async fn test_service() -> Result<MimirService> {
    MimirService::connect(&Config {
        database: isolation::fixture().database_config(),
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
        retirement: None,
    })
    .await
}

async fn fixture_identity() -> Result<uuid::Uuid> {
    Ok(db::connect(&isolation::fixture().database_config())
        .await?
        .query_one("SELECT gen_random_uuid()", &[])
        .await?
        .get(0))
}

async fn fixture_pattern(project: Option<&str>) -> Result<mimir_core::graph::Pattern> {
    let database = isolation::fixture().database_config();
    let db = db::connect(&database).await?;
    let row = db.query_one("SELECT gen_random_uuid(), now()", &[]).await?;
    let mut pattern = mimir_core::graph::Pattern::new(
        "reference fixture".into(),
        "explicit observed approach".into(),
        0.5,
    )?;
    pattern.id = row.get(0);
    pattern.created_at = row.get(1);
    pattern.project = project.map(str::to_owned);
    mimir_core::store::AgeStore::new(db, database.dbname)?
        .insert_pattern(&pattern)
        .await?;
    Ok(pattern)
}

fn reference_correction(value: Value, path: Value, code: Code) -> Result<()> {
    let response: NeedsInput = serde_json::from_value(value)?;
    let issue = &response.issues()[0];
    ensure!(
        issue.fault().code == code && serde_json::to_value(&issue.fault().path)? == path,
        "wrong reference diagnosis: {response:?}"
    );
    ensure!(
        issue.suggested_correction().contains("user")
            && issue.suggested_correction().contains("Do not")
    );
    Ok(())
}

#[tokio::test]
async fn learning_references_keep_exact_paths_and_refuse_before_preparation_or_publication(
) -> Result<()> {
    use mimir_core::graph::MemoryType;
    let service = test_service().await?;
    let id = fixture_identity().await?;
    let missing = fixture_identity().await?;
    let project = format!("learning-references-{id}");
    let other = format!("other-learning-references-{id}");
    let local =
        isolation::seed_belief_in_project("local fixture", 0.5, 0.1, &project, MemoryType::Fact)
            .await?;
    let foreign =
        isolation::seed_belief_in_project("foreign fixture", 0.5, 0.1, &other, MemoryType::Fact)
            .await?;
    let working = isolation::seed_belief_in_project(
        "working fixture",
        0.5,
        0.1,
        &project,
        MemoryType::Working,
    )
    .await?;
    let global = isolation::seed_belief("global fixture", 0.5, 0.1, MemoryType::Fact).await?;
    let pattern = fixture_pattern(Some(&other)).await?;
    let mut client = Client::start(id)?;
    let checked = async {
        let source = json!({"id":id,"project":project,"context":"reference fixture","action":"explicit isolated observation","outcome":"unknown","source":"agent_report","evidence":["isolated fixture receipt"]});
        for (belief, code) in [(missing, Code::MissingReference), (foreign.id, Code::WrongIdentity), (global.id, Code::WrongIdentity), (working.id, Code::UnsupportedCombination)] {
            let mut invalid = source.clone(); invalid["belief_ids"] = json!([belief]);
            reference_correction(client.call("record_experience", json!({"experience":invalid,"expected_revision":0})).await?, json!(["experience","belief_ids",0]), code)?;
            ensure!(service.get_experience(id).await?.is_none(), "refused reference published an experience");
            reference_correction(client.call("get_lesson_assessment", json!({"project":project,"belief_id":belief,"scope":"fixture","rubric":"fixture"})).await?, json!(["belief_id"]), code)?;
        }
        for (pattern_id, code) in [(missing, Code::MissingReference), (pattern.id, Code::WrongIdentity)] {
            let mut invalid = source.clone(); invalid["pattern_id"] = json!(pattern_id);
            reference_correction(client.call("record_experience", json!({"experience":invalid,"expected_revision":0})).await?, json!(["experience","pattern_id"]), code)?;
            ensure!(service.get_experience(id).await?.is_none());
        }
        let mut valid_source = source.clone(); valid_source["belief_ids"] = json!([local.id]);
        ensure!(client.call("record_experience", json!({"experience":valid_source,"expected_revision":0})).await?["revision"] == 1);
        let history = service.experience_history(id).await?;
        let review = json!({"experience_id":id,"experience_revision":1,"reviewer":"fixture","rationale":"no fabricated observation"});
        let absent = json!({"belief_id":missing});
        let present = json!({"belief_id":local.id});
        let cases = [
            ("feedback", json!([{"belief_id":missing,"verdict":"support","weight":0.5}]), json!(["review","feedback",0,"belief_id"])),
            ("superseded_beliefs", json!([missing]), json!(["review","superseded_beliefs",0])),
            ("links", json!([{"from_id":missing,"to_id":local.id,"relation":"Supports","weight":0.5}]), json!(["review","links",0,"from_id"])),
            ("links", json!([{"from_id":local.id,"to_id":missing,"relation":"Supports","weight":0.5}]), json!(["review","links",0,"to_id"])),
            ("assessments", json!([{"target":absent,"scope":"fixture","rubric":"fixture","correctness":{"value":null,"weight":0},"usefulness":{"value":null,"weight":0},"evidence_indices":[],"rationale":"unresolved"}]), json!(["review","assessments",0,"target","belief_id"])),
            ("candidate_feedback", json!([{"target":absent,"verdict":"support","weight":0.5}]), json!(["review","candidate_feedback",0,"target","belief_id"])),
            ("candidate_links", json!([{"from":absent,"to":present,"relation":"Supports","weight":0.5}]), json!(["review","candidate_links",0,"from","belief_id"])),
            ("candidate_links", json!([{"from":present,"to":absent,"relation":"Supports","weight":0.5}]), json!(["review","candidate_links",0,"to","belief_id"])),
        ];
        for (field, value, path) in cases {
            let mut invalid = review.clone(); invalid[field] = value;
            // If preparation ran first, the absent embedding configuration
            // would mask the actual invalid reference.
            invalid["candidates"] = json!([{"kind":"belief","key":"prepared-later","content":"complete candidate fixture","memory_type":"Fact"}]);
            reference_correction(client.call("review_experience", json!({"review":invalid,"expected_review_revision":0})).await?, path, Code::MissingReference)?;
            ensure!(service.experience_history(id).await? == history && service.get_experience(id).await?.unwrap().review_revision == 0);
        }
        ensure!(client.call("review_experience", json!({"review":review,"expected_review_revision":0})).await?["review_revision"] == 1);
        let score = client.call("get_lesson_assessment", json!({"project":project,"belief_id":local.id,"scope":"fixture","rubric":"fixture"})).await?;
        ensure!(score["status"] != "needs_input" && !score.is_null());
        Ok::<_, anyhow::Error>(())
    }.await;
    drop(client.input);
    let stopped = client.child.wait().await?;
    let cleanup = service.delete_project(&project).await;
    let other_cleanup = service.delete_project(&other).await;
    let global_cleanup = service.delete_belief(global.id).await;
    checked?;
    ensure!(stopped.success());
    cleanup?;
    other_cleanup?;
    global_cleanup?;
    Ok(())
}

#[tokio::test]
async fn permitted_project_and_global_patterns_remain_valid_references() -> Result<()> {
    let service = test_service().await?;
    let id = fixture_identity().await?;
    let project = format!("pattern-references-{id}");
    let local = fixture_pattern(Some(&project)).await?;
    let global = fixture_pattern(None).await?;
    let mut client = Client::start(id)?;
    let checked = async {
        for pattern in [&local, &global] {
            let source_id = fixture_identity().await?;
            let source = json!({"id":source_id,"project":project,"context":"pattern scope fixture","action":"explicit pattern use","outcome":"unknown","source":"agent_report","evidence":["isolated fixture"],"pattern_id":pattern.id});
            let recorded = client.call("record_experience", json!({"experience":source,"expected_revision":0})).await?;
            ensure!(recorded["revision"] == 1 && recorded["experience"]["pattern_id"] == json!(pattern.id), "permitted pattern was refused: {recorded}");
        }
        Ok::<_, anyhow::Error>(())
    }.await;
    drop(client.input);
    let stopped = client.child.wait().await?;
    let cleanup = service.delete_project(&project).await;
    let global_cleanup = service.delete_pattern(global.id).await;
    checked?;
    ensure!(stopped.success());
    cleanup?;
    global_cleanup?;
    Ok(())
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
