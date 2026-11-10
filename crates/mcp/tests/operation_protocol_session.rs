//! Exercise the real operation protocol, including correction before binding.
#[cfg(feature = "test-boundaries")]
#[path = "../../../tests/support/commit_boundary.rs"]
mod commit_boundary;
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;
use anyhow::{ensure, Context, Result};
use mimir_core::{config::Config, db, interaction::NeedsInput, MimirService};
use serde_json::{json, Value};
use std::{io::Write, process::Stdio};
use tokio::io::{AsyncBufReadExt, AsyncReadExt, AsyncWriteExt, BufReader};
use uuid::Uuid;

fn preserves_completed_result(readback: &Value, original: &Value) -> Result<()> {
    for field in ["operation_token", "status", "original_request", "result"] {
        ensure!(
            readback[field] == original[field],
            "readback changed original {field}"
        );
    }
    ensure!(readback["worker_cleanup"] == "not_confirmed_by_this_receipt");
    let owners: Vec<mimir_core::store::ExecutionReceipt> =
        mimir_json::decode_ref(&readback["pending_executions"])?;
    let token: Uuid = original["operation_token"]
        .as_str()
        .context("completed token")?
        .parse()?;
    ensure!(owners
        .iter()
        .all(|owner| owner.operation_token == token && owner.stopped_at.is_none()));
    Ok(())
}

struct Session {
    child: tokio::process::Child,
    input: Option<tokio::process::ChildStdin>,
    output: BufReader<tokio::process::ChildStdout>,
    transcript: std::fs::File,
    next: u64,
}
impl Session {
    fn start(root: &std::path::Path, key: Uuid) -> Result<Self> {
        Self::launch(
            root,
            key,
            tokio::process::Command::new(env!("CARGO_BIN_EXE_mimir-mcp")),
        )
    }
    fn launch(
        root: &std::path::Path,
        key: Uuid,
        mut command: tokio::process::Command,
    ) -> Result<Self> {
        let stderr = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(root.join(format!("operation-{key}.stderr")))?;
        let transcript = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(root.join(format!("operation-{key}.stdout")))?;
        let mut child = command
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(stderr)
            .kill_on_drop(true)
            .spawn()?;
        Ok(Self {
            input: child.stdin.take(),
            output: BufReader::new(child.stdout.take().unwrap()),
            child,
            transcript,
            next: 0,
        })
    }
    async fn request(&mut self, method: &str, params: Value) -> Result<mimir_json::Document> {
        self.next += 1;
        let request =
            mimir_json::Document::new(json!({"jsonrpc":"2.0","id":self.next,"method":method}));
        let mut request = request;
        request["params"] = params;
        let encoded = mimir_json::to_string(&request)?;
        self.transcript.write_all(encoded.as_bytes())?;
        self.transcript.write_all(b"\n")?;
        let input = self.input.as_mut().context("session input was closed")?;
        input.write_all(encoded.as_bytes()).await?;
        input.write_all(b"\n").await?;
        input.flush().await?;
        let mut line = String::new();
        ensure!(
            self.output.read_line(&mut line).await? != 0,
            "server stopped before replying"
        );
        self.transcript.write_all(line.as_bytes())?;
        self.transcript.flush()?;
        let reply = mimir_json::parse(&line)?;
        ensure!(
            reply["id"] == self.next && reply.get("error").is_none(),
            "protocol failure: {reply}"
        );
        Ok(mimir_json::Document::new(mimir_json::clone_value(
            &reply["result"],
        )))
    }
    async fn tool(&mut self, name: &str, arguments: Value) -> Result<mimir_json::Document> {
        let mut params = mimir_json::Document::new(json!({"name":name}));
        params["arguments"] = arguments;
        let reply = self.request("tools/call", params.into_value()).await?;
        ensure!(
            reply["isError"] != true,
            "tool failed rather than explaining its outcome: {reply}"
        );
        mimir_json::parse(
            reply["content"][0]["text"]
                .as_str()
                .context("missing tool result")?,
        )
        .map_err(Into::into)
    }
    async fn finish(mut self) -> Result<()> {
        self.input.take();
        let mut rest = Vec::new();
        self.output.read_to_end(&mut rest).await?;
        self.transcript.write_all(&rest)?;
        self.transcript.flush()?;
        ensure!(
            self.child.wait().await?.success(),
            "server did not exit successfully"
        );
        Ok(())
    }
}

#[tokio::test]
async fn missing_relationship_endpoints_preserve_bound_requests_and_offer_a_user_decision(
) -> Result<()> {
    use mimir_core::{
        graph::MemoryType,
        store::AgeStore,
        validation::{Code, Segment},
    };
    let fixture = isolation::fixture();
    let cfg = fixture.database_config();
    let audit = db::connect(&cfg).await?;
    let key: Uuid = audit
        .query_one("SELECT gen_random_uuid()", &[])
        .await?
        .get(0);
    let missing: Uuid = audit
        .query_one("SELECT gen_random_uuid()", &[])
        .await?
        .get(0);
    let project = format!("bound-endpoint-{key}");
    let source =
        isolation::seed_belief_in_project("source", 0.7, 0.5, &project, MemoryType::Fact).await?;
    let target =
        isolation::seed_belief_in_project("target", 0.4, 0.5, &project, MemoryType::Fact).await?;
    let store = AgeStore::new(db::connect(&cfg).await?, cfg.dbname.clone())?;
    ensure!(store.get_belief(missing).await?.is_none());
    let before = mimir_json::to_value((
        store.get_belief(source.id).await?,
        store.get_belief(target.id).await?,
    ))?;
    let mut session = Session::start(&fixture.root, key)?;
    let checked: Result<()> = async {
        for (name, first, second) in [("record_support", "from_id", "to_id"), ("record_cause", "from_id", "to_id"), ("record_contradiction", "id_a", "id_b")] {
            for missing_first in [true, false] {
                let left = if missing_first { missing } else { source.id }.to_string().to_uppercase();
                let right = if missing_first { target.id } else { missing }.to_string();
                let mut arguments = json!({"weight":0.5});
                arguments[first] = json!(left);
                arguments[second] = json!(right);
                let reservation = session.tool("reserve_operation", json!({"request_key":format!("bound-endpoint-{key}-{name}-{missing_first}")})).await?;
                let token: Uuid = reservation["operation_token"].as_str().context("missing reserved token")?.parse()?;
                let mut submitted = arguments.clone();
                submitted["operation_token"] = json!(token);
                let refused = session.tool(name, submitted.clone()).await?;
                let correction: NeedsInput = mimir_json::decode_ref(&refused)?;
                ensure!(refused["business_changes"] == "none");
                let fault = correction.issues()[0].fault();
                ensure!(fault.code == Code::MissingReference);
                ensure!(fault.path == vec![Segment::Key(if missing_first {first} else {second}.into())]);
                ensure!(fault.message == format!("The requested belief {missing} was not found in Mimir."));
                let binding = store.read_operation_binding(token).await?.context("request must already be bound")?;
                ensure!(binding.request.arguments() == &arguments, "refusal changed the exact submitted endpoints");
                let pending = session.tool("operation_outcome", json!({"operation_token":token})).await?;
                ensure!(pending["status"] == "pending", "{pending}");
                let saved: i64 = audit.query_one("SELECT count(*) FROM mimir_operation_step_replies WHERE operation_token=$1", &[&token]).await?.get(0);
                let cancelled: i64 = audit.query_one("SELECT count(*) FROM mimir_operation_cancellations WHERE operation_token=$1", &[&token]).await?.get(0);
                ensure!(saved == 0 && cancelled == 0, "refusal must not fabricate completion or cancel the action");
                ensure!(store.get_edges_among(&[source.id, target.id, missing]).await?.is_empty());
                ensure!(mimir_json::to_value((store.get_belief(source.id).await?, store.get_belief(target.id).await?))? == before);
                let repair = correction.issues()[0].suggested_correction();
                ensure!(repair.contains(first) && repair.contains(second) && repair.contains(&left) && repair.contains(&right), "exact original endpoints missing from correction: {refused}");
                ensure!(repair.contains("operation_outcome") && repair.contains("user") && repair.contains("cancel") && repair.contains("reserve"), "missing immutable-request decision: {refused}");
                ensure!(!repair.contains("then retry with its ID"), "bound request cannot be edited: {refused}");
                ensure!(correction.message().contains("already bound"), "top-level guidance must not suggest rewriting the request: {refused}");
                submitted[if missing_first { first } else { second }] = json!(if missing_first {source.id} else {target.id});
                let changed = session.tool(name, submitted).await?;
                let changed: NeedsInput = mimir_json::decode_ref(&changed)?;
                ensure!(changed.issues()[0].fault().code == Code::WrongIdentity);
                ensure!(store.read_operation_binding(token).await?.context("original binding retained")?.request == binding.request);
            }
        }
        Ok(())
    }.await;
    let shutdown = session.finish().await;
    let cleanup = store.delete_project(&project).await;
    checked?;
    shutdown?;
    cleanup?;
    Ok(())
}

#[cfg(feature = "test-boundaries")]
#[tokio::test]
async fn project_deletion_retries_after_real_process_exit_at_each_commit_side() -> Result<()> {
    use commit_boundary::{Controller, Phase};
    use mimir_core::{
        documents::DocumentChunk,
        graph::MemoryType,
        operation_catalogue::{CommitSite, GraphOperation, Operation},
        store::AgeStore,
    };
    let fixture = isolation::fixture();
    let audit = db::connect(&fixture.database_config()).await?;
    let store = AgeStore::new(
        db::connect(&fixture.database_config()).await?,
        fixture.database_config().dbname,
    )?;
    let config = Config {
        database: fixture.database_config(),
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
        retirement: None,
    };
    let service = MimirService::connect(&config).await?;
    let operation = Operation::Graph(GraphOperation::DeleteProject);
    let declared = operation.committed_boundaries();
    ensure!(declared.len() == 1 && declared[0].site == CommitSite::ProjectDeletion);
    for phase in [Phase::BeforeCommit, Phase::AfterCommit] {
        let ids = audit
            .query_one(
                "SELECT gen_random_uuid(),gen_random_uuid(),gen_random_uuid(),gen_random_uuid()",
                &[],
            )
            .await?;
        let key: Uuid = ids.get(0);
        let killed_session_key: Uuid = ids.get(1);
        let retry_session_key: Uuid = ids.get(2);
        let chunk_id: Uuid = ids.get(3);
        let project = format!("named-boundary-{key}");
        let unrelated = format!("named-boundary-preserved-{key}");
        let belief =
            isolation::seed_belief_in_project("owned belief", 0.5, 0.5, &project, MemoryType::Fact)
                .await?;
        let survivor = isolation::seed_belief_in_project(
            "unrelated belief",
            0.5,
            0.5,
            &unrelated,
            MemoryType::Fact,
        )
        .await?;
        let vector = vec![0.125; 384];
        store.insert_belief_embedding(belief.id, &vector).await?;
        store.insert_belief_embedding(survivor.id, &vector).await?;
        let chunk = DocumentChunk::with_id(
            chunk_id,
            format!("/private/{key}.md"),
            vec![],
            "owned passage".into(),
            None,
            Some(project.clone()),
        );
        store.insert_document_chunk(&chunk).await?;
        store.insert_chunk_embedding(chunk.id, &vector).await?;
        let reservation = service
            .reserve_operation(&format!("named-boundary-{key}"))
            .await?;
        let token = reservation.operation_token;
        let step = mimir_json::to_string(&(declared[0].site.name(), Option::<String>::None))?;
        let controller = Controller::new(token, operation, declared[0].site, step, phase)?;
        let mut command = tokio::process::Command::new(env!("CARGO_BIN_EXE_mimir-mcp"));
        controller.configure(&mut command);
        let mut session = Session::launch(&fixture.root, killed_session_key, command)?;
        let original = json!({"operation_token":token,"project":project});
        let mut pending = Box::pin(session.tool("delete_project", original.clone()));
        let checkpoint = tokio::select! {
            reached = controller.reached() => reached?,
            early = &mut pending => anyhow::bail!("operation returned before its actual {phase:?} checkpoint: {early:?}"),
        };
        drop(pending);
        let event = checkpoint.terminate(&mut session.child).await?;
        std::fs::write(
            fixture.root.join(format!("boundary-{key}.json")),
            mimir_json::to_string(&event)?,
        )?;
        session.input.take();
        let mut remaining = Vec::new();
        session.output.read_to_end(&mut remaining).await?;
        session.transcript.write_all(&remaining)?;
        session.transcript.flush()?;
        let expected_before_retry = usize::from(phase == Phase::BeforeCommit);
        ensure!(service.list_beliefs(Some(&project)).await?.len() == expected_before_retry);
        let count = audit.query_one("SELECT (SELECT count(*) FROM belief_embeddings WHERE belief_id=$1), (SELECT count(*) FROM chunk_embeddings WHERE chunk_id=$2)",&[&belief.id,&chunk.id]).await?;
        ensure!(
            count.get::<_, i64>(0) == expected_before_retry as i64
                && count.get::<_, i64>(1) == expected_before_retry as i64
        );
        let mut retry = Session::start(&fixture.root, retry_session_key)?;
        let completed = retry.tool("delete_project", original.clone()).await?;
        ensure!(
            completed["status"] == "completed" && completed["result"]["deleted"] == 2,
            "lost reply must retain the original count: {completed}"
        );
        ensure!(retry.tool("delete_project", original).await? == completed);
        let readback = retry
            .tool("operation_outcome", json!({"operation_token":token}))
            .await?;
        preserves_completed_result(&readback, &completed)?;
        retry.finish().await?;
        ensure!(service.list_beliefs(Some(&project)).await?.is_empty());
        ensure!(store.get_chunk_ids_by_project(&project).await?.is_empty());
        let count=audit.query_one("SELECT (SELECT count(*) FROM belief_embeddings WHERE belief_id=$1), (SELECT count(*) FROM chunk_embeddings WHERE chunk_id=$2), (SELECT count(*) FROM belief_embeddings WHERE belief_id=$3)",&[&belief.id,&chunk.id,&survivor.id]).await?;
        ensure!(
            count.get::<_, i64>(0) == 0
                && count.get::<_, i64>(1) == 0
                && count.get::<_, i64>(2) == 1
        );
        ensure!(
            mimir_json::to_value(service.get_belief(survivor.id).await?)?
                == mimir_json::to_value(Some(survivor))?
        );
        service.delete_project(&unrelated).await?;
    }
    Ok(())
}

#[tokio::test]
async fn writes_require_a_recoverable_identity_and_correct_input_before_binding() -> Result<()> {
    let fixture = isolation::fixture();
    let audit = db::connect(&fixture.database_config()).await?;
    let key: Uuid = audit
        .query_one("SELECT gen_random_uuid()", &[])
        .await?
        .get(0);
    let project = format!("operation-protocol-{key}");
    let config = Config {
        database: fixture.database_config(),
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
        retirement: None,
    };
    let child_config =
        std::env::var_os("MIMIR_CONFIG").context("the isolated child config is required")?;
    ensure!(
        Config::load_from_path(std::path::Path::new(&child_config))?
            .embeddings
            .is_none(),
        "this protocol case requires an isolated fixture without a model backend"
    );
    let service = MimirService::connect(&config).await?;
    let mut session = Session::start(&fixture.root, key)?;
    let checked:Result<()>=async {
        let listed=session.request("tools/list",json!({})).await?;
        let tools=listed["tools"].as_array().context("missing advertised tools")?;
        for operation in mimir_core::operation_catalogue::Operation::ALL {
            let tool=tools.iter().find(|tool|tool["name"]==operation.name()).context("missing declared operation")?;
            if operation.registered_write().is_some() {
                ensure!(tool["inputSchema"]["required"].as_array().unwrap().contains(&json!("operation_token")));
            }
        }
        let arguments=json!({"situation":"stable incident","approach":"preserve the original action","success_rate":0.8,"project":project});
        let missing=session.tool("insert_pattern",arguments.clone()).await?;
        let correction:NeedsInput=mimir_json::decode_ref(&missing)?;
        ensure!(correction.issues().iter().any(|i|mimir_json::to_value(&i.fault().path).unwrap()==json!(["operation_token"])));
        let request_key=format!("operation-protocol-{key}");
        let reserved=session.tool("reserve_operation",json!({"request_key":request_key})).await?;
        let replayed=session.tool("reserve_operation",json!({"request_key":request_key})).await?;
        ensure!(reserved==replayed,"lost reservation replies must recover the original token and time");
        let token:Uuid=reserved["operation_token"].as_str().context("missing issued token")?.parse()?;
        let mut original=arguments.clone();original["operation_token"]=json!(token);
        let completed=session.tool("insert_pattern",original.clone()).await?;
        ensure!(completed["status"]=="completed");
        ensure!(session.tool("insert_pattern",original.clone()).await?==completed);
        let mut changed=original.clone();changed["approach"]=json!("different work");
        let changed=session.tool("insert_pattern",changed).await?;
        let correction:NeedsInput=mimir_json::decode_ref(&changed)?;
        ensure!(correction.issues()[0].suggested_correction().contains("operation_outcome"));
        let readback = session.tool("operation_outcome",json!({"operation_token":token})).await?;
        preserves_completed_result(&readback, &completed)?;
        ensure!(session.tool("cancel_operation",json!({"operation_token":token})).await?==completed,
            "cancelling completed work must retain the original result");
        ensure!(service.list_patterns(Some(&project)).await?.len()==1);

        let reserved=session.tool("reserve_operation",json!({"request_key":format!("cancel-{key}")})).await?;
        let cancelled=reserved["operation_token"].as_str().context("missing issued token")?.to_owned();
        let answer=session.tool("cancel_operation",json!({"operation_token":cancelled})).await?;
        ensure!(answer["status"]=="cancelled" && answer["worker_cleanup"]=="confirmed_for_all_registered_copies");
        ensure!(session.tool("operation_outcome",json!({"operation_token":cancelled})).await?["worker_cleanup"]=="not_confirmed_by_this_receipt");
        original["operation_token"]=json!(cancelled);
        ensure!(session.tool("insert_pattern",original).await?["status"]=="cancelled");
        ensure!(service.list_patterns(Some(&project)).await?.len()==1);

        let reserved=session.tool("reserve_operation",json!({"request_key":format!("correct-{key}")})).await?;
        let corrected:Uuid=reserved["operation_token"].as_str().context("missing issued token")?.parse()?;
        let mut belief=json!({"operation_token":corrected,"content":"   ","probability":0.5,"confidence":0.5,
            "project":project,"provenance":{"basis":"user_instruction","reference":"private fixture"},
            "grounding":[{"chunk_id":key,"document_path":"/private-fixture.md","quotation":"supporting passage","explanation":"private fixture"}]});
        let refused=session.tool("insert_belief",belief.clone()).await?;
        let _:NeedsInput=mimir_json::decode_ref(&refused)?;
        ensure!(service.read_operation_binding(corrected).await?.is_none(),"invalid input must not become immutable");
        ensure!(session.tool("operation_outcome",json!({"operation_token":corrected})).await?["status"]=="reserved");
        belief["content"]=json!("corrected nonblank content");
        let refused=session.tool("insert_belief",belief).await?;
        let _:NeedsInput=mimir_json::decode_ref(&refused)?;
        let binding=service.read_operation_binding(corrected).await?.context("corrected request was not admitted")?;
        ensure!(binding.request.arguments()["content"]=="corrected nonblank content");
        ensure!(service.list_beliefs(Some(&project)).await?.is_empty(),"no belief can precede embedding and grounding");
        Ok(())
    }.await;
    let shutdown = session.finish().await;
    let cleanup = service.delete_project(&project).await;
    checked?;
    shutdown?;
    cleanup?;
    Ok(())
}
