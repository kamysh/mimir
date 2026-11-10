//! Exercise the real operation protocol, including correction before binding.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;
use anyhow::{ensure, Context, Result};
use mimir_core::{config::Config, db, interaction::NeedsInput, MimirService};
use serde_json::{json, Value};
use std::{io::Write, process::Stdio};
use tokio::io::{AsyncBufReadExt, AsyncReadExt, AsyncWriteExt, BufReader};
use uuid::Uuid;

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

#[cfg(feature = "test-boundaries")]
#[tokio::test]
async fn project_deletion_retries_after_real_process_exit_at_each_commit_side() -> Result<()> {
    use mimir_core::{
        documents::DocumentChunk,
        graph::MemoryType,
        operation_catalogue::{CommitSite, GraphOperation, Operation},
        store::AgeStore,
    };
    use tokio::net::UnixListener;
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
    let declared = Operation::Graph(GraphOperation::DeleteProject).committed_boundaries();
    ensure!(declared.len() == 1 && declared[0].site == CommitSite::ProjectDeletion);
    for phase in ["before_commit", "after_commit"] {
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
        // Unix socket paths have an OS-defined size. Keep this private
        // controller alongside /tmp rather than inside the long fixture path.
        use std::os::unix::fs::DirBuilderExt;
        let controller = std::env::temp_dir().join(format!("mimir-boundary-{key}"));
        std::fs::DirBuilder::new().mode(0o700).create(&controller)?;
        let socket = controller.join("control.sock");
        let listener = UnixListener::bind(&socket)?;
        let mut command = tokio::process::Command::new(env!("CARGO_BIN_EXE_mimir-mcp"));
        command
            .env("MIMIR_TEST_BOUNDARY_SOCKET", &socket)
            .env("MIMIR_TEST_BOUNDARY_TOKEN", token.to_string())
            .env("MIMIR_TEST_BOUNDARY_SITE", declared[0].site.name())
            .env("MIMIR_TEST_BOUNDARY_PHASE", phase);
        let mut session = Session::launch(&fixture.root, killed_session_key, command)?;
        let original = json!({"operation_token":token,"project":project});
        let mut pending = Box::pin(session.tool("delete_project", original.clone()));
        let transport = tokio::select! {
            accepted = listener.accept() => accepted?.0,
            early = &mut pending => anyhow::bail!("operation returned before its actual {phase} checkpoint: {early:?}"),
        };
        drop(pending);
        let mut line = String::new();
        let mut checkpoint = BufReader::new(transport);
        checkpoint.read_line(&mut line).await?;
        let event = mimir_json::parse(&line)?;
        ensure!(
            event["operation_token"] == token.to_string()
                && event["operation"] == "delete_project"
                && event["site"] == declared[0].site.name()
                && event["phase"] == phase
        );
        ensure!(event["step"].as_str().is_some_and(|name| !name.is_empty()));
        std::fs::write(fixture.root.join(format!("boundary-{key}.json")), line)?;
        // Terminate the real MCP process while it is held at the observed
        // statement boundary. No fabricated receipt or wall-clock sleep.
        session.child.kill().await?;
        ensure!(!session.child.wait().await?.success());
        drop(checkpoint);
        session.input.take();
        let mut remaining = Vec::new();
        session.output.read_to_end(&mut remaining).await?;
        session.transcript.write_all(&remaining)?;
        session.transcript.flush()?;
        let expected_before_retry = usize::from(phase == "before_commit");
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
        ensure!(
            retry
                .tool("operation_outcome", json!({"operation_token":token}))
                .await?
                == completed
        );
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
        ensure!(session.tool("operation_outcome",json!({"operation_token":token})).await?==completed);
        ensure!(session.tool("cancel_operation",json!({"operation_token":token})).await?==completed,
            "cancelling completed work must retain the original result");
        ensure!(service.list_patterns(Some(&project)).await?.len()==1);

        let reserved=session.tool("reserve_operation",json!({"request_key":format!("cancel-{key}")})).await?;
        let cancelled=reserved["operation_token"].as_str().context("missing issued token")?.to_owned();
        let answer=session.tool("cancel_operation",json!({"operation_token":cancelled})).await?;
        ensure!(answer["status"]=="cancelled" && answer["worker_cleanup"]=="confirmed_for_this_server");
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
