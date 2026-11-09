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
        let stderr = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(root.join(format!("operation-{key}.stderr")))?;
        let transcript = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(root.join(format!("operation-{key}.stdout")))?;
        let mut child = tokio::process::Command::new(env!("CARGO_BIN_EXE_mimir-mcp"))
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
        ensure!(answer["status"]=="cancelled" && answer["worker_cleanup"]=="not_confirmed_by_this_receipt");
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
