//! Disconnect must reach a real owned worker without waiting for its reply.
use super::*;
#[allow(dead_code)]
mod isolation {
    include!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tests/support/isolation.rs"
    ));
}
use anyhow::{ensure, Context};
use std::{future::Future, os::unix::fs::PermissionsExt, task::Poll};

async fn blocked_request(
    service: &MimirService,
    database: &mimir_core::config::DatabaseConfig,
    project: &str,
) -> Result<Value> {
    let client = mimir_core::db::connect(database).await?;
    let chunk_id: uuid::Uuid = client
        .query_one("SELECT gen_random_uuid()", &[])
        .await?
        .get(0);
    let path = format!("/private-fixture/{project}.md");
    let passage = "The owned worker must stop when its request is cancelled.";
    let store = mimir_core::store::AgeStore::new(client, database.dbname.clone())?;
    store
        .insert_document_chunk(&mimir_core::documents::DocumentChunk::with_id(
            chunk_id,
            path.clone(),
            vec![],
            passage.into(),
            None,
            Some(project.into()),
        ))
        .await?;
    store
        .insert_chunk_embedding(chunk_id, &[1.0, 0.0, 0.0])
        .await?;
    let token = service
        .reserve_operation(&format!("blocked-{project}"))
        .await?
        .operation_token;
    Ok(
        json!({"jsonrpc":"2.0","id":1,"method":"tools/call","params":{"name":"insert_belief","arguments":{
            "operation_token":token,"content":"blocked owned embedding","probability":0.5,"confidence":0.1,
            "memory_type":"fact","project":project,"provenance":{"basis":"user_instruction","reference":"explicit isolated fixture"},
            "grounding":[{"chunk_id":chunk_id,"document_path":path,"quotation":passage,"explanation":"The passage directly states the required cancellation behavior."}]
        }}}),
    )
}

#[tokio::test]
async fn disconnect_drops_and_reaps_active_embedding_before_returning_or_starting_queued_work(
) -> Result<()> {
    let fixture = isolation::fixture();
    let database = fixture.database_config();
    let db = mimir_core::db::connect(&database).await?;
    let id: uuid::Uuid = db.query_one("SELECT gen_random_uuid()", &[]).await?.get(0);
    let directory = std::path::Path::new("/tmp").join(format!("mimir-session-{id}"));
    std::fs::create_dir(&directory)?;
    std::fs::set_permissions(&directory, std::fs::Permissions::from_mode(0o700))?;
    let ready = directory.join("r.sock");
    let listener = tokio::net::UnixListener::bind(&ready)?;
    let worker = directory.join("worker.py");
    std::fs::write(&worker,format!("#!/usr/bin/env python3\nimport json,os,socket,sys\nrequest=json.loads(sys.stdin.readline())\nprint(json.dumps({{'status':'started','version':request['version']}}),flush=True)\ns=socket.socket(socket.AF_UNIX)\ns.connect({:?})\ns.sendall((str(os.getpid())+'\\n').encode())\nwhile True: pass\n",ready.to_str().unwrap()))?;
    std::fs::set_permissions(&worker, std::fs::Permissions::from_mode(0o700))?;
    let config = Config {
        database: database.clone(),
        embeddings: Some(mimir_json::from_value(
            json!({"backend":"local","cache_dir":directory.join("model-cache")}),
        )?),
        llm: None,
        judge: None,
        email: None,
        retirement: None,
    };
    let service = MimirService::connect_with_worker(&config, worker).await?;
    let project = format!("disconnected-session-{id}");
    let protected_project = format!("unrelated-session-{id}");
    let protected = isolation::seed_belief_in_project(
        "unrelated belief survives disconnect",
        0.5,
        0.1,
        &protected_project,
        MemoryType::Fact,
    )
    .await?;
    let request = blocked_request(&service, &database, &project).await?;
    let operation_token = operation_protocol::token(&request["params"]["arguments"])?;
    let request = request.to_string() + "\n";
    // The in-memory connection holds this complete request; no production
    // quota, timer or fixed test sleep is involved.
    let (client, server) = tokio::io::duplex(request.len());
    let (client_reader, mut input) = tokio::io::split(client);
    let mut client_reader = BufReader::new(client_reader);
    input.write_all(request.as_bytes()).await?;
    let (reader, writer) = tokio::io::split(server);
    let catalogue = operation_catalogue::Catalogue::new(tools_list())?;
    let mut session = Box::pin(serve(&service, &catalogue, BufReader::new(reader), writer));
    let mut early = String::new();
    let (stream, _) = tokio::select! {
        ready=listener.accept()=>ready?,
        reply=client_reader.read_line(&mut early)=>{reply?;anyhow::bail!("fixture request returned before starting its worker: {early}")},
        result=&mut session=>anyhow::bail!("session ended before its worker blocked: {result:?}"),
    };
    let mut ready = BufReader::new(stream);
    let mut pid = String::new();
    ready.read_line(&mut pid).await?;
    let pid: u32 = pid.trim().parse()?;
    let delete_token = service
        .reserve_operation(&format!("delete-{id}"))
        .await?
        .operation_token;
    let queued=json!({"jsonrpc":"2.0","id":2,"method":"tools/call","params":{"name":"delete_belief","arguments":{"operation_token":delete_token,"id":protected.id}}}).to_string()+"\n";
    input.write_all(queued.as_bytes()).await?;
    input.shutdown().await?;
    // EOF must destroy/reap the body in this poll, before waiting for an ACK
    // connection. The asynchronous database acknowledgement may still be pending.
    let first_poll =
        std::future::poll_fn(|context| Poll::Ready(session.as_mut().poll(context))).await;
    let mut worker_socket = ready.into_inner().into_std()?;
    let mut byte = [0];
    let socket_closed = matches!(std::io::Read::read(&mut worker_socket, &mut byte), Ok(0));
    #[cfg(target_os = "linux")]
    let reaped = !std::path::PathBuf::from(format!("/proc/{pid}")).exists();
    let physically_stopped = socket_closed;
    #[cfg(target_os = "linux")]
    let physically_stopped = physically_stopped && reaped;
    if !physically_stopped {
        drop(session);
        anyhow::bail!("disconnect did not immediately stop and reap owned worker {pid}");
    }
    let ended = match first_poll {
        Poll::Ready(result) => result,
        Poll::Pending => session.as_mut().await,
    };
    drop(session);
    let pending: i64 = db.query_one(
        "SELECT count(*) FROM mimir_operation_executions WHERE operation_token=$1 AND stopped_at IS NULL", &[&operation_token]
    ).await?.get(0);
    let no_publication = service
        .list_beliefs(Some(&project))
        .await?
        .iter()
        .all(|belief| belief.project.as_deref() != Some(project.as_str()));
    let unrelated_survived = service.get_belief(protected.id).await?.is_some();
    let cleanup = service.delete_project(&project).await;
    let protected_cleanup = service.delete_project(&protected_project).await;
    ensure!(
        ended.is_ok() && pending == 0,
        "disconnect did not finish its execution acknowledgement: {ended:?}; pending={pending}"
    );
    ensure!(
        socket_closed,
        "server returned before its owned worker {pid} stopped"
    );
    #[cfg(target_os = "linux")]
    ensure!(
        reaped,
        "server returned before owned worker {pid} was reaped"
    );
    ensure!(
        no_publication && unrelated_survived,
        "disconnect published work or started the queued deletion"
    );
    cleanup?;
    protected_cleanup?;
    eprintln!(
        "Owned disconnect fixture retained at {}",
        directory.display()
    );
    Ok(())
}

#[tokio::test]
async fn cancellation_on_the_same_connection_stops_and_reaps_the_blocked_worker() -> Result<()> {
    let fixture = isolation::fixture();
    let database = fixture.database_config();
    let audit = mimir_core::db::connect(&database).await?;
    let id: uuid::Uuid = audit
        .query_one("SELECT gen_random_uuid()", &[])
        .await?
        .get(0);
    let directory = std::path::Path::new("/tmp").join(format!("mimir-cancel-session-{id}"));
    std::fs::create_dir(&directory)?;
    std::fs::set_permissions(&directory, std::fs::Permissions::from_mode(0o700))?;
    let ready = directory.join("r.sock");
    let listener = tokio::net::UnixListener::bind(&ready)?;
    let worker = directory.join("worker.py");
    std::fs::write(&worker,format!("#!/usr/bin/env python3\nimport json,os,socket,sys\nrequest=json.loads(sys.stdin.readline())\nprint(json.dumps({{'status':'started','version':request['version']}}),flush=True)\ns=socket.socket(socket.AF_UNIX)\ns.connect({:?})\ns.sendall((str(os.getpid())+'\\n').encode())\nwhile True: pass\n",ready.to_str().unwrap()))?;
    std::fs::set_permissions(&worker, std::fs::Permissions::from_mode(0o700))?;
    let config = Config {
        database: database.clone(),
        embeddings: Some(mimir_json::from_value(
            json!({"backend":"local","cache_dir":directory.join("model-cache")}),
        )?),
        llm: None,
        judge: None,
        email: None,
        retirement: None,
    };
    let service = MimirService::connect_with_worker(&config, worker).await?;
    let project = format!("cancel-session-{id}");
    let request = blocked_request(&service, &database, &project).await?;
    let token = request["params"]["arguments"]["operation_token"]
        .as_str()
        .context("missing token")?
        .to_owned();
    let cancel=json!({"jsonrpc":"2.0","id":2,"method":"tools/call","params":{"name":"cancel_operation","arguments":{"operation_token":token}}}).to_string()+"\n";
    let request = request.to_string() + "\n";
    let (client, server) = tokio::io::duplex(request.len() + cancel.len());
    let (client_reader, mut input) = tokio::io::split(client);
    let mut client_reader = BufReader::new(client_reader);
    input.write_all(request.as_bytes()).await?;
    let (reader, writer) = tokio::io::split(server);
    let catalogue = operation_catalogue::Catalogue::new(tools_list())?;
    let mut session = Box::pin(serve(&service, &catalogue, BufReader::new(reader), writer));
    let mut early = String::new();
    let (stream, _) = tokio::select! {
        ready=listener.accept()=>ready?,
        reply=client_reader.read_line(&mut early)=>{reply?;anyhow::bail!("fixture request returned before starting its worker: {early}")},
        result=&mut session=>anyhow::bail!("session ended before the worker blocked: {result:?}"),
    };
    let mut ready = BufReader::new(stream);
    let mut pid = String::new();
    ready.read_line(&mut pid).await?;
    let pid: u32 = pid.trim().parse()?;
    input.write_all(cancel.as_bytes()).await?;
    let dialogue = async {
        let mut output = client_reader;
        let mut seen = std::collections::BTreeSet::new();
        let mut transcript = String::new();
        for _ in [1, 2] {
            let mut line = String::new();
            ensure!(
                output.read_line(&mut line).await? != 0,
                "server closed before cancellation replied"
            );
            transcript.push_str(&line);
            std::fs::write(directory.join("responses.jsonl"), &transcript)?;
            let response = mimir_json::parse(&line)?;
            let request_id = response["id"].as_u64().context("missing reply identity")?;
            ensure!(
                [1, 2].contains(&request_id) && seen.insert(request_id),
                "unexpected reply: {response}"
            );
            ensure!(
                response.get("error").is_none() && response["result"]["isError"] != true,
                "cancellation must be a normal outcome: {response}"
            );
            let body = mimir_json::parse(
                response["result"]["content"][0]["text"]
                    .as_str()
                    .context("missing tool reply")?,
            )?;
            ensure!(
                body["status"] == "cancelled",
                "the original execution must read back its cancellation: {body}"
            );
            if request_id == 2 {
                ensure!(body["worker_cleanup"] == "confirmed_for_all_registered_copies");
                #[cfg(target_os = "linux")]
                ensure!(
                    !std::path::PathBuf::from(format!("/proc/{pid}")).exists(),
                    "cancel reply arrived before owned worker {pid} was reaped"
                );
            }
        }
        input.shutdown().await?;
        Ok::<_, anyhow::Error>(())
    };
    let (served, dialogue) = tokio::join!(&mut session, dialogue);
    served?;
    dialogue?;
    drop(session);
    ensure!(
        service
            .list_beliefs(Some(&project))
            .await?
            .iter()
            .all(|belief| belief.project.as_deref() != Some(project.as_str())),
        "cancelled preparation published a belief"
    );
    service.delete_project(&project).await?;
    eprintln!(
        "Same-connection cancellation fixture retained at {}",
        directory.display()
    );
    Ok(())
}

#[tokio::test]
async fn partial_input_survives_response_completion_and_concurrent_replies_keep_their_ids(
) -> Result<()> {
    let fixture = isolation::fixture();
    let config = Config {
        database: fixture.database_config(),
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
        retirement: None,
    };
    let service = MimirService::connect(&config).await?;
    let db = mimir_core::db::connect(&config.database).await?;
    let missing: uuid::Uuid = db.query_one("SELECT gen_random_uuid()", &[]).await?.get(0);
    let first = json!({"jsonrpc":"2.0","id":1,"method":"tools/list"}).to_string() + "\n";
    let second=json!({"jsonrpc":"2.0","id":2,"method":"tools/call","params":{"name":"get_belief","arguments":{"id":missing}}}).to_string()+"\n";
    let third=json!({"jsonrpc":"2.0","id":3,"method":"tools/call","params":{"name":"learning_capabilities","arguments":{}}}).to_string()+"\n";
    let split = second.len() / 2;
    // Hold a partial second frame while the catalogue response exceeds the
    // initial input's buffer. The reader then releases it without a timer.
    let (client, server) = tokio::io::duplex(first.len() + split);
    let (client_reader, mut input) = tokio::io::split(client);
    let (reader, writer) = tokio::io::split(server);
    input.write_all(first.as_bytes()).await?;
    input.write_all(&second.as_bytes()[..split]).await?;
    let catalogue = operation_catalogue::Catalogue::new(tools_list())?;
    let session = serve(&service, &catalogue, BufReader::new(reader), writer);
    let dialogue = async {
        let mut output = BufReader::new(client_reader);
        let mut line = String::new();
        output.read_line(&mut line).await?;
        let response: Value = mimir_json::from_str(&line)?;
        ensure!(response["id"] == 1 && response["result"]["tools"].is_array());
        input.write_all(&second.as_bytes()[split..]).await?;
        input.write_all(third.as_bytes()).await?;
        let mut received = std::collections::BTreeSet::new();
        for _ in [2, 3] {
            line.clear();
            output.read_line(&mut line).await?;
            let response: Value = mimir_json::from_str(&line)?;
            let id = response["id"]
                .as_u64()
                .context("missing request identity")?;
            ensure!(
                [2, 3].contains(&id) && received.insert(id) && response.get("error").is_none(),
                "partial or queued request changed: {response}"
            );
            let body: Value =
                mimir_json::from_str(response["result"]["content"][0]["text"].as_str().unwrap())?;
            if id == 2 {
                ensure!(body.is_null());
            } else {
                ensure!(body["contract_version"] == 3);
            }
        }
        input.shutdown().await?;
        Ok::<_, anyhow::Error>(())
    };
    let (served, dialogue) = tokio::join!(session, dialogue);
    served?;
    dialogue?;
    Ok(())
}
