//! Disconnect must reach a real owned worker without waiting for its reply.
use super::*;
#[allow(dead_code)]
mod isolation {
    include!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tests/support/isolation.rs"
    ));
}
use anyhow::ensure;
use std::{future::Future, os::unix::fs::PermissionsExt, task::Poll};

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
    std::fs::write(&worker,format!("#!/usr/bin/env python3\nimport json,os,socket,sys\njson.loads(sys.stdin.readline())\nprint(json.dumps({{'status':'started','version':1}}),flush=True)\ns=socket.socket(socket.AF_UNIX)\ns.connect({:?})\ns.sendall((str(os.getpid())+'\\n').encode())\nwhile True: pass\n",ready.to_str().unwrap()))?;
    std::fs::set_permissions(&worker, std::fs::Permissions::from_mode(0o700))?;
    let config = Config {
        database,
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
    let request=json!({"jsonrpc":"2.0","id":1,"method":"tools/call","params":{"name":"insert_belief","arguments":{"content":"blocked owned embedding","probability":0.5,"confidence":0.1,"memory_type":"fact","project":project,"provenance":{"basis":"user_instruction","reference":"explicit isolated fixture"}}}}).to_string()+"\n";
    // The in-memory connection holds this complete request; no production
    // quota, timer or fixed test sleep is involved.
    let (mut client, server) = tokio::io::duplex(request.len());
    client.write_all(request.as_bytes()).await?;
    let (reader, writer) = tokio::io::split(server);
    let catalogue = operation_catalogue::Catalogue::new(tools_list())?;
    let mut session = Box::pin(serve(&service, &catalogue, BufReader::new(reader), writer));
    let (stream, _) = tokio::select! {
        ready=listener.accept()=>ready?,
        result=&mut session=>anyhow::bail!("session ended before its worker blocked: {result:?}"),
    };
    let mut ready = BufReader::new(stream);
    let mut pid = String::new();
    ready.read_line(&mut pid).await?;
    let pid: u32 = pid.trim().parse()?;
    let queued=json!({"jsonrpc":"2.0","id":2,"method":"tools/call","params":{"name":"delete_belief","arguments":{"id":protected.id}}}).to_string()+"\n";
    client.write_all(queued.as_bytes()).await?;
    client.shutdown().await?;
    // Duplex EOF is immediately observable: one poll distinguishes the old
    // blocked handler from a server which watches disconnect during execution.
    let ended = std::future::poll_fn(|context| Poll::Ready(session.as_mut().poll(context))).await;
    let mut worker_socket = ready.into_inner().into_std()?;
    let mut byte = [0];
    let socket_closed = matches!(std::io::Read::read(&mut worker_socket, &mut byte), Ok(0));
    #[cfg(target_os = "linux")]
    let reaped = !std::path::PathBuf::from(format!("/proc/{pid}")).exists();
    // Release even the failing negative control's owner before reporting it.
    drop(session);
    let no_publication = service
        .list_beliefs(Some(&project))
        .await?
        .iter()
        .all(|belief| belief.project.as_deref() != Some(project.as_str()));
    let unrelated_survived = service.get_belief(protected.id).await?.is_some();
    let cleanup = service.delete_project(&project).await;
    let protected_cleanup = service.delete_project(&protected_project).await;
    ensure!(
        matches!(ended, Poll::Ready(Ok(()))),
        "disconnect left the active request pending: {ended:?}"
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
async fn partial_input_survives_response_completion_and_queued_requests_keep_their_order(
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
        for id in [2, 3] {
            line.clear();
            output.read_line(&mut line).await?;
            let response: Value = mimir_json::from_str(&line)?;
            ensure!(
                response["id"] == id && response.get("error").is_none(),
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
