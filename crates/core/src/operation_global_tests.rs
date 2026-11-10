use super::*;
use crate::{
    config::{Config, EmbeddingBackend, EmbeddingsConfig},
    db, test_isolation as isolation,
};
use std::{os::unix::fs::PermissionsExt, path::PathBuf};
use tokio::{
    io::{AsyncBufReadExt, AsyncReadExt, BufReader},
    net::{UnixListener, UnixStream},
};

fn configuration() -> Config {
    Config {
        database: isolation::fixture().database_config(),
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
        retirement: None,
    }
}

async fn action(service: &MimirService) -> Result<Uuid> {
    let client = db::connect(&service.database).await?;
    let key: Uuid = client
        .query_one("SELECT gen_random_uuid()", &[])
        .await?
        .get(0);
    Ok(service
        .reserve_operation(&key.to_string())
        .await?
        .operation_token)
}

struct Worker {
    service: Arc<MimirService>,
    job: tokio::task::JoinHandle<Result<Vec<Vec<f32>>>>,
    ready: UnixStream,
    pid: u32,
    directory: PathBuf,
}

async fn worker_setup(
    cache_dir: Option<String>,
) -> Result<(Arc<MimirService>, UnixListener, PathBuf)> {
    let mut cfg = configuration();
    let id: Uuid = db::connect(&cfg.database)
        .await?
        .query_one("SELECT gen_random_uuid()", &[])
        .await?
        .get(0);
    let directory = PathBuf::from("/tmp").join(format!("mimir-global-worker-{id}"));
    std::fs::create_dir(&directory)?;
    std::fs::set_permissions(&directory, std::fs::Permissions::from_mode(0o700))?;
    let socket = directory.join("ready.sock");
    let listener = UnixListener::bind(&socket)?;
    let program = directory.join("worker.py");
    std::fs::write(&program, format!("#!/usr/bin/env python3\nimport sys,json,socket,os\njson.loads(sys.stdin.readline())\nprint(json.dumps({{'status':'started','version':2}}),flush=True)\ns=socket.socket(socket.AF_UNIX)\ns.connect({:?})\ns.sendall((str(os.getpid())+'\\n').encode())\nsys.stdin.read()\n",socket.to_str().unwrap()))?;
    std::fs::set_permissions(&program, std::fs::Permissions::from_mode(0o700))?;
    cfg.embeddings = Some(EmbeddingsConfig {
        backend: EmbeddingBackend::Local,
        model: String::new(),
        api_key: None,
        cache_dir: Some(
            cache_dir.unwrap_or_else(|| directory.join("unused-model-cache").display().to_string()),
        ),
    });
    let service = Arc::new(MimirService::connect_with_worker(&cfg, program).await?);
    Ok((service, listener, directory))
}

async fn worker(token: Uuid) -> Result<Worker> {
    let (service, listener, directory) = worker_setup(None).await?;
    let running = service.clone();
    let mut job = tokio::spawn(async move {
        let texts = ["Complete original input; no real model is loaded.".to_owned()];
        running
            .operation_embedding_job(running.embeddings.as_ref().unwrap(), &texts, Some(token))
            .await
    });
    let (stream, _) = tokio::select! {
        connected = listener.accept() => connected?,
        returned = &mut job => anyhow::bail!("worker returned before readiness: {returned:?}"),
    };
    let mut ready = BufReader::new(stream);
    let mut pid = String::new();
    ready.read_line(&mut pid).await?;
    Ok(Worker {
        service,
        job,
        ready: ready.into_inner(),
        pid: pid.trim().parse()?,
        directory,
    })
}

async fn exited(worker: &mut Worker) -> Result<()> {
    let mut rest = Vec::new();
    worker.ready.read_to_end(&mut rest).await?;
    Ok(())
}

async fn started<F, T>(listener: &UnixListener, work: &mut Pin<Box<F>>) -> Result<(UnixStream, u32)>
where
    F: Future<Output = Result<T>>,
    T: std::fmt::Debug,
{
    let (stream, _) = tokio::select! {
        connected=listener.accept()=>connected?,
        returned=work.as_mut()=>anyhow::bail!("registered work returned before its worker started: {returned:?}"),
    };
    let mut ready = BufReader::new(stream);
    let mut pid = String::new();
    ready.read_line(&mut pid).await?;
    Ok((ready.into_inner(), pid.trim().parse()?))
}

#[tokio::test]
async fn completed_action_stops_both_duplicate_preparations_and_returns_its_exact_result(
) -> Result<()> {
    use crate::embed::{
        EmbedFuture, EmbeddingCancellation, EmbeddingProvider, OwnedEmbeddingBackend,
    };
    use std::sync::atomic::{AtomicUsize, Ordering};
    struct ReadyProvider(Arc<AtomicUsize>);
    impl EmbeddingProvider for ReadyProvider {
        fn embed<'a>(&'a self, texts: &'a [String], _: EmbeddingCancellation) -> EmbedFuture<'a> {
            Box::pin(async move {
                self.0.fetch_add(1, Ordering::SeqCst);
                Ok(vec![vec![0.125; 768]; texts.len()])
            })
        }
    }
    let cache = isolation::fixture()
        .root
        .join("controlled-shared-embedding-model")
        .display()
        .to_string();
    let mut cfg = configuration();
    cfg.embeddings = Some(EmbeddingsConfig {
        backend: EmbeddingBackend::Local,
        model: String::new(),
        api_key: None,
        cache_dir: Some(cache.clone()),
    });
    let calls = Arc::new(AtomicUsize::new(0));
    let coordinator = Arc::new(
        MimirService::connect_with_embeddings(
            &cfg,
            Some(OwnedEmbeddingBackend::for_test(Box::new(ReadyProvider(
                calls.clone(),
            )))),
        )
        .await?,
    );
    let token = action(&coordinator).await?;
    let project = format!("completed-global-{token}");
    let belief = isolation::seed_belief_in_project(
        "The original captured source needs its complete embedding.",
        0.6,
        0.5,
        &project,
        crate::graph::MemoryType::Fact,
    )
    .await?;
    assert!(matches!(
        coordinator.prepare_reembed_operation(token).await?,
        crate::store::PlanDecision::Ready(_)
    ));
    let (first, first_listener, first_directory) = worker_setup(Some(cache.clone())).await?;
    let first_source = first.clone();
    let mut first_work = Box::pin(async move { first_source.reembed_operation(token).await });
    let (mut first_socket, first_pid) = started(&first_listener, &mut first_work).await?;
    let observer = db::connect(&cfg.database).await?;
    let first_ids: Vec<_> = executions::pending(&observer, token)
        .await?
        .iter()
        .map(|row| row.execution_id)
        .collect();
    let (second, second_listener, second_directory) = worker_setup(Some(cache)).await?;
    let second_source = second.clone();
    let mut second_work = Box::pin(async move { second_source.reembed_operation(token).await });
    let (mut second_socket, second_pid) = started(&second_listener, &mut second_work).await?;
    // Their real public reembed futures are now deliberately unpolled while
    // another copy completes the same immutable plan. This is a valid scheduler
    // interleaving; the real worker processes remain blocked on their inputs.
    let original = coordinator.reembed_operation(token).await?;
    assert!(matches!(original, OperationOutcome::Completed { .. }));
    let original_reply = coordinator
        .read_operation_step(token, "@operation-result")
        .await?
        .unwrap();
    let original_payload = crate::operation_reporting::outcome(token, original)?;
    let original_calls = calls.load(Ordering::SeqCst);
    let vector: String = observer
        .query_one(
            "SELECT embedding::text FROM belief_embeddings WHERE belief_id=$1",
            &[&belief.id],
        )
        .await?
        .get(0);
    let second_row = executions::pending(&observer, token)
        .await?
        .into_iter()
        .find(|row| !first_ids.contains(&row.execution_id))
        .unwrap();
    let mut gate = db::connect(&cfg.database).await?;
    let held = gate.transaction().await?;
    held.query_one(
        "SELECT execution_id FROM mimir_operation_executions WHERE execution_id=$1 FOR UPDATE",
        &[&second_row.execution_id],
    )
    .await?;
    let mut stop_requested =
        db::OperationExecutionSubscription::cancelled(&cfg.database, token).await?;
    let caller = coordinator.clone();
    let mut cancellation = Box::pin(async move { caller.cancel_operation(token).await });
    tokio::select! {
        event=stop_requested.changed()=>event?,
        result=&mut cancellation=>anyhow::bail!("completed cancellation returned before requesting its duplicate workers to stop: {}",result.is_ok()),
    }
    let cancelling = tokio::spawn(cancellation);
    let first_job = tokio::spawn(first_work);
    let second_job = tokio::spawn(second_work);
    let mut first_tail = Vec::new();
    let mut second_tail = Vec::new();
    let (first_exit, second_exit) = tokio::join!(
        first_socket.read_to_end(&mut first_tail),
        second_socket.read_to_end(&mut second_tail)
    );
    first_exit?;
    second_exit?;
    assert!(
        !cancelling.is_finished(),
        "completed business data is not a stop acknowledgement"
    );
    assert_eq!(
        observer
            .query_one(
                "SELECT count(*) FROM mimir_operation_cancellations WHERE operation_token=$1",
                &[&token]
            )
            .await?
            .get::<_, i64>(0),
        0
    );
    let readback = crate::operation_reporting::readback(
        token,
        coordinator.read_operation_outcome(token, None).await?,
    )?;
    assert_eq!(readback["status"], "completed");
    assert_eq!(readback["result"], original_payload["result"]);
    assert!(!readback["pending_executions"]
        .as_array()
        .unwrap()
        .is_empty());
    held.rollback().await?;
    let completed = cancelling.await??;
    assert!(completed.all_cleanup_confirmed());
    assert_eq!(
        crate::operation_reporting::cancellation(token, completed)?,
        original_payload
    );
    let _ = first_job.await?;
    let _ = second_job.await?;
    assert_eq!(
        coordinator
            .read_operation_step(token, "@operation-result")
            .await?,
        Some(original_reply)
    );
    assert_eq!(
        observer
            .query_one(
                "SELECT embedding::text FROM belief_embeddings WHERE belief_id=$1",
                &[&belief.id]
            )
            .await?
            .get::<_, String>(0),
        vector
    );
    assert_eq!(calls.load(Ordering::SeqCst), original_calls);
    assert!(executions::pending(&observer, token).await?.is_empty());
    #[cfg(target_os = "linux")]
    for pid in [first_pid, second_pid] {
        assert!(!PathBuf::from(format!("/proc/{pid}")).exists());
    }
    println!(
        "completed duplicate artifacts: {} {}",
        first_directory.display(),
        second_directory.display()
    );
    Ok(())
}

#[tokio::test]
async fn global_cancel_waits_for_both_copy_acknowledgements_and_preserves_other_work() -> Result<()>
{
    let coordinator = Arc::new(MimirService::connect(&configuration()).await?);
    let token = action(&coordinator).await?;
    let unrelated = action(&coordinator).await?;
    let mut first = worker(token).await?;
    let observer = db::connect(&coordinator.database).await?;
    let first_id = executions::pending(&observer, token).await?[0].execution_id;
    let mut second = worker(token).await?;
    let mut other = worker(unrelated).await?;
    let second_row = executions::pending(&observer, token)
        .await?
        .into_iter()
        .find(|row| row.execution_id != first_id)
        .unwrap();
    let mut gate = db::connect(&coordinator.database).await?;
    let held = gate.transaction().await?;
    held.query_one(
        "SELECT execution_id FROM mimir_operation_executions WHERE execution_id=$1 FOR UPDATE",
        &[&second_row.execution_id],
    )
    .await?;
    let caller = coordinator.clone();
    let cancelling = tokio::spawn(async move { caller.cancel_operation(token).await });
    exited(&mut first).await?;
    exited(&mut second).await?;
    assert!(
        !cancelling.is_finished(),
        "a worker exit alone cannot replace its blocked durable ACK"
    );
    let outcome = coordinator.read_operation_outcome(token, None).await?;
    let OperationOutcome::Cancelled {
        pending_executions, ..
    } = &outcome
    else {
        panic!("revocation not visible")
    };
    assert!(pending_executions
        .iter()
        .any(|row| row.execution_id == second_row.execution_id));
    assert_eq!(second_row.owner_pid, i64::from(std::process::id()));
    assert_eq!(
        second_row.owner_program,
        std::env::current_exe()?.display().to_string()
    );
    let observed_address: Option<String> = observer
        .query_one("SELECT inet_client_addr()::text", &[])
        .await?
        .get(0);
    assert_eq!(second_row.client_address, observed_address);
    #[cfg(target_os = "linux")]
    {
        if let Ok(actual) = std::fs::read_to_string("/proc/sys/kernel/hostname") {
            let actual = actual.trim_end_matches('\n');
            if !actual.is_empty() {
                assert_eq!(second_row.owner_host.as_deref(), Some(actual));
                assert_eq!(
                    second_row.owner_host_source.as_deref(),
                    Some("kernel_hostname")
                );
            }
        }
    }
    let report = crate::operation_reporting::outcome(token, outcome)?;
    assert_eq!(report["worker_cleanup"], "not_confirmed_by_this_receipt");
    assert!(!report["pending_executions"].as_array().unwrap().is_empty());
    #[cfg(target_os = "linux")]
    assert!(
        PathBuf::from(format!("/proc/{}", other.pid)).exists(),
        "another action was stopped"
    );
    held.rollback().await?;
    let cancelled = cancelling.await??;
    assert!(cancelled.all_cleanup_confirmed());
    let result = crate::operation_reporting::cancellation(token, cancelled)?;
    assert_eq!(
        result["worker_cleanup"],
        "confirmed_for_all_registered_copies"
    );
    assert!(executions::pending(&observer, token).await?.is_empty());
    assert!(first.job.await?.is_err());
    assert!(second.job.await?.is_err());
    #[cfg(target_os = "linux")]
    for pid in [first.pid, second.pid] {
        assert!(!PathBuf::from(format!("/proc/{pid}")).exists());
    }
    assert!(coordinator
        .cancel_operation(unrelated)
        .await?
        .all_cleanup_confirmed());
    exited(&mut other).await?;
    assert!(other.job.await?.is_err());
    // Keep owned diagnostic directories and the disposable fixture for review.
    println!(
        "worker artifacts: {} {} {}",
        first.directory.display(),
        second.directory.display(),
        other.directory.display()
    );
    Ok(())
}

#[tokio::test]
async fn disconnected_request_stays_pending_until_its_original_host_acknowledges() -> Result<()> {
    let coordinator = Arc::new(MimirService::connect(&configuration()).await?);
    let token = action(&coordinator).await?;
    let mut copy = worker(token).await?;
    copy.job.abort();
    assert!((&mut copy.job).await.unwrap_err().is_cancelled());
    exited(&mut copy).await?;
    let mut revoked =
        db::OperationExecutionSubscription::cancelled(&coordinator.database, token).await?;
    let caller = coordinator.clone();
    let cancelling = tokio::spawn(async move { caller.cancel_operation(token).await });
    revoked.changed().await?;
    let outcome = coordinator.read_operation_outcome(token, None).await?;
    let OperationOutcome::Cancelled {
        pending_executions, ..
    } = outcome
    else {
        panic!("cancellation absent")
    };
    assert_eq!(pending_executions.len(), 1);
    assert!(
        !cancelling.is_finished(),
        "connection loss must not acknowledge an execution"
    );
    copy.service.finish_operation_host().await?;
    assert!(cancelling.await??.all_cleanup_confirmed());
    println!("disconnected owner artifacts: {}", copy.directory.display());
    Ok(())
}

#[tokio::test]
async fn registration_is_fenced_and_stop_acknowledgement_replays_original_time() -> Result<()> {
    let service = MimirService::connect(&configuration()).await?;
    let token = action(&service).await?;
    let mut client = db::connect(&service.database).await?;
    let (registered, ()) = executions::register(&mut client, token, |_| ())
        .await?
        .unwrap();
    service.record_operation_cancellation(token).await?;
    assert!(executions::register(&mut client, token, |_| ())
        .await?
        .is_none());
    assert_eq!(
        executions::pending(&client, token).await?,
        vec![registered.clone()]
    );
    // This execution never began a body. Its owner may now acknowledge that
    // fact even though publication has already been revoked.
    let first = executions::acknowledge(&mut client, &registered)
        .await?
        .unwrap();
    let second = executions::acknowledge(&mut client, &registered)
        .await?
        .unwrap();
    assert!(first.stopped_at.is_some());
    assert_eq!(first, second);
    assert!(executions::pending(&client, token).await?.is_empty());
    Ok(())
}

#[tokio::test]
async fn dropping_registration_after_returning_retains_its_original_stop_owner() -> Result<()> {
    let service = Arc::new(MimirService::connect(&configuration()).await?);
    let token = action(&service).await?;
    let (sent, received) = tokio::sync::oneshot::channel();
    let source = service.clone();
    let task = tokio::spawn(async move {
        let mut client = db::connect(&source.database).await?;
        let registration = executions::register(&mut client, token, |execution| {
            let _ = sent.send(execution.clone());
            RegistrationOwner {
                registry: source.operation_executions.clone(),
                execution: Some(execution.clone()),
            }
        })
        .await;
        drop(registration);
        Ok::<(), anyhow::Error>(())
    });
    let original = received.await?;
    task.abort();
    let _ = task.await;
    service.finish_operation_host().await?;
    let client = db::connect(&service.database).await?;
    let row = client
        .query_opt(
            "SELECT stopped_at FROM mimir_operation_executions WHERE execution_id=$1",
            &[&original.execution_id],
        )
        .await?;
    if let Some(row) = row {
        assert!(row
            .get::<_, Option<chrono::DateTime<chrono::Utc>>>(0)
            .is_some());
    }
    assert!(executions::pending(&client, token).await?.is_empty());
    Ok(())
}
