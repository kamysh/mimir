//! A worker lease owns the OS process, not just a task waiting for inference.
use super::*;
use serde::{Deserialize, Serialize};
use std::io::{BufRead, Write};
use std::process::{Child, Command, Stdio};
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};

const FLAG: &str = "--embedding-worker";
const VERSION: u32 = 2;

#[derive(Default)]
pub(super) struct Cleanup {
    unreaped: Mutex<Vec<UnreapedWorker>>,
}

struct UnreapedWorker {
    child: Option<Child>,
    directory: PathBuf,
    partials: Vec<PathBuf>,
    error: String,
}

impl UnreapedWorker {
    fn retry(&mut self) -> std::io::Result<()> {
        let Some(child) = self.child.as_mut() else {
            return Ok(());
        };
        // The initial owner already attempted kill+wait. A failed wait may
        // mean another reaper consumed the child, so never signal that PID
        // again. Only an actual wait receipt can resolve this uncertainty.
        if child.try_wait()?.is_none() {
            return Err(std::io::Error::other(
                "the local worker has not reported exit after the earlier failed cleanup",
            ));
        }
        self.child.take();
        remove_partials(&self.partials);
        Ok(())
    }
}

impl Drop for UnreapedWorker {
    fn drop(&mut self) {
        if let Err(error) = self.retry() {
            tracing::error!(%error, diagnostics = %self.directory.display(), "local worker cleanup remains unconfirmed");
        }
    }
}

impl Cleanup {
    pub(super) fn pending(&self) -> bool {
        !self
            .unreaped
            .lock()
            .unwrap_or_else(|error| error.into_inner())
            .is_empty()
    }

    pub(super) fn retry(&self) -> Vec<WorkerCleanupIssue> {
        let mut pending = self
            .unreaped
            .lock()
            .unwrap_or_else(|error| error.into_inner());
        pending.retain_mut(|worker| match worker.retry() {
            Ok(()) => false,
            Err(error) => {
                worker.error = error.to_string();
                true
            }
        });
        pending
            .iter()
            .filter_map(|worker| {
                worker.child.as_ref().map(|child| WorkerCleanupIssue {
                    pid: child.id(),
                    diagnostics: worker.directory.clone(),
                    error: worker.error.clone(),
                })
            })
            .collect()
    }

    fn retain(
        &self,
        child: Child,
        directory: PathBuf,
        partials: Vec<PathBuf>,
        error: std::io::Error,
    ) {
        self.unreaped
            .lock()
            .unwrap_or_else(|poison| poison.into_inner())
            .push(UnreapedWorker {
                child: Some(child),
                directory,
                partials,
                error: error.to_string(),
            });
    }
}

fn remove_partials(paths: &[PathBuf]) {
    for path in paths {
        if let Err(error) = std::fs::remove_file(path) {
            if error.kind() != std::io::ErrorKind::NotFound {
                tracing::warn!(%error, path = %path.display(), "could not remove worker partial download");
            }
        }
    }
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Request {
    version: u32,
    texts: Vec<String>,
    cache_dir: Option<String>,
}

#[derive(Serialize, Deserialize)]
#[serde(tag = "status", rename_all = "snake_case", deny_unknown_fields)]
enum Response {
    Started { version: u32 },
    Complete { vectors: Vec<Vec<f32>> },
    Failed { message: String },
}

pub(super) struct LocalBackend {
    idle: Mutex<Vec<Worker>>,
    cache_dir: Option<String>,
    executable: Option<PathBuf>,
}

impl LocalBackend {
    pub(super) fn new(cache_dir: Option<String>, executable: Option<PathBuf>) -> Self {
        Self {
            idle: Mutex::new(Vec::new()),
            cache_dir: cache_dir
                .map(|path| path.trim().to_owned())
                .filter(|path| !path.is_empty()),
            executable,
        }
    }
}

impl EmbeddingProvider for LocalBackend {
    fn embed<'a>(
        &'a self,
        texts: &'a [String],
        cancellation: EmbeddingCancellation,
    ) -> EmbedFuture<'a> {
        Box::pin(async move {
            cancellation.check()?;
            if texts.is_empty() {
                return Ok(Vec::new());
            }
            let idle = self
                .idle
                .lock()
                .map_err(|_| anyhow::anyhow!("local worker pool poisoned"))?
                .pop();
            let mut worker = match idle {
                Some(worker) => worker,
                None => Worker::spawn_with_cleanup(
                    match &self.executable {
                        Some(path) => path.clone(),
                        None => std::env::current_exe()?,
                    },
                    cancellation.cleanup.clone(),
                )?,
            };
            worker.cleanup = cancellation.cleanup.clone();
            let request = Request {
                version: VERSION,
                texts: texts.to_vec(),
                cache_dir: self.cache_dir.clone(),
            };
            let result = worker.exchange(&request).await;
            cancellation.check()?;
            match result {
                Ok(vectors) => {
                    // The completed protocol reply ended this job. The idle
                    // process is now owned by the backend, not this operation.
                    worker.cleanup = Arc::new(Cleanup::default());
                    self.idle
                        .lock()
                        .map_err(|_| anyhow::anyhow!("local worker pool poisoned"))?
                        .push(worker);
                    Ok(vectors)
                }
                Err(error) => {
                    worker.preserve = true;
                    Err(error.context(format!(
                        "local embedding worker failed; complete private diagnostics: {}",
                        worker.directory.display()
                    )))
                }
            }
        })
    }
}

struct Worker {
    // The child is kept even if stdio conversion or exchange fails.
    child: Option<Child>,
    cleanup: Arc<Cleanup>,
    input: Option<tokio::process::ChildStdin>,
    output: Option<BufReader<tokio::process::ChildStdout>>,
    directory: PathBuf,
    preserve: bool,
    partials: Vec<PathBuf>,
}

impl Worker {
    #[cfg(test)]
    fn spawn(executable: PathBuf) -> Result<Self> {
        Self::spawn_with_cleanup(executable, Arc::new(Cleanup::default()))
    }

    fn id(&self) -> u32 {
        self.child
            .as_ref()
            .expect("worker child is owned until drop")
            .id()
    }

    fn spawn_with_cleanup(executable: PathBuf, cleanup: Arc<Cleanup>) -> Result<Self> {
        use std::os::unix::fs::DirBuilderExt;
        let directory =
            std::env::temp_dir().join(format!("mimir-embedding-{}", uuid::Uuid::new_v4()));
        std::fs::DirBuilder::new().mode(0o700).create(&directory)?;
        let stderr = std::fs::File::create(directory.join("stderr.log"))?;
        let spawned = Command::new(executable)
            .arg(FLAG)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(stderr)
            .spawn();
        let child = match spawned {
            Ok(child) => child,
            Err(error) => {
                let _ = std::fs::remove_dir_all(&directory);
                return Err(error.into());
            }
        };
        let mut worker = Self {
            child: Some(child),
            cleanup,
            input: None,
            output: None,
            directory,
            preserve: false,
            partials: Vec::new(),
        };
        worker.input = Some(tokio::process::ChildStdin::from_std(
            worker
                .child
                .as_mut()
                .context("worker process missing")?
                .stdin
                .take()
                .context("worker stdin missing")?,
        )?);
        worker.output = Some(BufReader::new(tokio::process::ChildStdout::from_std(
            worker
                .child
                .as_mut()
                .context("worker process missing")?
                .stdout
                .take()
                .context("worker stdout missing")?,
        )?));
        Ok(worker)
    }

    async fn response(&mut self) -> Result<Response> {
        let mut line = Vec::new();
        let length = self
            .output
            .as_mut()
            .context("worker stdout unavailable")?
            .read_until(b'\n', &mut line)
            .await?;
        anyhow::ensure!(length != 0, "worker exited without a complete response");
        match mimir_json::from_slice(&line) {
            Ok(response) => Ok(response),
            Err(error) => {
                std::fs::write(self.directory.join("invalid-response.json"), line)?;
                Err(error.into())
            }
        }
    }

    async fn exchange(&mut self, request: &Request) -> Result<Vec<Vec<f32>>> {
        // Only these per-PID partial files belong to this worker. Complete
        // cached assets and other processes' downloads are never removed.
        let root = local_model_root(request.cache_dir.as_ref().map(std::path::Path::new))?;
        let model = root.join(HF_MODEL_ID.replace('/', "--"));
        self.partials = [model.join("tokenizer.json"), model.join("onnx/model.onnx")]
            .into_iter()
            .map(|path| path.with_extension(format!("part-{}", self.id())))
            .collect();
        let mut encoded = mimir_json::to_vec(request)?;
        encoded.push(b'\n');
        let input = self.input.as_mut().context("worker stdin unavailable")?;
        input.write_all(&encoded).await?;
        input.flush().await?;
        match self.response().await? {
            Response::Started { version: VERSION } => {}
            _ => anyhow::bail!("worker did not acknowledge protocol version {VERSION}"),
        }
        match self.response().await? {
            Response::Complete { vectors } => {
                anyhow::ensure!(
                    vectors.len() == request.texts.len(),
                    "worker returned the wrong number of embeddings"
                );
                anyhow::ensure!(
                    vectors
                        .iter()
                        .all(|row| row.len() == LOCAL_DIM
                            && row.iter().all(|value| value.is_finite())),
                    "worker returned an invalid local model vector"
                );
                Ok(vectors)
            }
            Response::Failed { message } => anyhow::bail!("{message}"),
            Response::Started { .. } => anyhow::bail!("worker sent a second start acknowledgement"),
        }
    }
}

impl Drop for Worker {
    fn drop(&mut self) {
        // Dropping an async inference future cannot detach model work. SIGKILL
        // stops even a blocked native model call; wait reaps this exact child.
        self.input.take();
        let Some(mut child) = self.child.take() else {
            return;
        };
        let _ = child.kill();
        if let Err(error) = child.wait() {
            tracing::error!(%error, pid = child.id(), diagnostics = %self.directory.display(), "could not reap local embedding worker");
            self.cleanup
                .retain(child, self.directory.clone(), self.partials.clone(), error);
            return;
        }
        remove_partials(&self.partials);
        if !self.preserve {
            let _ = std::fs::remove_dir_all(&self.directory);
        }
    }
}

/// Call before creating a Tokio runtime or reading application configuration.
/// Returns None for ordinary application invocations. This private stdio
/// protocol is used only between a process and its own embedding worker.
pub fn worker_entrypoint() -> Option<Result<()>> {
    let args: Vec<_> = std::env::args_os().skip(1).collect();
    if args.len() != 1 || args[0] != FLAG {
        return None;
    }
    Some(worker_main())
}

fn worker_main() -> Result<()> {
    let (sender, receiver) = std::sync::mpsc::channel();
    // The pipe also carries the owner's lifetime. EOF terminates inference
    // even if the parent disappeared during a blocking native call. There is
    // no heartbeat, polling interval or model-progress prerequisite.
    std::thread::spawn(move || {
        for line in std::io::stdin().lock().lines() {
            if sender.send(line).is_err() {
                return;
            }
        }
        std::process::exit(0);
    });
    let mut model: Option<LocalModel> = None;
    let mut selected: Option<Option<String>> = None;
    let mut output = std::io::stdout().lock();
    for line in receiver {
        let request: Request = mimir_json::from_str(&line?)?;
        anyhow::ensure!(
            request.version == VERSION,
            "unsupported worker protocol version"
        );
        serde_json::to_writer(&mut output, &Response::Started { version: VERSION })?;
        output.write_all(b"\n")?;
        output.flush()?;
        let result = (|| -> Result<Vec<Vec<f32>>> {
            if request.texts.is_empty() {
                return Ok(Vec::new());
            }
            let settings = request.cache_dir.clone();
            if selected.as_ref() != Some(&settings) {
                model = Some(LocalModel::new(request.cache_dir));
                selected = Some(settings);
            }
            let model = model.as_ref().context("worker model absent")?;
            let state = model.ensure_loaded()?;
            let (_owner, received) = tokio::sync::watch::channel(EmbeddingStatus::Running);
            embed_with_state(
                &state,
                &request.texts,
                &EmbeddingCancellation {
                    state: received,
                    cleanup: Arc::new(Cleanup::default()),
                },
            )
        })();
        let response = match result {
            Ok(vectors) => Response::Complete { vectors },
            Err(error) => Response::Failed {
                message: format!("{error:#}"),
            },
        };
        serde_json::to_writer(&mut output, &response)?;
        output.write_all(b"\n")?;
        output.flush()?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::fs::PermissionsExt;

    fn fixture(body: &str) -> (PathBuf, PathBuf) {
        let directory =
            std::env::temp_dir().join(format!("mimir-worker-test-{}", uuid::Uuid::new_v4()));
        std::fs::create_dir(&directory).unwrap();
        std::fs::set_permissions(&directory, std::fs::Permissions::from_mode(0o700)).unwrap();
        let program = directory.join("worker.py");
        std::fs::write(
            &program,
            format!("#!/usr/bin/env python3\nimport sys,json\n{body}\n"),
        )
        .unwrap();
        std::fs::set_permissions(&program, std::fs::Permissions::from_mode(0o700)).unwrap();
        (directory, program)
    }

    fn request(cache: &std::path::Path) -> Request {
        Request {
            version: VERSION,
            texts: vec!["whole input".into()],
            cache_dir: Some(cache.join("model-cache").display().to_string()),
        }
    }

    fn retain_missing_exit_receipt(worker: &mut Worker, partials: Vec<PathBuf>) -> u32 {
        unsafe extern "C" {
            fn waitpid(pid: i32, status: *mut i32, options: i32) -> i32;
        }
        let mut child = worker.child.take().unwrap();
        let pid = child.id();
        child.kill().unwrap();
        let mut status = 0;
        // Consume only this test's exact child exit outside Child::wait.
        // This reproduces an actual missing wait receipt without changing a
        // process-wide signal handler or signalling any unrelated process.
        assert_eq!(unsafe { waitpid(pid as i32, &mut status, 0) }, pid as i32);
        let error = child.wait().unwrap_err();
        worker
            .cleanup
            .retain(child, worker.directory.clone(), partials, error);
        pid
    }

    #[tokio::test]
    async fn stopped_native_work_is_killed_and_reaped() {
        let (directory, program) = fixture("json.loads(sys.stdin.readline())\nprint(json.dumps({'status':'started','version':2}),flush=True)\nwhile True: pass");
        let mut worker = Worker::spawn(program).unwrap();
        worker
            .input
            .as_mut()
            .unwrap()
            .write_all(b"{}\n")
            .await
            .unwrap();
        assert!(matches!(
            worker.response().await.unwrap(),
            Response::Started { version: VERSION }
        ));
        let pid = worker.id();
        let log_directory = worker.directory.clone();
        drop(worker);
        // wait() has reaped the child, so there is neither computation nor a
        // zombie. This assertion is Linux-specific; kill/wait itself is Unix.
        #[cfg(target_os = "linux")]
        assert!(!PathBuf::from(format!("/proc/{pid}")).exists());
        assert!(!log_directory.exists());
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[tokio::test]
    async fn a_missing_child_exit_receipt_remains_unconfirmed_and_keeps_diagnostics() {
        let (directory, program) = fixture("sys.stdin.read()");
        let mut worker = Worker::spawn(program).unwrap();
        let diagnostics = worker.directory.clone();
        let partial = diagnostics.join("owned.part");
        std::fs::write(&partial, b"incomplete model download").unwrap();
        let pid = retain_missing_exit_receipt(&mut worker, vec![partial.clone()]);
        let cleanup = worker.cleanup.clone();
        drop(worker);
        assert!(cleanup.pending());
        for _ in 0..2 {
            let issues = cleanup.retry();
            assert_eq!(issues.len(), 1);
            assert_eq!(issues[0].pid, pid);
            assert_eq!(issues[0].diagnostics, diagnostics);
            assert!(!issues[0].error.is_empty());
            assert!(partial.exists());
            assert!(diagnostics.join("stderr.log").exists());
        }
        // A different job's successful cleanup cannot clear this receipt.
        let healthy = Cleanup::default();
        assert!(healthy.retry().is_empty());
        assert!(cleanup.pending());
        drop(cleanup);
        std::fs::remove_dir_all(diagnostics).unwrap();
        std::fs::remove_dir_all(directory).unwrap();
    }

    struct MissingReceipt {
        program: PathBuf,
        ready: Mutex<Option<tokio::sync::oneshot::Sender<PathBuf>>>,
    }
    impl EmbeddingProvider for MissingReceipt {
        fn embed<'a>(
            &'a self,
            _texts: &'a [String],
            cancellation: EmbeddingCancellation,
        ) -> EmbedFuture<'a> {
            Box::pin(async move {
                let mut worker =
                    Worker::spawn_with_cleanup(self.program.clone(), cancellation.cleanup)?;
                retain_missing_exit_receipt(&mut worker, vec![]);
                self.ready
                    .lock()
                    .unwrap()
                    .take()
                    .unwrap()
                    .send(worker.directory.clone())
                    .unwrap();
                std::future::pending::<()>().await;
                Ok(vec![])
            })
        }
    }

    #[tokio::test]
    async fn cancelling_a_job_preserves_its_physical_cleanup_failure() {
        let (directory, program) = fixture("sys.stdin.read()");
        let (ready, mut received) = tokio::sync::oneshot::channel();
        let backend = OwnedEmbeddingBackend::for_test(Box::new(MissingReceipt {
            program,
            ready: Mutex::new(Some(ready)),
        }));
        let texts = vec!["input".into()];
        let mut job = Box::pin(backend.embed(&texts));
        let control = job.stop_handle();
        let diagnostics = tokio::select! {
            diagnostics = &mut received => diagnostics.unwrap(),
            result = &mut job => panic!("job returned before cancellation: {result:?}"),
        };
        assert!(control.cancel());
        let error = job.await.unwrap_err();
        assert!(!error.is::<EmbeddingCancelled>());
        assert!(error.to_string().contains("cleanup is unconfirmed"));
        assert!(error.to_string().contains(diagnostics.to_str().unwrap()));
        assert!(control.cleanup_pending());
        std::fs::remove_dir_all(diagnostics).unwrap();
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[tokio::test]
    async fn document_query_stop_kills_its_blocked_embedding() -> anyhow::Result<()> {
        use crate::{config::Config, test_isolation as isolation, MimirService};
        let cfg = Config {
            database: isolation::fixture().database_config(),
            embeddings: None,
            llm: None,
            judge: None,
            email: None,
            retirement: None,
        };
        let directory =
            PathBuf::from("/tmp").join(format!("mimir-read-stop-{}", uuid::Uuid::new_v4()));
        std::fs::create_dir(&directory)?;
        let socket = directory.join("ready.sock");
        let listener = tokio::net::UnixListener::bind(&socket)?;
        let (program_directory, program) = fixture(&format!("import socket,os\njson.loads(sys.stdin.readline())\nprint(json.dumps({{'status':'started','version':2}}),flush=True)\ns=socket.socket(socket.AF_UNIX)\ns.connect({:?})\ns.sendall((str(os.getpid())+'\\n').encode())\nwhile True: pass", socket.to_str().unwrap()));
        let service = Arc::new(
            MimirService::connect_with_embeddings(
                &cfg,
                Some(OwnedEmbeddingBackend {
                    provider: Box::new(LocalBackend::new(
                        Some(directory.join("cache").display().to_string()),
                        Some(program),
                    )),
                }),
            )
            .await?,
        );
        let reader = service.clone();
        let query = tokio::spawn(async move {
            reader
                .query_document("find relevant text", None, None)
                .await
        });
        let (stream, _) = listener.accept().await?;
        let mut pid = String::new();
        BufReader::new(stream).read_line(&mut pid).await?;
        query.abort();
        assert!(query.await.unwrap_err().is_cancelled());
        service.finish_operation_host().await?;
        #[cfg(target_os = "linux")]
        assert!(!PathBuf::from(format!("/proc/{}", pid.trim())).exists());
        std::fs::remove_dir_all(program_directory)?;
        std::fs::remove_dir_all(directory)?;
        Ok(())
    }

    #[tokio::test]
    async fn document_query_stop_retains_unconfirmed_worker_cleanup() -> anyhow::Result<()> {
        use crate::{config::Config, test_isolation as isolation, MimirService};
        let cfg = Config {
            database: isolation::fixture().database_config(),
            embeddings: None,
            llm: None,
            judge: None,
            email: None,
            retirement: None,
        };
        let (directory, program) = fixture("sys.stdin.read()");
        let (ready, received) = tokio::sync::oneshot::channel();
        let service = Arc::new(
            MimirService::connect_with_embeddings(
                &cfg,
                Some(OwnedEmbeddingBackend::for_test(Box::new(MissingReceipt {
                    program,
                    ready: Mutex::new(Some(ready)),
                }))),
            )
            .await?,
        );
        let reader = service.clone();
        let query = tokio::spawn(async move {
            reader
                .query_document("find relevant text", None, None)
                .await
        });
        let diagnostics = received.await?;
        query.abort();
        assert!(query.await.unwrap_err().is_cancelled());
        let error = service.finish_operation_host().await.unwrap_err();
        assert!(format!("{error:#}").contains(diagnostics.to_str().unwrap()));
        println!(
            "retained missing-receipt artifacts: {} {}",
            directory.display(),
            diagnostics.display()
        );
        Ok(())
    }

    #[tokio::test]
    async fn global_confirmation_keeps_missing_physical_receipts_pending() -> anyhow::Result<()> {
        use crate::{config::Config, db, test_isolation as isolation, MimirService};
        let cfg = Config {
            database: isolation::fixture().database_config(),
            embeddings: None,
            llm: None,
            judge: None,
            email: None,
            retirement: None,
        };
        let (directory, program) = fixture("sys.stdin.read()");
        let (ready, received) = tokio::sync::oneshot::channel();
        let service = Arc::new(
            MimirService::connect_with_embeddings(
                &cfg,
                Some(OwnedEmbeddingBackend::for_test(Box::new(MissingReceipt {
                    program,
                    ready: Mutex::new(Some(ready)),
                }))),
            )
            .await?,
        );
        let key: uuid::Uuid = db::connect(&cfg.database)
            .await?
            .query_one("SELECT gen_random_uuid()", &[])
            .await?
            .get(0);
        let token = service
            .reserve_operation(&key.to_string())
            .await?
            .operation_token;
        let source = service.clone();
        let job = tokio::spawn(async move {
            let texts = ["complete original content".to_owned()];
            source
                .own_operation(token, async {
                    source
                        .operation_embedding_job(
                            source.embeddings.as_ref().unwrap(),
                            &texts,
                            Some(token),
                        )
                        .await
                })
                .await
        });
        let diagnostics = received.await?;
        let cancellation = service.cancel_operation(token).await?;
        assert!(!cancellation.all_cleanup_confirmed());
        assert!(!cancellation.local_cleanup_confirmed());
        assert!(!cancellation.cleanup_issues().is_empty());
        let report = crate::operation_reporting::cancellation(token, cancellation)?;
        assert_eq!(report["worker_cleanup"], "unconfirmed_for_this_server");
        assert_eq!(report["next_action"], "open_user_dialog");
        assert_eq!(report["pending_executions"].as_array().unwrap().len(), 1);
        let error = job.await?.unwrap_err();
        assert!(format!("{error:#}").contains(diagnostics.to_str().unwrap()));
        let pending =
            crate::store::executions::pending(&db::connect(&cfg.database).await?, token).await?;
        assert_eq!(pending.len(), 1);
        assert!(pending[0].stopped_at.is_none());
        let healthy_key: uuid::Uuid = db::connect(&cfg.database)
            .await?
            .query_one("SELECT gen_random_uuid()", &[])
            .await?
            .get(0);
        let healthy = service
            .reserve_operation(&healthy_key.to_string())
            .await?
            .operation_token;
        service.own_operation(healthy, async { Ok(()) }).await?;
        assert!(
            service
                .cancel_operation(healthy)
                .await?
                .all_cleanup_confirmed(),
            "an unrelated owner's missing exit receipt must not block this action"
        );
        assert_eq!(
            crate::store::executions::pending(&db::connect(&cfg.database).await?, token)
                .await?
                .len(),
            1
        );
        println!(
            "retained missing-receipt artifacts: {} {}",
            directory.display(),
            diagnostics.display()
        );
        Ok(())
    }

    #[tokio::test]
    async fn cancelling_the_public_job_stops_its_blocking_worker() {
        let directory =
            PathBuf::from("/tmp").join(format!("mimir-owner-test-{}", uuid::Uuid::new_v4()));
        std::fs::create_dir(&directory).unwrap();
        std::fs::set_permissions(&directory, std::fs::Permissions::from_mode(0o700)).unwrap();
        let socket = directory.join("ready.sock");
        let listener = tokio::net::UnixListener::bind(&socket).unwrap();
        let (program_directory, program) = fixture(&format!("import socket,os\njson.loads(sys.stdin.readline())\nprint(json.dumps({{'status':'started','version':2}}),flush=True)\ns=socket.socket(socket.AF_UNIX)\ns.connect({:?})\ns.sendall((str(os.getpid())+'\\n').encode())\nwhile True: pass", socket.to_str().unwrap()));
        let backend = OwnedEmbeddingBackend {
            provider: Box::new(LocalBackend::new(
                Some(directory.join("model-cache").display().to_string()),
                Some(program),
            )),
        };
        let texts = vec!["input".into()];
        let mut job = Box::pin(backend.embed(&texts));
        let control = job.stop_handle();
        let (stream, _) = tokio::select! {
            connected = listener.accept() => connected.unwrap(),
            result = &mut job => panic!("worker should remain active: {result:?}"),
        };
        let mut pid = String::new();
        BufReader::new(stream).read_line(&mut pid).await.unwrap();
        assert!(control.cancel());
        assert!(job.await.unwrap_err().is::<EmbeddingCancelled>());
        assert!(control.confirm_cleanup().is_empty());
        assert!(!control.cleanup_pending());
        #[cfg(target_os = "linux")]
        assert!(!PathBuf::from(format!("/proc/{}", pid.trim())).exists());
        std::fs::remove_dir_all(program_directory).unwrap();
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[tokio::test]
    async fn exchange_preserves_whole_vectors_and_reuses_one_process() {
        let (directory, program) = fixture("for line in sys.stdin:\n request=json.loads(line)\n print(json.dumps({'status':'started','version':2}),flush=True)\n print(json.dumps({'status':'complete','vectors':[[0.125]*768 for text in request['texts']]}),flush=True)");
        let mut worker = Worker::spawn(program).unwrap();
        let pid = worker.id();
        let expected = vec![vec![0.125; LOCAL_DIM]];
        assert_eq!(
            worker.exchange(&request(&directory)).await.unwrap(),
            expected
        );
        assert_eq!(
            worker.exchange(&request(&directory)).await.unwrap(),
            expected
        );
        assert_eq!(worker.id(), pid);
        drop(worker);
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[tokio::test]
    async fn complete_collection_reaches_worker_once_without_a_batch_setting() {
        let (directory, program) = fixture("for line in sys.stdin:\n request=json.loads(line)\n assert sorted(request)==['cache_dir','texts','version']\n assert request['version']==2\n assert request['texts']==['input-'+str(i) for i in range(257)]\n print(json.dumps({'status':'started','version':2}),flush=True)\n print(json.dumps({'status':'complete','vectors':[[float(i)]*768 for i in range(len(request['texts']))]}),flush=True)");
        let backend = make_backend_with_worker(
            &EmbeddingsConfig {
                backend: EmbeddingBackend::Local,
                model: String::new(),
                api_key: None,
                cache_dir: Some(directory.join("model-cache").display().to_string()),
            },
            program,
        )
        .unwrap();
        let texts: Vec<String> = (0..257).map(|index| format!("input-{index}")).collect();
        let vectors = backend.embed(&texts).await.unwrap();
        assert_eq!(vectors.len(), texts.len());
        for (index, vector) in vectors.iter().enumerate() {
            assert_eq!(vector, &vec![index as f32; LOCAL_DIM]);
        }
        drop(backend);
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[tokio::test]
    async fn dropping_one_job_does_not_stop_another_worker() {
        let (directory, program) = fixture("json.loads(sys.stdin.readline())\nprint(json.dumps({'status':'started','version':2}),flush=True)\nwhile True: pass");
        let mut first = Worker::spawn(program.clone()).unwrap();
        let mut second = Worker::spawn(program).unwrap();
        first
            .input
            .as_mut()
            .unwrap()
            .write_all(b"{}\n")
            .await
            .unwrap();
        second
            .input
            .as_mut()
            .unwrap()
            .write_all(b"{}\n")
            .await
            .unwrap();
        assert!(matches!(
            first.response().await.unwrap(),
            Response::Started { .. }
        ));
        assert!(matches!(
            second.response().await.unwrap(),
            Response::Started { .. }
        ));
        drop(first);
        assert!(second.child.as_mut().unwrap().try_wait().unwrap().is_none());
        drop(second);
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[tokio::test]
    async fn provider_failure_keeps_complete_private_diagnostics() {
        let (directory, program) = fixture("json.loads(sys.stdin.readline())\nsys.stderr.write('whole diagnostic\\n'*10000)\nsys.stderr.flush()\nprint(json.dumps({'status':'started','version':2}),flush=True)\nprint(json.dumps({'status':'failed','message':'model rejected input'}),flush=True)\nsys.stdin.read()");
        let backend = LocalBackend::new(
            Some(directory.join("model-cache").display().to_string()),
            Some(program),
        );
        let (_sender, received) = tokio::sync::watch::channel(EmbeddingStatus::Running);
        let error = backend
            .embed(
                &["input".into()],
                EmbeddingCancellation {
                    state: received,
                    cleanup: Arc::new(Cleanup::default()),
                },
            )
            .await
            .unwrap_err();
        let message = error.to_string();
        assert!(format!("{error:#}").contains("model rejected input"));
        let log_directory = PathBuf::from(
            message
                .split("complete private diagnostics: ")
                .nth(1)
                .unwrap(),
        );
        assert_eq!(
            std::fs::read_to_string(log_directory.join("stderr.log")).unwrap(),
            "whole diagnostic\n".repeat(10000)
        );
        assert!(backend.idle.lock().unwrap().is_empty());
        std::fs::remove_dir_all(log_directory).unwrap();
        std::fs::remove_dir_all(directory).unwrap();
    }
}
