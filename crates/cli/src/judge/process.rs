//! Bounded, process-group-owned subprocess I/O for judge adapters.
use anyhow::{anyhow, ensure, Result};
use std::path::Path;
use std::process::Stdio;
use std::time::Duration;
use tokio::io::{AsyncRead, AsyncReadExt, AsyncWriteExt};
use tokio::process::{Child, Command};

const MAX_INPUT: usize = 2 * 1024 * 1024;
const MAX_OUTPUT: usize = 8 * 1024 * 1024;
const MAX_DIAGNOSTIC: usize = 64 * 1024;

pub struct Output {
    pub stdout: Vec<u8>,
}

struct GroupChild {
    child: Child,
    group: Option<i32>,
}
impl GroupChild {
    fn new(child: Child) -> Self {
        let group = child.id().map(|pid| pid as i32);
        Self { child, group }
    }
    fn kill_group(&self) {
        if let Some(pid) = self.group {
            let _ = unsafe { libc::kill(-pid, libc::SIGKILL) };
        }
    }
}
impl Drop for GroupChild {
    fn drop(&mut self) {
        if self.group.is_some() {
            self.kill_group();
            let _ = self.child.start_kill();
        }
    }
}

async fn read_limited<R: AsyncRead + Unpin>(mut reader: R, max: usize) -> Result<Vec<u8>> {
    let mut bytes = Vec::new();
    let mut chunk = [0u8; 8192];
    loop {
        let n = reader.read(&mut chunk).await?;
        if n == 0 {
            break;
        }
        ensure!(bytes.len() + n <= max, "harness output exceeded limit");
        bytes.extend_from_slice(&chunk[..n]);
    }
    Ok(bytes)
}

pub async fn run(
    program: &str,
    args: &[String],
    cwd: &Path,
    input: &[u8],
    timeout: Duration,
) -> Result<Output> {
    ensure!(input.len() <= MAX_INPUT, "harness input exceeded limit");
    let mut command = Command::new(program);
    command
        .args(args)
        .current_dir(cwd)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .kill_on_drop(true);
    unsafe {
        command.pre_exec(|| {
            if libc::setpgid(0, 0) == -1 {
                return Err(std::io::Error::last_os_error());
            }
            Ok(())
        });
    }
    let mut child = GroupChild::new(
        command
            .spawn()
            .map_err(|_| anyhow!("unable to start harness"))?,
    );
    let mut stdin = child
        .child
        .stdin
        .take()
        .ok_or_else(|| anyhow!("harness stdin unavailable"))?;
    let stdout = child
        .child
        .stdout
        .take()
        .ok_or_else(|| anyhow!("harness stdout unavailable"))?;
    let stderr = child
        .child
        .stderr
        .take()
        .ok_or_else(|| anyhow!("harness stderr unavailable"))?;
    let outcome = tokio::time::timeout(timeout, async {
        let write = async move {
            stdin.write_all(input).await?;
            stdin.shutdown().await?;
            drop(stdin);
            Ok::<_, std::io::Error>(())
        };
        let ((), stdout, _stderr) = tokio::try_join!(
            async { write.await.map_err(anyhow::Error::from) },
            read_limited(stdout, MAX_OUTPUT),
            read_limited(stderr, MAX_DIAGNOSTIC),
        )?;
        // Kill any descendants while the child PID is still reserved, then reap.
        child.kill_group();
        let exit = child.child.wait().await?;
        child.group = None;
        ensure!(exit.success(), "harness exited unsuccessfully");
        Ok::<_, anyhow::Error>(Output { stdout })
    })
    .await;
    if child.group.is_some() {
        child.kill_group();
        let reaped = matches!(
            tokio::time::timeout(Duration::from_secs(1), child.child.wait()).await,
            Ok(Ok(_))
        );
        // Once reaped, never signal a potentially reused process-group ID.
        if reaped {
            child.group = None;
        }
    }
    match outcome {
        Ok(Ok(output)) => Ok(output),
        Ok(Err(_)) => Err(anyhow!("harness I/O or exit failure")),
        Err(_) => Err(anyhow!("harness timed out")),
    }
}
