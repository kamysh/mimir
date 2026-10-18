//! Bounded, process-group-owned subprocess I/O for judge adapters.
use super::state::SourceFailure;
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

async fn read_limited<R: AsyncRead + Unpin>(
    mut reader: R,
    max: usize,
    stream: &str,
) -> Result<Vec<u8>> {
    let mut bytes = Vec::new();
    let mut chunk = [0u8; 8192];
    loop {
        let n = reader.read(&mut chunk).await?;
        if n == 0 {
            break;
        }
        if bytes.len() + n > max {
            // Include the triggering read in the observed lower bound. Storage
            // remains bounded by the stream limit plus one fixed-size chunk;
            // SourceFailure retains only a private, bounded prefix.
            bytes.extend_from_slice(&chunk[..n]);
            return Err(SourceFailure::input(
                &format!("harness {stream} output"),
                &bytes,
                &format!(
                    "output exceeded limit of {max} bytes (observed at least {} bytes)",
                    bytes.len()
                ),
            )
            .into());
        }
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
            .map_err(|error| anyhow!("unable to start harness: {error}"))?,
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
        let ((), stdout, stderr) = tokio::try_join!(
            async { write.await.map_err(anyhow::Error::from) },
            read_limited(stdout, MAX_OUTPUT, "stdout"),
            read_limited(stderr, MAX_DIAGNOSTIC, "stderr"),
        )?;
        // Kill any descendants while the child PID is still reserved, then reap.
        child.kill_group();
        let exit = child.child.wait().await?;
        child.group = None;
        if !exit.success() {
            let detail = super::state::bounded(&String::from_utf8_lossy(&stderr), 512);
            return Err(anyhow!("harness exited with {exit}: {detail}"));
        }
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
        Ok(Err(error)) => Err(error),
        Err(_) => Err(anyhow!("harness timed out")),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::judge::state::Report;

    #[tokio::test]
    async fn output_limits_accept_the_boundary_and_preserve_overflow_evidence() {
        for (stream, limit) in [("stdout", MAX_OUTPUT), ("stderr", MAX_DIAGNOSTIC)] {
            let input = vec![b'x'; limit];
            assert_eq!(
                read_limited(input.as_slice(), limit, stream).await.unwrap(),
                input
            );

            let mut input = input;
            input.push(b'y');
            let error = read_limited(input.as_slice(), limit, stream)
                .await
                .unwrap_err();
            let source = error.downcast_ref::<SourceFailure>().unwrap();
            assert_eq!(source.stage, format!("harness {stream} output"));
            assert_eq!(source.total_bytes, limit + 1);
            assert!(source.detail.contains(&format!("limit of {limit} bytes")));
            assert!(source
                .detail
                .contains(&format!("at least {} bytes", limit + 1)));
            assert_eq!(source.excerpt_start, 0);
            assert_eq!(source.excerpt, "x".repeat(32 * 1024));
            assert!(!error.to_string().contains(&"x".repeat(100)));

            let mut report = Report::new("blocked", 1, 0, 0, 1, 0);
            report.capture_source(&error);
            assert_eq!(report.failure_source.unwrap().total_bytes, limit + 1);
        }
    }
}
