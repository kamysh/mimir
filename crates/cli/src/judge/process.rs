//! Complete model I/O, bounded diagnostics, and owned subprocess cleanup.
use anyhow::{anyhow, Result};
use std::path::Path;
use std::process::Stdio;
use tokio::io::{AsyncRead, AsyncReadExt, AsyncWriteExt};
use tokio::process::{Child, Command};

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

async fn read_complete<R: AsyncRead + Unpin>(mut reader: R) -> Result<Vec<u8>> {
    let mut bytes = Vec::new();
    reader.read_to_end(&mut bytes).await?;
    Ok(bytes)
}

// Retention never stops draining the pipe or fails the model operation.
async fn read_diagnostic<R: AsyncRead + Unpin>(mut reader: R) -> Result<Vec<u8>> {
    let mut bytes = Vec::new();
    let mut chunk = [0u8; 8192];
    loop {
        let n = reader.read(&mut chunk).await?;
        if n == 0 {
            break;
        }
        bytes.extend_from_slice(&chunk[..n]);
    }
    Ok(bytes)
}

/// A nonzero harness exit carrying both captured streams: `output` (stdout,
/// where result envelopes land) for classification and `diagnostic` (stderr)
/// for the human-readable failure text.
#[derive(Debug)]
pub struct HarnessExit {
    pub code: Option<i32>,
    pub output: String,
    pub diagnostic: String,
}
impl std::fmt::Display for HarnessExit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Enough to include a provider error envelope's classification
        // fields (api_error, api_error_status, result).
        let diagnostic: String = self.diagnostic.chars().take(4000).collect();
        let output: String = self.output.chars().take(4000).collect();
        write!(
            f,
            "harness exited with status {:?}: {diagnostic} {output}",
            self.code
        )
    }
}
impl std::error::Error for HarnessExit {}

pub async fn run(program: &str, args: &[String], cwd: &Path, input: &[u8]) -> Result<Output> {
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
    let outcome = async {
        let write = async move {
            stdin.write_all(input).await?;
            stdin.shutdown().await?;
            drop(stdin);
            Ok::<_, std::io::Error>(())
        };
        let ((), stdout, stderr) = tokio::try_join!(
            async { write.await.map_err(anyhow::Error::from) },
            read_complete(stdout),
            read_diagnostic(stderr),
        )?;
        // Kill any descendants while the child PID is still reserved, then reap.
        child.kill_group();
        let exit = child.child.wait().await?;
        child.group = None;
        if !exit.success() {
            let diagnostic: String = String::from_utf8_lossy(&stderr)
                .trim()
                .chars()
                .take(65536)
                .collect();
            let output: String = String::from_utf8_lossy(&stdout)
                .trim()
                .chars()
                .take(65536)
                .collect();
            return Err(HarnessExit {
                code: exit.code(),
                output,
                diagnostic,
            }
            .into());
        }
        Ok::<_, anyhow::Error>(Output { stdout })
    }
    .await;
    if child.group.is_some() {
        child.kill_group();
        let reaped = child.child.wait().await.is_ok();
        // Once reaped, never signal a potentially reused process-group ID.
        if reaped {
            child.group = None;
        }
    }
    outcome
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn stdout_and_stderr_are_both_retained_completely() {
        let input = vec![b'x'; 8 * 1024 * 1024 + 1];
        assert_eq!(read_complete(input.as_slice()).await.unwrap(), input);
        let (mut writer, reader) = tokio::io::duplex(8192);
        let writer = tokio::spawn(async move {
            writer.write_all(&input).await.unwrap();
            writer.shutdown().await.unwrap();
        });
        assert_eq!(
            read_diagnostic(reader).await.unwrap(),
            vec![b'x'; 8 * 1024 * 1024 + 1]
        );
        writer.await.unwrap();
    }
}
