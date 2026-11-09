//! Complete model I/O and diagnostics, with owned subprocess cleanup.
use anyhow::{anyhow, Result};
use std::path::Path;
use std::process::{ExitStatus, Stdio};
use tokio::io::{AsyncRead, AsyncReadExt, AsyncWriteExt};
use tokio::process::{Child, Command};

pub struct Output {
    pub stdout: Vec<u8>,
}

#[derive(Debug)]
pub struct HarnessExitFailure {
    pub status: ExitStatus,
    pub stderr: Vec<u8>,
}

impl std::fmt::Display for HarnessExitFailure {
    fn fmt(&self, output: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            output,
            "harness exited with {}: {}",
            self.status,
            String::from_utf8_lossy(&self.stderr)
        )
    }
}

impl std::error::Error for HarnessExitFailure {}

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
            read_complete(stderr),
        )?;
        // Kill any descendants while the child PID is still reserved, then reap.
        child.kill_group();
        let exit = child.child.wait().await?;
        child.group = None;
        if !exit.success() {
            return Err(HarnessExitFailure {
                status: exit,
                stderr,
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
    async fn both_streams_are_read_completely() {
        let input = vec![b'x'; 8 * 1024 * 1024 + 1];
        assert_eq!(read_complete(input.as_slice()).await.unwrap(), input);
        let expected = input.clone();
        let (mut writer, reader) = tokio::io::duplex(8192);
        let writer = tokio::spawn(async move {
            writer.write_all(&input).await.unwrap();
            writer.shutdown().await.unwrap();
        });
        assert_eq!(read_complete(reader).await.unwrap(), expected);
        writer.await.unwrap();
    }

    #[tokio::test]
    async fn failed_harness_preserves_the_whole_multibyte_explanation() {
        let explanation = format!(
            "first line\n{}\nlast line: actual failure\n",
            "λ".repeat(64 * 1024 + 1)
        );
        let mut bytes = explanation.as_bytes().to_vec();
        bytes.push(0xff);
        let work = std::env::current_dir().unwrap();
        let error = run(
            "sh",
            &["-c".into(), "cat >&2; exit 7".into()],
            &work,
            &bytes,
        )
        .await
        .err()
        .expect("the harness must report its unsuccessful exit");
        let detail = error.to_string();
        assert!(detail.contains("7"));
        assert!(
            detail.ends_with(String::from_utf8_lossy(&bytes).as_ref()),
            "the full stderr must survive the error boundary"
        );
        assert_eq!(
            error.downcast_ref::<HarnessExitFailure>().unwrap().stderr,
            bytes,
            "the returned error must retain even bytes that cannot be displayed as UTF-8"
        );
    }
}
