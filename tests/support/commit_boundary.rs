//! Control an actual registered publication in an explicitly instrumented
//! test child. The caller retains its stdout/stderr and owns the child.
use anyhow::{ensure, Result};
use mimir_core::operation_catalogue::{CommitSite, Operation};
use std::{os::unix::fs::DirBuilderExt, path::PathBuf};
use tokio::{
    io::{AsyncBufReadExt, BufReader},
    net::{UnixListener, UnixStream},
    process::{Child, Command},
};
use uuid::Uuid;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Phase {
    BeforeCommit,
    AfterCommit,
}
impl Phase {
    pub fn name(self) -> &'static str {
        match self {
            Self::BeforeCommit => "before_commit",
            Self::AfterCommit => "after_commit",
        }
    }
}

pub struct Controller {
    listener: UnixListener,
    socket: PathBuf,
    token: Uuid,
    operation: Operation,
    site: CommitSite,
    step: String,
    phase: Phase,
}
pub struct Paused {
    // Keep the controller connection open until the exact child is reaped.
    _transport: BufReader<UnixStream>,
    event: mimir_json::Document,
}
impl Controller {
    pub fn new(
        token: Uuid,
        operation: Operation,
        site: CommitSite,
        step: String,
        phase: Phase,
    ) -> Result<Self> {
        ensure!(
            operation
                .committed_boundaries()
                .iter()
                .any(|entry| entry.site == site),
            "the selected publication site is not registered for this operation"
        );
        let name = mimir_json::parse(&step)?;
        ensure!(
            name.as_array().is_some_and(|parts| parts.len() == 2)
                && name[0] == site.name()
                && (name[1].is_null() || name[1].is_string()),
            "select the exact saved-step name from the operation plan"
        );
        // Unix socket paths have an OS-defined size. Do not place the socket
        // inside a potentially long disposable database fixture path.
        let directory = std::env::temp_dir().join(format!("mimir-boundary-{token}"));
        std::fs::DirBuilder::new().mode(0o700).create(&directory)?;
        let socket = directory.join("control.sock");
        Ok(Self {
            listener: UnixListener::bind(&socket)?,
            socket,
            token,
            operation,
            site,
            step,
            phase,
        })
    }
    pub fn configure(&self, command: &mut Command) {
        command
            .env("MIMIR_TEST_BOUNDARY_SOCKET", &self.socket)
            .env("MIMIR_TEST_BOUNDARY_TOKEN", self.token.to_string())
            .env("MIMIR_TEST_BOUNDARY_SITE", self.site.name())
            .env("MIMIR_TEST_BOUNDARY_STEP", &self.step)
            .env("MIMIR_TEST_BOUNDARY_PHASE", self.phase.name());
    }
    pub async fn reached(&self) -> Result<Paused> {
        let (stream, _) = self.listener.accept().await?;
        let mut transport = BufReader::new(stream);
        let mut line = String::new();
        ensure!(
            transport.read_line(&mut line).await? != 0,
            "child closed before its checkpoint event"
        );
        let event = mimir_json::parse(&line)?;
        let expected = serde_json::json!({"operation_token":self.token,"operation":self.operation.name(),
            "site":self.site.name(),"step":self.step,"phase":self.phase.name()});
        ensure!(
            *event == expected,
            "child reached a different publication: {event}"
        );
        Ok(Paused {
            _transport: transport,
            event,
        })
    }
}
impl Paused {
    pub async fn terminate(self, child: &mut Child) -> Result<mimir_json::Document> {
        child.kill().await?;
        ensure!(
            !child.wait().await?.success(),
            "the child completed before interruption"
        );
        Ok(self.event)
    }
}
