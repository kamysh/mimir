//! Actual CLI signals with fake model/MCP processes and an isolated DB subscription.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;
use std::{fs, os::unix::fs::PermissionsExt, process::Stdio};
use tokio::{
    io::{AsyncBufReadExt, AsyncReadExt, BufReader},
    net::TcpListener,
    process::{Child, Command},
};
use uuid::Uuid;
struct Owned(Child);
impl Drop for Owned {
    fn drop(&mut self) {
        let _ = self.0.start_kill();
    }
}
fn alive(pid: u32) -> bool {
    fs::read_to_string(format!("/proc/{pid}/stat"))
        .is_ok_and(|s| s.split_whitespace().nth(2) != Some("Z"))
}
#[tokio::test]
async fn stop_signals_cancel_active_run_and_watch_and_owned_children() {
    // Watch subscribes before starting MCP. Reject missing or conflicting test
    // settings before spawning a process, rather than guessing a local DB.
    let database = toml::to_string(&isolation::fixture().database_config()).unwrap();
    for mode in ["run", "watch"] {
        for signal in [libc::SIGINT, libc::SIGTERM] {
            let dir = std::env::temp_dir().join(format!("mimir-signal-{}", Uuid::new_v4()));
            fs::create_dir(&dir).unwrap();
            fs::set_permissions(&dir, fs::Permissions::from_mode(0o700)).unwrap();
            let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
            let address = listener.local_addr().unwrap();
            let model = dir.join("model.sh");
            // The shell and its child keep the event connection open. EOF
            // observes descriptor cleanup after cancellation. The FIFO child
            // has no elapsed-time completion path.
            fs::write(&model, format!("#!/usr/bin/env bash\nset -euo pipefail\ncat >/dev/null\nexec 9<>/dev/tcp/127.0.0.1/{}\nmkfifo '{}.wait'\ncat '{}.wait' >/dev/null & descendant=$!\nprintf '%s\\n' \"$$\" \"$descendant\" > '{}'\nprintf 'model %s %s\\n' \"$$\" \"$descendant\" >&9\nwait\n", address.port(), dir.join("model-pids").display(), dir.join("model-pids").display(), dir.join("model-pids").display())).unwrap();
            fs::set_permissions(&model, fs::Permissions::from_mode(0o700)).unwrap();
            let fixture =
                std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/judge/retry_fixture.sh");
            let cfg = dir.join("config.toml");
            fs::write(&cfg, format!("config_version=1\n[logging]\ndirectory='{}'\n[database]\n{database}\n[judge]\nproject='judge-retry-fixture'\nmcp_command='bash'\nmcp_args=['{}','{}','{}','normal','{}','{}']\n[llm]\nbackend='command'\nmodel='fixture'\ncommand='{}'\nargs=[]\n", dir.join("logs").display(), fixture.display(), Uuid::new_v4(), dir.join("reviews").display(), dir.join("requests").display(), dir.join("mcp-pids").display(), model.display())).unwrap();
            fs::set_permissions(&cfg, fs::Permissions::from_mode(0o600)).unwrap();
            let mut child = Owned(
                Command::new(env!("CARGO_BIN_EXE_mimir"))
                    .args(["judge", mode, "--config"])
                    .arg(&cfg)
                    .arg("--state-dir")
                    .arg(dir.join("state"))
                    .env("MIMIR_JUDGE_FIXTURE_EVENTS", address.to_string())
                    .stdout(Stdio::from(fs::File::create(dir.join("stdout")).unwrap()))
                    .stderr(Stdio::from(fs::File::create(dir.join("stderr")).unwrap()))
                    .kill_on_drop(true)
                    .spawn()
                    .unwrap(),
            );
            let mut owners = std::collections::BTreeSet::new();
            let mut connections = Vec::new();
            while owners.len() != 2 {
                let (stream, _) = tokio::select! {
                    accepted = listener.accept() => accepted.unwrap(),
                    status = child.0.wait() => panic!("CLI exited before fixture readiness: {status:?}: {}", fs::read_to_string(dir.join("stderr")).unwrap()),
                };
                let mut reader = BufReader::new(stream);
                let mut event = String::new();
                let received = tokio::select! {
                    received = reader.read_line(&mut event) => received.unwrap(),
                    status = child.0.wait() => panic!("CLI exited before readiness message: {status:?}: {}", fs::read_to_string(dir.join("stderr")).unwrap()),
                };
                assert!(received > 0, "fixture closed before announcing readiness");
                let fields: Vec<_> = event.split_whitespace().collect();
                assert_eq!(fields.len(), 3, "unexpected event: {event}");
                assert!(matches!(fields[0], "model" | "mcp"), "{event}");
                assert!(
                    owners.insert(fields[0].to_owned()),
                    "duplicate owner: {event}"
                );
                let pids: Vec<u32> = fields[1..].iter().map(|pid| pid.parse().unwrap()).collect();
                assert!(
                    pids.iter().all(|pid| alive(*pid)),
                    "owner was not active: {event}"
                );
                connections.push((reader, pids));
            }
            let pid = child.0.id().unwrap();
            assert_eq!(unsafe { libc::kill(pid as i32, signal) }, 0);
            let status = child.0.wait().await.unwrap();
            assert!(status.success());
            for (mut reader, pids) in connections {
                let mut remaining = Vec::new();
                reader.read_to_end(&mut remaining).await.unwrap();
                assert!(remaining.is_empty(), "unexpected event after readiness");
                for pid in pids {
                    assert!(
                        !alive(pid),
                        "owned child {pid} survived {mode} cancellation"
                    );
                }
            }
            fs::remove_dir_all(dir).unwrap();
        }
    }
}
