//! Actual CLI signals while a model request is active; no external model or DB.
use std::{
    fs,
    os::unix::fs::PermissionsExt,
    process::{Child, Command, Stdio},
    thread,
    time::{Duration, Instant},
};
use uuid::Uuid;
struct Owned(Child);
impl Drop for Owned {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}
fn alive(pid: u32) -> bool {
    fs::read_to_string(format!("/proc/{pid}/stat"))
        .is_ok_and(|s| s.split_whitespace().nth(2) != Some("Z"))
}
#[test]
fn stop_signals_cancel_active_run_and_watch_and_owned_children() {
    for mode in ["run", "watch"] {
        for signal in [libc::SIGINT, libc::SIGTERM] {
            let dir = std::env::temp_dir().join(format!("mimir-signal-{}", Uuid::new_v4()));
            fs::create_dir(&dir).unwrap();
            fs::set_permissions(&dir, fs::Permissions::from_mode(0o700)).unwrap();
            let model = dir.join("model.sh");
            fs::write(&model, format!("#!/usr/bin/env bash\ncat >/dev/null\nsleep 600 & descendant=$!\nprintf '%s\\n' \"$$\" \"$descendant\" > '{}'\nwait\n", dir.join("model-pids").display())).unwrap();
            fs::set_permissions(&model, fs::Permissions::from_mode(0o700)).unwrap();
            let fixture =
                std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/judge/retry_fixture.sh");
            let cfg = dir.join("config.toml");
            fs::write(&cfg, format!("config_version=1\n[logging]\ndirectory='{}'\n[database]\nhost='localhost'\nport=5432\ndbname='unused'\nuser='unused'\n[judge]\nproject='judge-retry-fixture'\nmcp_command='bash'\nmcp_args=['{}','{}','{}','normal','{}','{}']\n[llm]\nbackend='command'\nmodel='fixture'\ncommand='{}'\nargs=[]\n", dir.join("logs").display(), fixture.display(), Uuid::new_v4(), dir.join("reviews").display(), dir.join("requests").display(), dir.join("mcp-pids").display(), model.display())).unwrap();
            fs::set_permissions(&cfg, fs::Permissions::from_mode(0o600)).unwrap();
            let mut child = Owned(
                Command::new(env!("CARGO_BIN_EXE_mimir"))
                    .args(["judge", mode, "--config"])
                    .arg(&cfg)
                    .arg("--state-dir")
                    .arg(dir.join("state"))
                    .stdout(Stdio::from(fs::File::create(dir.join("stdout")).unwrap()))
                    .stderr(Stdio::from(fs::File::create(dir.join("stderr")).unwrap()))
                    .spawn()
                    .unwrap(),
            );
            let deadline = Instant::now() + Duration::from_secs(10);
            while !dir.join("model-pids").exists() {
                assert!(
                    child.0.try_wait().unwrap().is_none(),
                    "CLI exited: {}",
                    fs::read_to_string(dir.join("stderr")).unwrap()
                );
                assert!(
                    Instant::now() < deadline,
                    "fixture model did not start: {}",
                    fs::read_to_string(dir.join("stderr")).unwrap()
                );
                thread::sleep(Duration::from_millis(10));
            }
            assert_eq!(unsafe { libc::kill(child.0.id() as i32, signal) }, 0);
            let status = loop {
                if let Some(status) = child.0.try_wait().unwrap() {
                    break status;
                }
                assert!(
                    Instant::now() < deadline,
                    "stop did not interrupt active {mode}"
                );
                thread::sleep(Duration::from_millis(10));
            };
            assert!(status.success());
            for file in ["model-pids", "mcp-pids"] {
                for pid in fs::read_to_string(dir.join(file))
                    .unwrap()
                    .lines()
                    .map(|s| s.parse::<u32>().unwrap())
                {
                    while alive(pid) && Instant::now() < deadline {
                        thread::sleep(Duration::from_millis(10));
                    }
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
