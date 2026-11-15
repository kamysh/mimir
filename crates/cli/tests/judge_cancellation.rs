//! Actual CLI signals while a model request is active; no external model or DB.
use std::{
    fs,
    os::unix::fs::PermissionsExt,
    process::{Child, Command, Stdio},
};
use uuid::Uuid;
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;
struct Owned(Child);
impl Drop for Owned {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

/// Process/file events instead of polling (issue #469 items 256/356/359/362/377).
#[cfg(target_os = "linux")]
fn wait_for_file(path: &std::path::Path) {
    use std::os::unix::ffi::OsStrExt;
    let dir = path.parent().unwrap();
    let name = path.file_name().unwrap().as_bytes();
    unsafe {
        let ifd = libc::inotify_init1(libc::IN_CLOEXEC);
        assert!(ifd >= 0, "inotify_init failed");
        let c_dir = std::ffi::CString::new(dir.as_os_str().as_bytes()).unwrap();
        let wd = libc::inotify_add_watch(ifd, c_dir.as_ptr(), libc::IN_CREATE | libc::IN_MOVED_TO);
        assert!(
            wd >= 0,
            "inotify_add_watch failed: {:?}",
            std::io::Error::last_os_error()
        );
        if path.exists() {
            libc::close(ifd);
            return;
        }
        let mut buf = [0u8; 4096];
        loop {
            let n = libc::read(ifd, buf.as_mut_ptr() as *mut libc::c_void, buf.len());
            assert!(n > 0, "inotify read failed");
            let mut off = 0usize;
            while off + 16 <= n as usize {
                let ev = &*(buf.as_ptr().add(off) as *const libc::inotify_event);
                let len = ev.len as usize;
                if len > 0 && off + 16 + len <= n as usize {
                    let raw = std::slice::from_raw_parts(buf.as_ptr().add(off + 16), len);
                    let end = raw.iter().position(|&b| b == 0).unwrap_or(len);
                    if &raw[..end] == name {
                        libc::close(ifd);
                        return;
                    }
                }
                off += 16 + len;
            }
        }
    }
}

#[cfg(target_os = "linux")]
fn wait_for_exit(pid: u32) {
    unsafe {
        let fd = libc::syscall(libc::SYS_pidfd_open, pid as libc::c_int, 0) as libc::c_int;
        if fd < 0 {
            assert_eq!(
                *libc::__errno_location(),
                libc::ESRCH,
                "pidfd_open({pid}) failed"
            );
            return;
        }
        let mut pollfd = libc::pollfd {
            fd,
            events: libc::POLLIN,
            revents: 0,
        };
        assert_eq!(
            libc::poll(&mut pollfd, 1, -1),
            1,
            "pidfd poll failed for {pid}"
        );
        libc::close(fd);
    }
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
            if mode == "watch" {
                // Watch owns a real LISTEN connection even when its MCP/model
                // adapters are fixtures. Use only the guarded disposable DB.
                let database = isolation::fixture().database_config();
                let mut config: toml::Table =
                    toml::from_str(&fs::read_to_string(&cfg).unwrap()).unwrap();
                config.insert("database".into(), toml::Value::try_from(database).unwrap());
                fs::write(&cfg, toml::to_string(&config).unwrap()).unwrap();
            }
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
            wait_for_file(&dir.join("model-pids"));
            assert_eq!(unsafe { libc::kill(child.0.id() as i32, signal) }, 0);
            let status = child.0.wait().unwrap();
            assert!(status.success());
            for file in ["model-pids", "mcp-pids"] {
                for pid in fs::read_to_string(dir.join(file))
                    .unwrap()
                    .lines()
                    .map(|s| s.parse::<u32>().unwrap())
                {
                    wait_for_exit(pid);
                }
            }
            fs::remove_dir_all(dir).unwrap();
        }
    }
}
