//! Real process checks with disposable configuration, never the live database.
use std::ffi::{OsStr, OsString};
use std::io::Write;
use std::net::TcpListener;
use std::path::PathBuf;
use std::process::{Command, Output, Stdio};
use std::time::{Duration, Instant};

struct Fixture(PathBuf);

impl Fixture {
    fn new() -> Self {
        let path =
            PathBuf::from("/var/tmp").join(format!("mimir-startup-{}", uuid::Uuid::new_v4()));
        std::fs::create_dir(&path).unwrap();
        Self(path)
    }

    fn config(&self) -> PathBuf {
        self.0.join("config.toml")
    }

    fn run(&self, args: &[OsString]) -> Output {
        let mut child = Command::new(env!("CARGO_BIN_EXE_mimir-mcp"))
            .args(args)
            .env("MIMIR_CONFIG", self.config())
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        let deadline = Instant::now() + Duration::from_secs(5);
        while child.try_wait().unwrap().is_none() {
            if Instant::now() >= deadline {
                child.kill().unwrap();
                let output = child.wait_with_output().unwrap();
                panic!("startup did not exit promptly for {args:?}: {output:?}");
            }
            std::thread::sleep(Duration::from_millis(10));
        }
        child.wait_with_output().unwrap()
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        std::fs::remove_dir_all(&self.0).unwrap();
    }
}

fn cases() -> Vec<(Vec<OsString>, i32)> {
    let mut cases = vec![];
    for flag in ["--help", "-h", "--version", "-V"] {
        cases.push((vec![flag.into()], 0));
    }
    for args in [
        vec!["--unknown"],
        vec!["unexpected"],
        vec!["--"],
        vec!["--help=anything"],
        vec!["--help", "unexpected"],
        vec!["unexpected", "--version"],
        vec!["--unknown", "--help"],
        vec!["--version", "--help"],
        vec!["--version", "--version"],
        vec![""],
    ] {
        cases.push((args.into_iter().map(OsString::from).collect(), 2));
    }
    #[cfg(unix)]
    {
        use std::os::unix::ffi::OsStringExt;
        cases.push((vec![OsString::from_vec(vec![0xff])], 2));
    }
    cases
}

fn assert_arguments(fixture: &Fixture) {
    for (args, expected) in cases() {
        let output = fixture.run(&args);
        assert_eq!(output.status.code(), Some(expected), "{args:?}: {output:?}");
        if expected == 0 {
            assert!(output.stderr.is_empty(), "{args:?}: {output:?}");
            let stdout = String::from_utf8(output.stdout).unwrap();
            if args[0] == OsStr::new("--version") || args[0] == OsStr::new("-V") {
                assert_eq!(
                    stdout.trim(),
                    concat!("mimir-mcp ", env!("CARGO_PKG_VERSION"))
                );
            } else {
                assert!(stdout.contains("Usage: mimir-mcp"), "{stdout}");
                assert!(stdout.contains("--help") && stdout.contains("--version"));
            }
        } else {
            assert!(output.stdout.is_empty(), "{args:?}: {output:?}");
            let stderr = String::from_utf8(output.stderr).unwrap();
            assert!(stderr.contains("Usage: mimir-mcp"), "{stderr}");
        }
    }
}

#[test]
fn arguments_exit_before_missing_or_malformed_configuration() {
    let fixture = Fixture::new();
    assert_arguments(&fixture);
    std::fs::write(fixture.config(), "this is deliberately invalid TOML = [").unwrap();
    assert_arguments(&fixture);
    // No arguments must still enter normal startup and report configuration errors.
    let output = fixture.run(&[]);
    assert_eq!(output.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&output.stderr).contains("error:"));
}

#[test]
fn arguments_never_connect_even_with_valid_database_configuration() {
    let fixture = Fixture::new();
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    listener.set_nonblocking(true).unwrap();
    let mut config = std::fs::File::create(fixture.config()).unwrap();
    writeln!(
        config,
        "[database]\nhost = '127.0.0.1'\nport = {}\nuser = 'unused'\ndbname = 'unused'\nssl_mode = 'disable'",
        listener.local_addr().unwrap().port()
    )
    .unwrap();
    assert_arguments(&fixture);
    assert_eq!(
        listener.accept().unwrap_err().kind(),
        std::io::ErrorKind::WouldBlock
    );
}
