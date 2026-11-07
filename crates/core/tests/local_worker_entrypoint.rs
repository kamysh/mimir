#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;

use std::io::{BufRead, BufReader, Write};
use std::process::{Command, Stdio};

#[test]
fn both_binaries_serve_private_embedding_protocol_without_loading_configuration() {
    let fixture = isolation::fixture();
    for binary in [&fixture.mimir, &fixture.mcp] {
        let stderr_path = fixture
            .root
            .join(format!("worker-entrypoint-{}.stderr", uuid::Uuid::new_v4()));
        let stderr = std::fs::File::create(&stderr_path).unwrap();
        let mut child = Command::new(binary)
            .arg("--embedding-worker")
            .env(
                "MIMIR_CONFIG",
                fixture.root.join("must-not-load-this-config.toml"),
            )
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(stderr)
            .spawn()
            .unwrap();
        let mut input = child.stdin.take().unwrap();
        let mut output = BufReader::new(child.stdout.take().unwrap());
        for _ in 0..2 {
            input
                .write_all(b"{\"version\":1,\"texts\":[],\"batch_size\":null,\"cache_dir\":null}\n")
                .unwrap();
            input.flush().unwrap();
            let mut line = String::new();
            assert_ne!(output.read_line(&mut line).unwrap(), 0);
            assert_eq!(
                serde_json::from_str::<serde_json::Value>(&line).unwrap(),
                serde_json::json!({"status":"started","version":1})
            );
            line.clear();
            assert_ne!(output.read_line(&mut line).unwrap(), 0);
            assert_eq!(
                serde_json::from_str::<serde_json::Value>(&line).unwrap(),
                serde_json::json!({"status":"complete","vectors":[]})
            );
        }
        drop(input);
        assert!(
            child.wait().unwrap().success(),
            "complete stderr: {}",
            stderr_path.display()
        );
        assert!(std::fs::read(&stderr_path).unwrap().is_empty());
    }
}
