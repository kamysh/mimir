//! Real watcher and MCP processes with a disposable PostgreSQL and fixture model.
use mimir_core::{
    config::Config,
    learning::{Experience, ObservationSource, Outcome},
    MimirService,
};
use serde_json::Value;
use std::{fs, os::unix::fs::PermissionsExt, path::Path, process::Stdio, time::Duration};
use tokio::{
    net::{TcpSocket, TcpStream},
    process::Command,
};
use uuid::Uuid;

#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;

// The watchdog bounds a broken test, while progress depends on an observed
// state change. The watcher itself uses its normal reconnect policy.
async fn wait_for_state(file: &Path, field: &str, value: &str) {
    tokio::time::timeout(Duration::from_secs(60), async {
        loop {
            let state = fs::read(file)
                .ok()
                .and_then(|data| serde_json::from_slice::<Value>(&data).ok());
            if state.as_ref().and_then(|state| state[field].as_str()) == Some(value) {
                return;
            }
            tokio::time::sleep(Duration::from_millis(25)).await;
        }
    })
    .await
    .unwrap_or_else(|_| panic!("{} did not report {field}={value}", file.display()));
}

async fn assert_reviewed(service: &MimirService, id: Uuid) {
    tokio::time::timeout(Duration::from_secs(60), async {
        loop {
            let stored = service.get_experience(id).await.unwrap().unwrap();
            if stored.reviewed_revision == 1 {
                assert_eq!(stored.review_revision, 1);
                return;
            }
            tokio::time::sleep(Duration::from_millis(25)).await;
        }
    })
    .await
    .expect("watcher did not commit the review");
}

#[ignore = "requires MIMIR_TEST_ROOT isolated fixture"]
#[tokio::test]
async fn watcher_recovers_at_startup_and_after_listener_loss() {
    let fixture = isolation::fixture();
    let core = Config::load_from_path(&fixture.root.join("config.toml")).unwrap();
    fixture.assert_database(&core.database);
    let service = MimirService::connect(&core).await.unwrap();
    let control = mimir_core::db::connect(&core.database).await.unwrap();
    let project = format!("watch-reconnect-{}", Uuid::new_v4());
    let dir = fixture.root.join(&project);
    fs::create_dir(&dir).unwrap();
    let state = dir.join("state");
    let status = state.join("judge-status.json");
    let runtime = state.join("judge-runtime.json");
    let config = dir.join("config.toml");
    let model = dir.join("model.sh");
    fs::write(
        &model,
        r#"#!/usr/bin/env bash
set -euo pipefail
jq -c 'if (.history | length) > 0 then {calls:[]}
  else {calls:[{name:"review_experience",arguments_json:({
    expected_review_revision:.experience.review_revision,
    review:{experience_id:.experience.experience.id,experience_revision:.experience.revision,
            reviewer:"test",rationale:"Verified fixture observation"}
  }|tojson)}]} end'
"#,
    )
    .unwrap();
    fs::set_permissions(&model, fs::Permissions::from_mode(0o700)).unwrap();

    // Reserve a port without listening, so PostgreSQL is genuinely refused.
    // Start forwarding to the verified disposable PostgreSQL only after the
    // watcher has recorded the refusal.
    let socket = TcpSocket::new_v4().unwrap();
    socket.bind("127.0.0.1:0".parse().unwrap()).unwrap();
    let mut database = fixture.database_config();
    let upstream = ("127.0.0.1", database.port);
    database.port = socket.local_addr().unwrap().port();
    let passfile = dir.join("pgpass");
    let original_pass = fs::read_to_string(fixture.root.join("test.pgpass")).unwrap();
    let (_, remainder) = original_pass
        .strip_prefix("127.0.0.1:")
        .unwrap()
        .split_once(':')
        .unwrap();
    fs::write(
        &passfile,
        format!("127.0.0.1:{}:{remainder}", database.port),
    )
    .unwrap();
    fs::set_permissions(&passfile, fs::Permissions::from_mode(0o600)).unwrap();
    database.pgpassfile = Some(passfile.to_str().unwrap().into());

    let mut settings: toml::Table =
        toml::from_str(&fs::read_to_string(fixture.root.join("config.toml")).unwrap()).unwrap();
    settings.insert("database".into(), toml::Value::try_from(database).unwrap());
    settings["judge"]
        .as_table_mut()
        .unwrap()
        .insert("project".into(), project.clone().into());
    settings["llm"]["command"] = toml::Value::String(model.to_str().unwrap().into());
    fs::write(&config, toml::to_string(&settings).unwrap()).unwrap();
    fs::set_permissions(&config, fs::Permissions::from_mode(0o600)).unwrap();

    let new_experience = || Experience {
        id: Uuid::new_v4(),
        project: project.clone(),
        context: "watcher reconnect fixture".into(),
        action: "record isolated observation".into(),
        outcome: Outcome::Success,
        source: ObservationSource::ToolResult,
        evidence: vec!["fixture evidence".into()],
        belief_ids: vec![],
        pattern_id: None,
        learning_items: vec![],
        source_records: vec![],
    };
    let first = new_experience();
    let first = service
        .record_experience(&first, 0)
        .await
        .unwrap()
        .experience;
    let mut watcher = Command::new(&fixture.mimir)
        .args(["judge", "watch", "--config"])
        .arg(&config)
        .arg("--state-dir")
        .arg(&state)
        .stdout(Stdio::from(
            fs::File::create(dir.join("watch.stdout")).unwrap(),
        ))
        .stderr(Stdio::from(
            fs::File::create(dir.join("watch.stderr")).unwrap(),
        ))
        .kill_on_drop(true)
        .spawn()
        .unwrap();
    wait_for_state(&status, "block_reason", "database_unavailable").await;
    let diagnostic = Command::new(&fixture.mimir)
        .args(["judge", "diagnose", "--config"])
        .arg(&config)
        .arg("--state-dir")
        .arg(&state)
        .output()
        .await
        .unwrap();
    fs::write(dir.join("diagnose.stdout"), &diagnostic.stdout).unwrap();
    fs::write(dir.join("diagnose.stderr"), &diagnostic.stderr).unwrap();
    assert!(diagnostic.status.success());
    let diagnostic = String::from_utf8(diagnostic.stdout).unwrap();
    assert!(
        diagnostic.contains("PostgreSQL connection")
            && diagnostic.contains("retries automatically")
    );

    let listener = socket.listen(128).unwrap();
    let outage_report = fs::read(&status).unwrap();
    // Observe retries while PostgreSQL is still unreachable. Closing an
    // accepted connection before the handshake keeps the outage active.
    for _ in 0..2 {
        let (connection, _) = tokio::time::timeout(Duration::from_secs(60), listener.accept())
            .await
            .expect("watcher did not retry the connection")
            .unwrap();
        drop(connection);
    }
    assert_eq!(fs::read(&status).unwrap(), outage_report);
    let proxy = tokio::spawn(async move {
        while let Ok((mut incoming, _)) = listener.accept().await {
            tokio::spawn(async move {
                let mut outgoing = TcpStream::connect(upstream).await.unwrap();
                let _ = tokio::io::copy_bidirectional(&mut incoming, &mut outgoing).await;
            });
        }
    });
    assert_reviewed(&service, first.id).await;
    wait_for_state(&runtime, "phase", "waiting_for_work").await;

    // Close the actual LISTEN session. After observing the outage report,
    // queue another review before the watcher has a new subscription.
    let subscription = control.query_one(
        "SELECT pid FROM pg_stat_activity WHERE usename = current_user AND datname = current_database() AND query = 'LISTEN mimir_review_work'",
        &[],
    ).await.unwrap().get::<_, i32>(0);
    let terminated: bool = control
        .query_one("SELECT pg_terminate_backend($1)", &[&subscription])
        .await
        .unwrap()
        .get(0);
    assert!(terminated);
    wait_for_state(&status, "block_reason", "database_unavailable").await;
    let second = new_experience();
    let second = service
        .record_experience(&second, 0)
        .await
        .unwrap()
        .experience;
    assert_reviewed(&service, second.id).await;
    wait_for_state(&runtime, "phase", "waiting_for_work").await;

    let pid = watcher.id().unwrap() as i32;
    assert_eq!(unsafe { libc::kill(pid, libc::SIGTERM) }, 0);
    assert!(watcher.wait().await.unwrap().success());
    proxy.abort();
    let stderr = fs::read_to_string(dir.join("watch.stderr")).unwrap();
    assert_eq!(
        stderr
            .matches("PostgreSQL is unavailable; Mimir will retry")
            .count(),
        2,
        "expected one message for each outage"
    );
}
