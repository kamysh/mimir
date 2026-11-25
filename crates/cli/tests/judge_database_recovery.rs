//! Real watcher and MCP processes with a disposable PostgreSQL and fixture model.
use mimir_core::{
    config::Config,
    learning::{Experience, ObservationSource, Outcome},
    MimirService,
};
use serde_json::Value;
use std::{fs, os::unix::fs::PermissionsExt, path::Path, process::Stdio, time::Duration};
use tokio::{
    net::{TcpListener, TcpSocket, TcpStream},
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
async fn watcher_reopens_cases_whose_host_obstruction_was_fixed() {
    let fixture = isolation::fixture();
    let core = Config::load_from_path(&fixture.root.join("config.toml")).unwrap();
    fixture.assert_database(&core.database);
    let service = MimirService::connect(&core).await.unwrap();
    let db = mimir_core::db::connect(&core.database).await.unwrap();
    let project = format!("restored-host-{}", Uuid::new_v4());
    let dir = fixture.root.join(&project);
    fs::create_dir(&dir).unwrap();
    let state = dir.join("state");
    let config = dir.join("config.toml");
    let model = dir.join("model.sh");
    let belief = service
        .add_belief_in_project(
            "A project belief for explanation",
            0.6,
            0.5,
            &project,
            mimir_core::graph::MemoryType::Fact,
        )
        .await
        .unwrap();
    fs::write(dir.join("belief-id"), belief.id.to_string()).unwrap();
    fs::write(
        &model,
        r#"#!/usr/bin/env bash
set -euo pipefail
jq -c --rawfile belief "$(dirname "$0")/belief-id" '
  .experience as $selected |
  if $selected.experience.context == "legacy explanation" and (.history|length)==0 then
    {calls:[{name:"explain_belief",arguments_json:({id:$belief}|tojson)}]}
  elif (.history[-1].tool_results[0].result.error // null) != null or
       (.history[-1].tool_results[0].result.status // "") == "needs_correction" then
    error("the valid explanation was rejected")
  else
    {calls:[{name:"review_experience",arguments_json:({
      expected_review_revision:$selected.review_revision,
      review:{experience_id:$selected.experience.id,experience_revision:$selected.revision,
        reviewer:"fixture",rationale:"Checked the stored observation"}}|tojson)}]}
  end'
"#,
    )
    .unwrap();
    fs::set_permissions(&model, fs::Permissions::from_mode(0o700)).unwrap();
    let mut settings: toml::Table =
        toml::from_str(&fs::read_to_string(fixture.root.join("config.toml")).unwrap()).unwrap();
    settings["judge"]
        .as_table_mut()
        .unwrap()
        .insert("project".into(), project.clone().into());
    settings["llm"]["command"] = model.to_str().unwrap().into();
    settings["email"] = toml::Value::try_from(serde_json::json!({"enabled":false})).unwrap();
    fs::write(&config, toml::to_string(&settings).unwrap()).unwrap();
    fs::set_permissions(&config, fs::Permissions::from_mode(0o600)).unwrap();
    let make = |context: &str| Experience {
        id: (),
        project: project.clone(),
        context: context.into(),
        action: "record observation".into(),
        outcome: Outcome::Success,
        source: ObservationSource::ToolResult,
        evidence: vec!["fixture evidence".into()],
        belief_ids: vec![],
        pattern_id: None,
        learning_items: vec![],
        source_records: vec![],
    };
    let mut ids = Vec::new();
    for (context, events) in [
        (
            "legacy correction",
            serde_json::json!([
            {"kind":"automatic_review_correction","tool":"review_experience"},
            {"kind":"tool_result","tool":"review_experience","detail":{"status":"needs_correction",
                "fault":{"code":"quotation_mismatch"}}}]),
        ),
        (
            "legacy explanation",
            serde_json::json!([
            {"kind":"tool_request","tool":"explain_belief","detail":{"id":belief.id}},
            {"kind":"tool_rejection","tool":"explain_belief","detail":"invalid explain limit"}]),
        ),
        (
            "requires user decision",
            serde_json::json!([
            {"kind":"automatic_review_correction","tool":"review_experience"},
            {"kind":"tool_result","tool":"review_experience","detail":{"status":"needs_input"}}]),
        ),
    ] {
        let id = service
            .create_experience(&make(context))
            .await
            .unwrap()
            .experience
            .id;
        db.execute(
            "INSERT INTO mimir_review_repair_cases(experience_id,source_revision,remedy)
            VALUES($1,1,$2)",
            &[
                &id,
                &serde_json::json!({"remedy":"edit_review",
                "explanation":context,"detail":context,"diagnostic_id":null}),
            ],
        )
        .await
        .unwrap();
        db.execute(
            "INSERT INTO mimir_failed_review_transcripts
            (attempt_key,experience_id,source_revision,transcript) VALUES($1,$2,1,$3)",
            &[
                &format!("legacy-{id}"),
                &id,
                &serde_json::json!({"events":events,"readback":"pending"}),
            ],
        )
        .await
        .unwrap();
        ids.push(id);
    }
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
    assert_reviewed(&service, ids[0]).await;
    assert_reviewed(&service, ids[1]).await;
    wait_for_state(
        &state.join("judge-runtime.json"),
        "phase",
        "waiting_for_work",
    )
    .await;
    assert_eq!(
        service
            .get_experience(ids[2])
            .await
            .unwrap()
            .unwrap()
            .reviewed_revision,
        0
    );
    let held: Vec<Uuid> = db
        .query(
            "SELECT experience_id FROM mimir_review_repair_cases WHERE experience_id=ANY($1)",
            &[&ids],
        )
        .await
        .unwrap()
        .iter()
        .map(|row| row.get(0))
        .collect();
    assert_eq!(held, vec![ids[2]], "a genuine user decision must stay held");
    watcher.kill().await.unwrap();
    watcher.wait().await.unwrap();
    service.delete_project(&project).await.unwrap();
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
    let mcp_wrapper = dir.join("mcp-wrapper.sh");
    let block_batch = dir.join("block-batch");
    fs::write(
        &mcp_wrapper,
        r#"#!/usr/bin/env bash
set -euo pipefail
if [[ -e "$1" ]]; then
    echo "fixture interrupts MCP startup" >&2
    exit 1
fi
exec "$2"
"#,
    )
    .unwrap();
    fs::set_permissions(&mcp_wrapper, fs::Permissions::from_mode(0o700)).unwrap();
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
    let judge = settings["judge"].as_table_mut().unwrap();
    judge.insert("project".into(), project.clone().into());
    judge.insert("mcp_command".into(), mcp_wrapper.to_str().unwrap().into());
    judge.insert(
        "mcp_args".into(),
        toml::Value::Array(vec![
            block_batch.to_str().unwrap().into(),
            fixture.mcp.clone().into(),
        ]),
    );
    settings["llm"]["command"] = toml::Value::String(model.to_str().unwrap().into());
    fs::write(&config, toml::to_string(&settings).unwrap()).unwrap();
    fs::set_permissions(&config, fs::Permissions::from_mode(0o600)).unwrap();

    let new_experience = || Experience {
        id: (),
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
    let first = service
        .create_experience(&new_experience())
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
    let second = service
        .create_experience(&new_experience())
        .await
        .unwrap()
        .experience;
    assert_reviewed(&service, second.id).await;
    wait_for_state(&runtime, "phase", "waiting_for_work").await;

    // A blocked batch must keep listening for the database going away.
    // Removing the marker is deliberately separate from the watched config.
    fs::write(&block_batch, "").unwrap();
    let third = service
        .create_experience(&new_experience())
        .await
        .unwrap()
        .experience;
    wait_for_state(&runtime, "phase", "awaiting_repair").await;
    let subscription = control.query_one(
        "SELECT pid FROM pg_stat_activity WHERE usename = current_user AND datname = current_database() AND query = 'LISTEN mimir_review_work'",
        &[],
    ).await.unwrap().get::<_, i32>(0);
    fs::remove_file(&block_batch).unwrap();
    let terminated: bool = control
        .query_one("SELECT pg_terminate_backend($1)", &[&subscription])
        .await
        .unwrap()
        .get(0);
    assert!(terminated);
    wait_for_state(&status, "block_reason", "database_unavailable").await;
    assert_reviewed(&service, third.id).await;
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
        3,
        "expected one message for each outage"
    );
}

#[ignore = "requires MIMIR_TEST_ROOT isolated fixture"]
#[tokio::test]
async fn watcher_recovers_review_failures_without_stalling() {
    let fixture = isolation::fixture();
    let fixture_config = fixture.root.join("config.toml");
    let core = Config::load_from_path(&fixture_config).unwrap();
    fixture.assert_database(&core.database);
    let service = MimirService::connect(&core).await.unwrap();

    let project = "watch-review-rejection";
    let dir = fixture.root.join(project);
    fs::create_dir(&dir).unwrap();
    let state = dir.join("state");
    let runtime = state.join("judge-runtime.json");
    let config = dir.join("config.toml");
    let model = dir.join("model.sh");
    let global = service
        .add_belief(
            "global context for review scope fixture",
            0.6,
            0.5,
            mimir_core::graph::MemoryType::Fact,
        )
        .await
        .unwrap();
    fs::write(dir.join("global-id"), global.id.to_string()).unwrap();
    let repair_target = service
        .add_belief_in_project(
            "eligible project belief for the repair fixture",
            0.6,
            0.5,
            project,
            mimir_core::graph::MemoryType::Fact,
        )
        .await
        .unwrap();
    fs::write(
        &model,
        r#"#!/usr/bin/env bash
set -euo pipefail
jq -c --rawfile global "$(dirname "$0")/global-id" --rawfile repaired "$(dirname "$0")/retry-id" '
  def call($name; $args):
    {calls:[{name:$name,arguments_json:($args|tojson)}]};
  def review($extra): .experience as $selected |
    call("review_experience"; {expected_review_revision:$selected.review_revision,
      review:({experience_id:$selected.experience.id,experience_revision:$selected.revision,
        reviewer:"test",rationale:"Verified fixture observation"} + $extra)});
  def invalid:
    {assessments:[{target:{candidate_key:"missing"},scope:"fixture",rubric:"fixture",
      correctness:{value:0.5,weight:0},usefulness:{value:0,weight:0},
      evidence_indices:[],rationale:"Fixture assessment"}]};
  .experience.experience.context as $context |
  (.history[-1].tool_results[0].result // {}) as $reply |
  if .experience.experience.id == $repaired then review({})
  elif $context == "reject this review" or $context == "correct the assessment" then
    if (.history|length) == 0 and $context == "reject this review" then
      call("get_experience"; {id:.experience.experience.id})
    elif (.history|length) == 0 or $reply.experience.id == .experience.experience.id then review(invalid)
    elif $reply.fault.path != ["review","assessments",0,"target","candidate_key"]
      or ($reply.message|contains("missing")|not) then error("missing candidate correction")
    elif $context == "reject this review" then review(invalid)
    else review({}) end
  elif $context == "recover from premature done" then
    if (.history|length) == 0 then {calls:[]}
    elif $reply.error == "review_not_saved" and
      $reply.experience_revision == .experience.revision then review({})
    else error("missing submission instruction") end
  elif $context == "assessed a procedure as a belief" then
    if (.history|length) == 0 then
      review(invalid + {candidates:[{kind:"pattern",key:"missing",
        situation:"A job is already running",approach:"Check the existing job"}]})
    else {calls:[]} end
  else
    if (.history|length) == 0 then call("explain_belief"; {id:$global,limit:1,offset:0})
    elif $reply.fault.path == ["id"] and $reply.fault.code == "wrong_identity"
      then call("get_belief"; {id:$global})
    elif $reply.id == $global then review({})
    else error("missing graph scope correction") end
  end'
"#,
    )
    .unwrap();
    let retry_input = dir.join("retry-id");
    fs::write(&retry_input, "").unwrap();
    fs::set_permissions(&model, fs::Permissions::from_mode(0o700)).unwrap();
    let mut settings: toml::Table =
        toml::from_str(&fs::read_to_string(fixture_config).unwrap()).unwrap();
    settings["judge"]
        .as_table_mut()
        .unwrap()
        .insert("project".into(), project.into());
    settings["llm"]["command"] = model.to_str().unwrap().into();
    let smtp = TcpListener::bind("127.0.0.1:0").await.unwrap();
    settings["email"] = toml::Value::try_from(serde_json::json!({
        "enabled":true, "host":"127.0.0.1", "port":smtp.local_addr().unwrap().port(),
        "tls":"starttls", "auth":"none", "from":"mimir@example.test", "to":["operator@example.test"],
        "timeout_seconds":30, "retry_seconds":3600, "max_attempts":2
    })).unwrap();
    fs::write(&config, toml::to_string(&settings).unwrap()).unwrap();
    fs::set_permissions(&config, fs::Permissions::from_mode(0o600)).unwrap();

    let experience = |context: &str| Experience {
        id: (),
        project: project.into(),
        context: context.into(),
        action: "record isolated observation".into(),
        outcome: Outcome::Success,
        source: ObservationSource::ToolResult,
        evidence: vec!["fixture evidence".into()],
        belief_ids: vec![],
        pattern_id: None,
        learning_items: vec![],
        source_records: vec![],
    };
    let rejected = service
        .create_experience(&experience("reject this review"))
        .await
        .unwrap()
        .experience
        .id;
    let next = service
        .create_experience(&experience("recover from premature done"))
        .await
        .unwrap()
        .experience
        .id;
    let corrected = service
        .create_experience(&experience("correct the assessment"))
        .await
        .unwrap()
        .experience
        .id;
    // A status file from 3.2.0 lacks the guided-repair marker. The pending
    // revision retained by that version must be selected by this watcher.
    fs::create_dir(&state).unwrap();
    fs::set_permissions(&state, fs::Permissions::from_mode(0o700)).unwrap();
    let old_status = state.join("judge-status.json");
    fs::write(
        &old_status,
        serde_json::json!({
            "status":"blocked", "selected":1, "confirmed":0, "corrected":0,
            "pending":1, "unavailable":0, "recorded_at":0,
            "deferred_reviews":[{"id":next,"revision":1}]
        })
        .to_string(),
    )
    .unwrap();
    fs::set_permissions(&old_status, fs::Permissions::from_mode(0o600)).unwrap();

    let transcript_db = mimir_core::db::connect(&core.database).await.unwrap();
    transcript_db
        .batch_execute(
            "ALTER TABLE mimir_failed_review_transcripts RENAME TO unavailable_transcript_store",
        )
        .await
        .unwrap();

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

    // With no daily-report time configured, the separate mail worker must
    // connect on the failure event itself. Withhold the SMTP banner while
    // verifying that the watcher still saves the unrelated reviews.
    let (mail_connection, _) = tokio::time::timeout(Duration::from_secs(60), smtp.accept())
        .await
        .expect("the failure alert must start delivery immediately")
        .unwrap();
    assert_reviewed(&service, next).await;
    assert_reviewed(&service, corrected).await;
    wait_for_state(&runtime, "phase", "waiting_for_work").await;
    assert!(!state.join("judge-diagnostics.json").exists());
    let status: Value = serde_json::from_slice(&fs::read(&old_status).unwrap()).unwrap();
    assert_eq!(status["transcripts_pending"], 1);
    let log_directory = settings["logging"]["directory"].as_str().unwrap();
    let log = fs::read_to_string(Path::new(log_directory).join("mimir.log")).unwrap();
    assert!(log.contains("reason=review_requires_repair"));
    assert!(log.contains("confirmed=1; pending=0"));
    assert!(!log.contains("step=model_request"));
    assert_eq!(
        service
            .get_experience(rejected)
            .await
            .unwrap()
            .unwrap()
            .reviewed_revision,
        0
    );

    transcript_db
        .batch_execute(
            "ALTER TABLE unavailable_transcript_store RENAME TO mimir_failed_review_transcripts",
        )
        .await
        .unwrap();
    let later = service
        .create_experience(&experience("correct the graph scope"))
        .await
        .unwrap()
        .experience
        .id;
    assert_reviewed(&service, later).await;
    let automatic = service
        .create_experience(&experience("assessed a procedure as a belief"))
        .await
        .unwrap()
        .experience
        .id;
    assert_reviewed(&service, automatic).await;
    wait_for_state(&runtime, "phase", "waiting_for_work").await;

    let history = service.experience_history(automatic).await.unwrap();
    let review = &history["reviews"][0]["payload"];
    assert_eq!(review["candidates"][0]["kind"], "pattern");
    assert_eq!(review["candidates"][0]["key"], "missing");
    assert!(
        review["assessments"].is_null()
            || review["assessments"].as_array().is_some_and(Vec::is_empty)
    );
    let outbox: Value =
        serde_json::from_slice(&fs::read(state.join("notification-outbox.json")).unwrap()).unwrap();
    let automatic_key = format!("review/{automatic}/1");
    assert!(outbox["incidents"]
        .as_object()
        .unwrap()
        .values()
        .all(|incident| incident["incident_key"] != automatic_key));
    let review_key = format!("review/{rejected}/1");
    let incident = outbox["incidents"]
        .as_object()
        .unwrap()
        .values()
        .find(|incident| incident["incident_key"] == review_key)
        .unwrap();
    let details = incident["outbox"]["details"].as_str().unwrap();
    assert!(details.contains("belief candidate that it did not declare"));
    assert!(details.contains(&format!(
        "mimir judge repair --experience {rejected} --revision 1"
    )));
    assert!(details.contains("transcript is awaiting PostgreSQL"));
    let saved = transcript_db
        .query(
            "SELECT id, experience_id, transcript FROM mimir_failed_review_transcripts
         WHERE experience_id = ANY($1)",
            &[&vec![rejected, next, corrected, later, automatic]],
        )
        .await
        .unwrap();
    assert_eq!(
        saved.len(),
        1,
        "successful reviews discard their transcripts"
    );
    assert_eq!(saved[0].get::<_, Uuid>(1), rejected);
    let transcript_id: Uuid = saved[0].get(0);
    let transcript: Value = saved[0].get(2);
    let events = transcript["events"].as_array().unwrap();
    assert!(events.iter().any(|event| event["kind"] == "tool_rejection"));
    let result_events: Vec<_> = events
        .iter()
        .filter(|event| event["kind"] == "tool_result")
        .collect();
    assert_eq!(result_events.len(), 1);
    assert_eq!(result_events[0]["tool"], "get_experience");
    assert!(events.iter().all(|event| event["kind"] != "model_request"));
    let readback = Command::new(&fixture.mimir)
        .args(["judge", "diagnostics", "--json", "--config"])
        .arg(&config)
        .arg("--state-dir")
        .arg(&state)
        .args(["--id", &transcript_id.to_string()])
        .output()
        .await
        .unwrap();
    assert!(readback.status.success());
    let output: Value = serde_json::from_slice(&readback.stdout).unwrap();
    assert_eq!(output["trace"]["transcript"], transcript);
    let readable = Command::new(&fixture.mimir)
        .args(["judge", "diagnostics", "--config"])
        .arg(&config)
        .arg("--state-dir")
        .arg(&state)
        .args(["--id", &transcript_id.to_string()])
        .output()
        .await
        .unwrap();
    assert!(readable.status.success());
    let explanation = String::from_utf8(readable.stdout).unwrap();
    assert!(explanation.contains("Why it failed"));
    assert!(explanation.contains("guided repair"));
    assert!(!explanation.contains("\"events\""));

    let repair = |id: Uuid, revision: &str| {
        let mut command = Command::new(&fixture.mimir);
        command
            .args([
                "judge",
                "repair",
                "--experience",
                &id.to_string(),
                "--revision",
                revision,
                "--config",
            ])
            .arg(&config)
            .arg("--state-dir")
            .arg(&state)
            .kill_on_drop(true);
        command
    };
    let guide = repair(rejected, "1").output().await.unwrap();
    fs::write(dir.join("guide.stdout"), &guide.stdout).unwrap();
    fs::write(dir.join("guide.stderr"), &guide.stderr).unwrap();
    assert!(!guide.status.success());
    let instructions = String::from_utf8(guide.stdout).unwrap();
    assert!(instructions.contains("Fixture assessment"));
    assert!(instructions.contains("which the judge never defined as a belief"));
    assert!(instructions.contains("Repair cancelled"));

    let file = dir.join("corrected-review.json");
    fs::write(&file, serde_json::json!({
        "experience_id":rejected, "experience_revision":1,
        "reviewer":"operator", "rationale":"Reviewed the source and removed the unsupported reference."
    }).to_string()).unwrap();
    let stale = repair(rejected, "2")
        .arg("--review")
        .arg(&file)
        .output()
        .await
        .unwrap();
    fs::write(dir.join("stale.stdout"), &stale.stdout).unwrap();
    fs::write(dir.join("stale.stderr"), &stale.stderr).unwrap();
    assert!(!stale.status.success());
    assert_eq!(
        service
            .get_experience(rejected)
            .await
            .unwrap()
            .unwrap()
            .reviewed_revision,
        0
    );

    use tokio::io::AsyncWriteExt;
    let mut interactive = repair(rejected, "1")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    interactive
        .stdin
        .take()
        .unwrap()
        .write_all(b"b\neligible project belief for the repair fixture\ny\nyes\n")
        .await
        .unwrap();
    let applied = interactive.wait_with_output().await.unwrap();
    fs::write(dir.join("repair.stdout"), &applied.stdout).unwrap();
    fs::write(dir.join("repair.stderr"), &applied.stderr).unwrap();
    assert!(
        applied.status.success(),
        "{}",
        String::from_utf8_lossy(&applied.stderr)
    );
    assert!(String::from_utf8_lossy(&applied.stdout).contains("PostgreSQL confirmed the review"));
    assert_reviewed(&service, rejected).await;
    let history = service.experience_history(rejected).await.unwrap();
    assert_eq!(
        history["reviews"][0]["payload"]["reviewer"],
        "mimir-operator"
    );
    assert_eq!(
        history["reviews"][0]["payload"]["assessments"][0]["target"]["belief_id"],
        serde_json::json!(repair_target.id)
    );
    drop(mail_connection);

    let retry_id = service
        .create_experience(&experience("reject this review"))
        .await
        .unwrap()
        .experience
        .id;
    tokio::time::timeout(Duration::from_secs(60), async {
        loop {
            let report = fs::read(&old_status)
                .ok()
                .and_then(|data| serde_json::from_slice::<Value>(&data).ok());
            if report.as_ref().is_some_and(|report| {
                report["deferred_reviews"].as_array().is_some_and(|held| {
                    held.iter()
                        .any(|review| review["id"] == retry_id.to_string())
                })
            }) {
                break;
            }
            tokio::time::sleep(Duration::from_millis(25)).await;
        }
    })
    .await
    .expect("the second rejected review should have its own repair case");
    fs::write(&retry_input, retry_id.to_string()).unwrap();
    let retried = repair(retry_id, "1").arg("--retry").output().await.unwrap();
    fs::write(dir.join("retry.stdout"), &retried.stdout).unwrap();
    fs::write(dir.join("retry.stderr"), &retried.stderr).unwrap();
    assert!(
        retried.status.success(),
        "{}",
        String::from_utf8_lossy(&retried.stderr)
    );
    assert_reviewed(&service, retry_id).await;

    assert_eq!(
        unsafe { libc::kill(watcher.id().unwrap() as i32, libc::SIGTERM) },
        0
    );
    assert!(watcher.wait().await.unwrap().success());
}
