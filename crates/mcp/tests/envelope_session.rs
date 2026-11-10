//! Exercise correction and continued use through the actual stdio server.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;

use anyhow::{ensure, Result};
use mimir_core::{config::Config, interaction::NeedsInput, MimirService};
use serde_json::{json, Value};
use std::process::Stdio;
use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
use uuid::Uuid;

#[tokio::test]
async fn malformed_messages_do_not_execute_and_the_same_connection_recovers() -> Result<()> {
    let fixture = isolation::fixture();
    let service = MimirService::connect(&Config {
        database: fixture.database_config(),
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
        retirement: None,
    })
    .await?;
    let project = format!("envelope-session-{}", Uuid::new_v4());
    let experience_id = Uuid::new_v4();
    let other_project = format!("{project}-other");
    let audit = mimir_core::db::connect(&fixture.database_config()).await?;
    let other_id: Uuid = audit
        .query_one("SELECT gen_random_uuid()", &[])
        .await?
        .get(0);
    service.record_experience(&mimir_json::from_value(json!({
        "id":other_id,"project":other_project,"context":"preserve the other possible project too",
        "action":"reject ambiguous deletion","outcome":"unknown","source":"agent_report",
        "evidence":["private fixture setup"]
    }))?,0).await?;
    service
        .record_experience(
            &mimir_json::from_value(json!({
                "id":experience_id, "project":project, "context":"preserve this project",
                "action":"exercise envelope admission", "outcome":"unknown", "source":"agent_report",
                "evidence":["private fixture setup"]
            }))?,
            0,
        )
        .await?;

    let stderr = std::fs::File::create(
        fixture
            .root
            .join(format!("envelope-session-{}.stderr", Uuid::new_v4())),
    )?;
    let mut child = tokio::process::Command::new(env!("CARGO_BIN_EXE_mimir-mcp"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(stderr)
        .kill_on_drop(true)
        .spawn()?;
    let mut input = child.stdin.take().unwrap();
    let mut output = BufReader::new(child.stdout.take().unwrap());
    let delete_token = service
        .reserve_operation(&format!("{project}-delete-envelope-case"))
        .await?
        .operation_token;
    let delete = json!({"name":"delete_project", "arguments":{"project":project,"operation_token":delete_token}});
    let invalid = vec![
        (vec![0xff, b'\n'], -32700, Value::Null),
        (b"{\n".to_vec(), -32700, Value::Null),
        (b"[]\n".to_vec(), -32600, Value::Null),
        (
            format!(
                "{}\n",
                json!({"jsonrpc":"1.0","id":0,"method":"tools/call","params":delete})
            )
            .into_bytes(),
            -32600,
            json!(0),
        ),
        (
            format!(
                "{}\n",
                json!({"jsonrpc":"2.0","id":false,"method":"tools/call","params":delete})
            )
            .into_bytes(),
            -32600,
            Value::Null,
        ),
        (
            format!(
                "{}\n",
                json!({"jsonrpc":"2.0","id":"params","method":"tools/call","params":null})
            )
            .into_bytes(),
            -32602,
            json!("params"),
        ),
    ];
    for (bytes, code, id) in invalid {
        input.write_all(&bytes).await?;
        input.flush().await?;
        let mut line = String::new();
        ensure!(
            output.read_line(&mut line).await? != 0,
            "server exited on malformed input"
        );
        let response: Value = mimir_json::from_str(&line)?;
        ensure!(
            response["id"] == id && response["error"]["code"] == code,
            "wrong protocol response: {response}"
        );
        let correction: NeedsInput = mimir_json::from_value(response["error"]["data"].clone())?;
        ensure!(!correction.issues().is_empty(), "missing repair details");
    }
    // Repeated envelope/argument members are diagnosed before normalization
    // could choose a handler, project or response identity.
    let encoded_project = mimir_json::to_string(&project)?;
    let encoded_other_project = mimir_json::to_string(&other_project)?;
    for (message,id,path) in [
        (format!(r#"{{"jsonrpc":"2.0","id":"duplicate-project","method":"tools/call","params":{{"name":"delete_project","arguments":{{"project":{encoded_other_project},"project":{encoded_project}}}}}}}"#),json!("duplicate-project"),json!(["params","arguments","project"])),
        (format!(r#"{{"jsonrpc":"2.0","id":"duplicate-method","method":"tools/list","method":"tools/call","params":{delete}}}"#),json!("duplicate-method"),json!(["method"])),
        (format!(r#"{{"jsonrpc":"2.0","id":"first-id","id":"last-id","method":"tools/call","params":{delete}}}"#),Value::Null,json!(["id"])),
        (r#"{"jsonrpc":"2.0","id":"nested-array","method":"tools/call","params":{"name":"record_experience","arguments":{"experience":{"source_records":[{"actor":"one","actor":"two"}]}}}}"#.into(),json!("nested-array"),json!(["params","arguments","experience","source_records",0,"actor"])),
    ] {
        input.write_all(format!("{message}\n").as_bytes()).await?;
        input.flush().await?;
        let mut line=String::new();
        ensure!(output.read_line(&mut line).await?!=0,"server stopped on duplicate fields");
        let response:Value=mimir_json::from_str(&line)?;
        ensure!(response["id"]==id && response["error"]["code"]==-32600,"wrong ambiguous-request response: {response}");
        let correction:NeedsInput=mimir_json::from_value(response["error"]["data"].clone())?;
        let details=mimir_json::to_value(correction)?;
        ensure!(details["issues"].as_array().unwrap().iter().any(|issue|issue["fault"]["path"]==path),"missing repeated-field path: {details}");
    }
    // This ambiguous notification must produce no response and no deletion.
    input.write_all(format!(r#"{{"jsonrpc":"2.0","method":"tools/call","params":{{"name":"delete_project","arguments":{{"project":{encoded_project},"project":{encoded_project}}}}}}}
"#).as_bytes()).await?;
    // Supplied invalid tool fields are corrected before handler execution.
    for params in [
        json!({}),
        json!({"name":7,"arguments":null}),
        json!({"name":"delete_project","argumnts":{"project":project}}),
    ] {
        let message =
            json!({"jsonrpc":"2.0","id":"method-fields","method":"tools/call","params":params});
        input.write_all(format!("{message}\n").as_bytes()).await?;
        input.flush().await?;
        let mut line = String::new();
        ensure!(
            output.read_line(&mut line).await? != 0,
            "server exited on missing method fields"
        );
        let response: Value = mimir_json::from_str(&line)?;
        ensure!(
            response["error"]["code"] == -32602,
            "missing method correction: {response}"
        );
        let _: NeedsInput = mimir_json::from_value(response["error"]["data"].clone())?;
    }
    for (name, mut args, field) in [
        (
            "sweep_expired_defeated",
            json!({"project":project,"prob_threshold":2}),
            "prob_threshold",
        ),
        ("delete_project", json!({}), "project"),
        ("delete_project", json!({"project":4}), "project"),
        ("list_beliefs", json!({"project":false}), "project"),
        (
            "query_relevant",
            json!({"context":"must not embed","limit":"10"}),
            "limit",
        ),
        (
            "record_experience",
            json!({"experience":{"project":project},"expected_revision":"0"}),
            "id",
        ),
        (
            "delete_project",
            json!({"project":project,"projet":"do not guess"}),
            "projet",
        ),
        (
            "query_relevant",
            json!({"context":"must not embed","limt":1}),
            "limt",
        ),
        (
            "insert_pattern",
            json!({"project":project,"situation":"kept","approach":"kept","success_rate":0.5,"approch":"do not guess"}),
            "approch",
        ),
        (
            "record_experience",
            json!({"experience":{"id":experience_id,"project":project,"context":"must not replace","action":"must not apply","outcome":"unknown","source":"agent_report","evidence":[],"evidnce":[]},"expected_revision":1}),
            "evidnce",
        ),
        ("delete_porject", json!({"project":project}), "name"),
        (
            "review_experience",
            json!({"expected_review_revision":0,"review":{
                "experience_id":experience_id,"experience_revision":1,
                "reviewer":"fixture","rationale":"must not publish a candidate",
                "candidates":[{"kind":"belief","key":"","content":"must not be published"}]
            }}),
            "key",
        ),
    ] {
        if mimir_core::operation_catalogue::Operation::ALL
            .iter()
            .any(|operation| operation.name() == name && operation.registered_write().is_some())
        {
            args["operation_token"] = json!(
                service
                    .reserve_operation(&format!("{project}-arguments-{name}-{field}"))
                    .await?
                    .operation_token
            );
        }
        let message = json!({"jsonrpc":"2.0","id":"argument-fields","method":"tools/call","params":{"name":name,"arguments":args}});
        input.write_all(format!("{message}\n").as_bytes()).await?;
        input.flush().await?;
        let mut line = String::new();
        ensure!(
            output.read_line(&mut line).await? != 0,
            "server exited on invalid arguments"
        );
        let response: Value = mimir_json::from_str(&line)?;
        ensure!(
            response.get("error").is_none(),
            "tool correction became a protocol failure: {response}"
        );
        let correction: NeedsInput =
            mimir_json::from_str(response["result"]["content"][0]["text"].as_str().unwrap())?;
        let encoded = mimir_json::to_value(&correction)?;
        if name == "sweep_expired_defeated" {
            ensure!(
                correction.issues()[0].fault().code == mimir_core::validation::Code::InvalidNumber,
                "numeric admission must precede the configuration prerequisite: {encoded}"
            );
        }
        if name == "review_experience" {
            ensure!(
                correction.issues().iter().any(|issue| issue.fault().code
                    == mimir_core::validation::Code::EmptyText
                    && issue.fault().path
                        == vec![
                            mimir_core::validation::Segment::Key("review".into()),
                            mimir_core::validation::Segment::Key("candidates".into()),
                            mimir_core::validation::Segment::Index(0),
                            mimir_core::validation::Segment::Key("key".into())
                        ]),
                "empty candidate key did not receive its exact correction: {encoded}"
            );
        }
        ensure!(
            encoded.to_string().contains(field),
            "correction omitted {field}: {encoded}"
        );
    }
    // Malformed UUIDs are ordinary argument corrections, including nested
    // arrays. No handler may run first and turn them into generic tool errors.
    for (name, mut arguments, paths) in [
        (
            "record_support",
            json!({"from_id":"wrong-from","to_id":"wrong-to","weight":0.5}),
            vec![json!(["from_id"]), json!(["to_id"])],
        ),
        (
            "delete_belief",
            json!({"id":"wrong-id"}),
            vec![json!(["id"])],
        ),
        (
            "record_experience",
            json!({"expected_revision":1,"experience":{
            "id":experience_id,"project":project,"context":"must not replace",
            "action":"must not apply","outcome":"unknown","source":"agent_report",
            "evidence":[],"belief_ids":["wrong-belief"],"pattern_id":"wrong-pattern"}}),
            vec![
                json!(["experience", "belief_ids", 0]),
                json!(["experience", "pattern_id"]),
            ],
        ),
    ] {
        if mimir_core::operation_catalogue::Operation::ALL
            .iter()
            .any(|operation| operation.name() == name && operation.registered_write().is_some())
        {
            arguments["operation_token"] = json!(
                service
                    .reserve_operation(&format!("{project}-uuid-{name}"))
                    .await?
                    .operation_token
            );
        }
        let message = json!({"jsonrpc":"2.0","id":"uuid-fields","method":"tools/call","params":{"name":name,"arguments":arguments}});
        input.write_all(format!("{message}\n").as_bytes()).await?;
        input.flush().await?;
        let mut line = String::new();
        ensure!(
            output.read_line(&mut line).await? != 0,
            "server stopped on malformed UUIDs"
        );
        let response: Value = mimir_json::from_str(&line)?;
        ensure!(
            response.get("error").is_none(),
            "UUID correction became a tool error: {response}"
        );
        let correction: NeedsInput =
            mimir_json::from_str(response["result"]["content"][0]["text"].as_str().unwrap())?;
        let encoded = mimir_json::to_value(&correction)?;
        ensure!(
            encoded["business_changes"] == "none",
            "UUID refusal did not certify no business writes"
        );
        for path in paths {
            ensure!(
                encoded["issues"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .any(|issue| issue["fault"]["path"] == path
                        && issue["fault"]["code"] == "malformed_input"
                        && issue["suggested_correction"]
                            .as_str()
                            .unwrap()
                            .contains("Do not invent")),
                "missing UUID correction at {path}: {encoded}"
            );
        }
    }
    // Required preparation is an ordinary user decision, with no belief
    // written and no loss of the existing connection.
    let review_token = service
        .reserve_operation(&format!("{project}-required-review-preparation"))
        .await?
        .operation_token;
    let review_request = json!({"jsonrpc":"2.0","id":"required-review-preparation","method":"tools/call","params":{
        "name":"review_experience","arguments":{"operation_token":review_token,"expected_review_revision":0,"review":{
            "experience_id":experience_id,"experience_revision":1,"reviewer":"fixture",
            "rationale":"stored experience evidence alone cannot publish an ungrounded belief",
            "candidates":[{"kind":"belief","key":"lesson","content":"must prepare indexed document support"}]}}}});
    input
        .write_all(format!("{review_request}\n").as_bytes())
        .await?;
    input.flush().await?;
    let mut line = String::new();
    ensure!(
        output.read_line(&mut line).await? != 0,
        "server exited on unavailable review preparation"
    );
    let response: Value = mimir_json::from_str(&line)?;
    ensure!(
        response.get("error").is_none(),
        "review decision became a protocol failure: {response}"
    );
    let decision: NeedsInput =
        mimir_json::from_str(response["result"]["content"][0]["text"].as_str().unwrap())?;
    let path = &decision.issues()[0].fault().path;
    ensure!(
        path == &vec![mimir_core::validation::Segment::Key("embeddings".into())]
            || path.starts_with(&[
                mimir_core::validation::Segment::Key("review".into()),
                mimir_core::validation::Segment::Key("candidates".into()),
                mimir_core::validation::Segment::Index(0)
            ]),
        "preparation must identify the missing configuration or exact candidate: {decision:?}"
    );
    ensure!(
        decision.issues()[0]
            .suggested_correction()
            .contains("Open a dialog"),
        "missing user dialog instruction"
    );
    ensure!(
        service
            .get_experience(experience_id)
            .await?
            .unwrap()
            .reviewed_revision
            == 0,
        "unprepared review was acknowledged"
    );
    ensure!(
        service.list_beliefs(Some(&project)).await?.is_empty(),
        "unprepared candidate was published"
    );
    let chunk_id: Uuid = audit
        .query_one("SELECT gen_random_uuid()", &[])
        .await?
        .get(0);
    let chunk = mimir_core::documents::DocumentChunk::with_id(
        chunk_id,
        format!("/mimir-test/{project}.md"),
        vec![],
        "Prepare indexed document support before recording this fact.".into(),
        None,
        Some(project.clone()),
    );
    let store = mimir_core::store::AgeStore::new(
        mimir_core::db::connect(&fixture.database_config()).await?,
        fixture.database_config().dbname,
    )?;
    store.insert_document_chunk(&chunk).await?;
    store
        .insert_chunk_embedding(chunk_id, &[1.0, 0.0, 0.0])
        .await?;
    let belief_token = service
        .reserve_operation(&format!("{project}-required-belief-preparation"))
        .await?
        .operation_token;
    let request = json!({"jsonrpc":"2.0","id":"required-preparation","method":"tools/call","params":{
        "name":"insert_belief","arguments":{"operation_token":belief_token,"content":"must not store without preparation","probability":0.7,"confidence":0.5,
        "project":project,"memory_type":"fact","provenance":{"basis":"user_instruction","reference":"explicit isolated test instruction"},
        "grounding":[{"chunk_id":chunk_id,"document_path":chunk.document_path,"quotation":chunk.content,"explanation":"The passage explicitly requires preparation before publication."}]}}});
    input.write_all(format!("{request}\n").as_bytes()).await?;
    input.flush().await?;
    let mut line = String::new();
    ensure!(
        output.read_line(&mut line).await? != 0,
        "server exited on unavailable preparation"
    );
    let response: Value = mimir_json::from_str(&line)?;
    ensure!(
        response.get("error").is_none(),
        "preparation must open the dialog, not become a tool failure: {response}"
    );
    let decision: NeedsInput =
        mimir_json::from_str(response["result"]["content"][0]["text"].as_str().unwrap())?;
    let decision = mimir_json::to_value(decision)?;
    ensure!(
        decision["business_changes"] == "none" && decision["status"] == "needs_input",
        "untruthful preparation outcome: {decision}"
    );
    ensure!(
        decision["issues"][0]["fault"]["path"] == json!(["embeddings"]),
        "missing preparation location: {decision}"
    );
    ensure!(
        decision["issues"][0]["suggested_correction"]
            .as_str()
            .unwrap()
            .contains("Open a dialog"),
        "missing user decision path: {decision}"
    );
    ensure!(
        service.list_beliefs(Some(&project)).await?.is_empty(),
        "failed preparation stored a belief"
    );

    // Retention is configuration owned by the user, not an agent argument.
    for mut arguments in [
        json!({"project":project}),
        json!({"project":project,"grace_hours":0}),
    ] {
        arguments["operation_token"] = json!(
            service
                .reserve_operation(&format!(
                    "{project}-retention-case-{}",
                    arguments.get("grace_hours").is_some()
                ))
                .await?
                .operation_token
        );
        let request = json!({"jsonrpc":"2.0","id":"retention-policy","method":"tools/call","params":{"name":"sweep_expired_defeated","arguments":arguments}});
        input.write_all(format!("{request}\n").as_bytes()).await?;
        input.flush().await?;
        let mut line = String::new();
        ensure!(
            output.read_line(&mut line).await? != 0,
            "server stopped on missing retention"
        );
        let response: Value = mimir_json::from_str(&line)?;
        ensure!(
            response.get("error").is_none(),
            "retention decision became a tool failure: {response}"
        );
        let correction: NeedsInput =
            mimir_json::from_str(response["result"]["content"][0]["text"].as_str().unwrap())?;
        let code = if arguments.get("grace_hours").is_some() {
            mimir_core::validation::Code::UnknownField
        } else {
            mimir_core::validation::Code::MissingField
        };
        ensure!(
            correction.issues()[0].fault().code == code,
            "wrong retention repair"
        );
        if arguments.get("grace_hours").is_none() {
            ensure!(
                correction.issues()[0].location()
                    == mimir_core::interaction::Location::Configuration,
                "retention location is not configuration"
            );
        }
    }
    // Notifications receive no response. The next response must belong to the
    // identified request, and the original project data must still exist.
    for message in [
        json!({"jsonrpc":"2.0","method":"tools/call","params":delete}),
        json!({"jsonrpc":"2.0","method":"tools/call","params":null}),
        json!({"jsonrpc":"2.0","method":"notifications/initialized"}),
        json!({"jsonrpc":"2.0","id":"still-usable","method":"tools/call", "params":{"name":"get_experience","arguments":{"id":experience_id}}}),
    ] {
        input.write_all(format!("{message}\n").as_bytes()).await?;
    }
    input.flush().await?;
    let mut line = String::new();
    ensure!(
        output.read_line(&mut line).await? != 0,
        "server failed before corrected request"
    );
    let response: Value = mimir_json::from_str(&line)?;
    ensure!(
        response["id"] == "still-usable" && response.get("error").is_none(),
        "connection did not recover: {response}"
    );
    let body: Value =
        mimir_json::from_str(response["result"]["content"][0]["text"].as_str().unwrap())?;
    ensure!(
        body.to_string().contains(&experience_id.to_string()),
        "invalid message deleted project data: {body}"
    );
    ensure!(
        !body.to_string().contains("must not replace"),
        "invalid nested input changed the record: {body}"
    );
    let patterns = json!({"jsonrpc":"2.0","id":"no-hidden-pattern","method":"tools/call","params":{"name":"list_patterns","arguments":{"project":project}}});
    input.write_all(format!("{patterns}\n").as_bytes()).await?;
    input.flush().await?;
    line.clear();
    ensure!(
        output.read_line(&mut line).await? != 0,
        "server exited before checking pattern state"
    );
    let response: Value = mimir_json::from_str(&line)?;
    ensure!(
        response["id"] == "no-hidden-pattern",
        "unexpected extra response: {response}"
    );
    let patterns: Value =
        mimir_json::from_str(response["result"]["content"][0]["text"].as_str().unwrap())?;
    ensure!(
        patterns == json!([]),
        "invalid fields created a pattern: {patterns}"
    );
    drop(input);
    line.clear();
    ensure!(
        output.read_line(&mut line).await? == 0,
        "notification unexpectedly received a response"
    );
    ensure!(child.wait().await?.success(), "server failed on normal EOF");
    ensure!(
        service.get_experience(other_id).await?.is_some(),
        "ambiguous request deleted the other project"
    );
    service.delete_project(&project).await?;
    service.delete_project(&other_project).await?;
    Ok(())
}
