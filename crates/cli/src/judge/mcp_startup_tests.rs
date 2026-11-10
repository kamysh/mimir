use super::*;
use std::fs;
use std::path::PathBuf;
use tokio::io::AsyncBufReadExt;
use tokio::net::{TcpListener, TcpStream};
use tokio::sync::Mutex;

fn fixture_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("src/judge/retry_fixture.sh")
}

fn catalogue() -> Value {
    let output = std::process::Command::new("bash")
        .arg(fixture_path())
        .args(["unused", "", "dump-catalogue"])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    mimir_json::from_slice(&output.stdout).unwrap()
}

fn advertised_mut<'a>(catalogue: &'a mut Value, name: &str) -> &'a mut Value {
    catalogue["tools"]
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|tool| tool["name"] == name)
        .unwrap()
}

#[test]
fn deep_json_schema_survives_catalogue_copy_and_partial_validation_errors() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut valid = mimir_json::Document::new(catalogue());
            let nested =
                mimir_json::parse(&format!("{}null{}", "[".repeat(10000), "]".repeat(10000)))
                    .unwrap();
            advertised_mut(&mut valid, "get_experience")["inputSchema"]
                ["future_schema_annotation"] = nested.into_value();
            let allowed = mimir_json::Document::new(Value::Array(checked_tools(&valid).unwrap()));
            assert!(mimir_json::to_string(&allowed)
                .unwrap()
                .contains("future_schema_annotation"));
            advertised_mut(&mut valid, "review_experience")["inputSchema"]["properties"]
                ["review"]["type"] = json!("wrong");
            assert!(checked_tools(&valid).is_err());
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn catalogue_requires_host_capability_and_every_typed_review_property() {
    let valid = catalogue();
    let allowed = checked_tools(&valid).unwrap();
    let names: Vec<_> = allowed
        .iter()
        .map(|tool| tool["name"].as_str().unwrap())
        .collect();
    assert_eq!(
        names,
        [
            "get_experience",
            "review_experience",
            "experience_history",
            "query_relevant",
            "query_learning_context",
            "query_document",
            "explain_belief",
            "get_belief",
            "query_intervention",
            "get_contradictions"
        ]
    );
    for tool in &allowed {
        let mut expected = valid["tools"]
            .as_array()
            .unwrap()
            .iter()
            .find(|original| original["name"] == tool["name"])
            .unwrap()
            .clone();
        if expected["name"] == "review_experience" {
            expected["inputSchema"]["properties"]
                .as_object_mut()
                .unwrap()
                .remove("operation_token");
            expected["inputSchema"]["required"]
                .as_array_mut()
                .unwrap()
                .retain(|field| field != "operation_token");
        }
        assert_eq!(tool, &expected);
    }
    assert!(allowed
        .iter()
        .all(|tool| tool["name"] != "reserve_operation"
            && tool["name"] != "operation_outcome"
            && tool["name"] != "cancel_operation"));
    for name in ["reserve_operation", "operation_outcome"] {
        let mut absent = valid.clone();
        absent["tools"]
            .as_array_mut()
            .unwrap()
            .retain(|tool| tool["name"] != name);
        assert!(checked_tools(&absent).is_err());
    }
    let mut missing_token = valid.clone();
    advertised_mut(&mut missing_token, "review_experience")["inputSchema"]["required"]
        .as_array_mut()
        .unwrap()
        .retain(|field| field != "operation_token");
    assert!(checked_tools(&missing_token).is_err());
    let mut absent = valid.clone();
    absent["tools"]
        .as_array_mut()
        .unwrap()
        .retain(|tool| tool["name"] != "learning_capabilities");
    assert!(checked_tools(&absent).is_err());
    for wrong in [Value::Null, json!("array"), json!(1)] {
        let mut invalid = valid.clone();
        advertised_mut(&mut invalid, "learning_capabilities")["inputSchema"]["type"] = wrong;
        assert!(checked_tools(&invalid).is_err());
    }
    for field in [
        "experience_id",
        "experience_revision",
        "reviewer",
        "rationale",
        "assessments",
        "extracted_items",
        "source_coverage",
        "feedback",
        "links",
        "superseded_beliefs",
        "candidates",
        "candidate_feedback",
        "candidate_links",
    ] {
        for wrong in [Value::Null, json!("boolean")] {
            let mut invalid = valid.clone();
            advertised_mut(&mut invalid, "review_experience")["inputSchema"]["properties"]
                ["review"]["properties"][field]["type"] = wrong;
            assert!(checked_tools(&invalid).is_err(), "accepted invalid {field}");
        }
    }
}

#[test]
fn catalogue_keeps_first_match_and_optional_advertised_definitions() {
    let mut valid = catalogue();
    let duplicate = advertised_mut(&mut valid, "review_experience").clone();
    advertised_mut(&mut valid, "review_experience")["inputSchema"]["properties"]["review"]
        ["properties"]["assessments"]["type"] = json!("string");
    valid["tools"].as_array_mut().unwrap().push(duplicate);
    assert!(
        checked_tools(&valid).is_err(),
        "a later duplicate replaced the invalid first definition"
    );

    let mut valid = catalogue();
    let original_count = checked_tools(&valid).unwrap().len();
    for name in ["get_lesson_assessment", "lesson_assessment_history"] {
        valid["tools"]
            .as_array_mut()
            .unwrap()
            .push(json!({"name":name,"description":"original",
            "inputSchema":{"properties":{"project":{"type":"string"},"belief_id":{"type":"string"},
            "scope":{"type":"string"},"rubric":{"type":"string"}}}}));
    }
    valid["tools"]
        .as_array_mut()
        .unwrap()
        .push(json!({"name":"get_learning_review",
        "inputSchema":{"properties":{"id":{"type":"string"}}}}));
    assert_eq!(checked_tools(&valid).unwrap().len(), original_count + 3);
    for name in [
        "get_lesson_assessment",
        "lesson_assessment_history",
        "get_learning_review",
    ] {
        let mut malformed = valid.clone();
        advertised_mut(&mut malformed, name)["inputSchema"] = Value::Null;
        assert!(checked_tools(&malformed).is_err());
    }
}

fn capabilities() -> Value {
    json!({"contract_version":3,"assessment_model_version":1,"source_coverage":true,
        "typed_learning_items":true,"revision_owned_assessments":true,
        "legacy_graph_probability_unchanged":true})
}

#[test]
fn capabilities_require_exact_versions_and_all_boolean_support_flags() {
    let valid = capabilities();
    validate_learning_capabilities(&valid).unwrap();
    for field in ["contract_version", "assessment_model_version"] {
        for wrong in [
            Value::Null,
            json!(-1),
            json!(0),
            json!(2),
            json!(2.0),
            json!("2"),
            json!(true),
        ] {
            let mut invalid = valid.clone();
            invalid[field] = wrong;
            assert!(
                validate_learning_capabilities(&invalid).is_err(),
                "accepted invalid {field}"
            );
        }
    }
    for field in [
        "source_coverage",
        "typed_learning_items",
        "revision_owned_assessments",
        "legacy_graph_probability_unchanged",
    ] {
        for wrong in [Value::Null, json!(false), json!(1), json!("true")] {
            let mut invalid = valid.clone();
            invalid[field] = wrong;
            assert!(
                validate_learning_capabilities(&invalid).is_err(),
                "accepted invalid {field}"
            );
        }
    }
    for field in valid.as_object().unwrap().keys() {
        let mut absent = valid.clone();
        absent.as_object_mut().unwrap().remove(field);
        assert!(validate_learning_capabilities(&absent).is_err());
    }
    for invalid in [Value::Null, json!([]), json!("2.1.0")] {
        assert!(validate_learning_capabilities(&invalid).is_err());
    }
    let mut extended = valid;
    extended["future_field"] = json!({"ignored":true});
    validate_learning_capabilities(&extended).unwrap();
}

struct Fixture {
    path: PathBuf,
    listener: TcpListener,
    ownership: Mutex<Option<tokio::io::BufReader<TcpStream>>>,
}

impl Fixture {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!("mimir-startup-{}", uuid::Uuid::new_v4()));
        fs::create_dir(&path).unwrap();
        let listener = std::net::TcpListener::bind("127.0.0.1:0").unwrap();
        listener.set_nonblocking(true).unwrap();
        Self {
            path,
            listener: TcpListener::from_std(listener).unwrap(),
            ownership: Mutex::new(None),
        }
    }

    async fn start(&self, mode: &str) -> Result<Client> {
        let result = Client::start(
            "bash",
            &[
                fixture_path().to_string_lossy().into_owned(),
                "00000000-0000-4000-8000-000000000001".into(),
                String::new(),
                mode.into(),
                self.path.join("requests").to_string_lossy().into_owned(),
                self.path.join("pids").to_string_lossy().into_owned(),
                self.listener.local_addr()?.to_string(),
            ],
            &self.path.join("unused config.toml"),
        )
        .await;
        let (stream, _) = self.listener.accept().await?;
        let mut ownership = tokio::io::BufReader::new(stream);
        let mut event = String::new();
        ownership.read_line(&mut event).await?;
        let pids = self.pids();
        assert_eq!(event, format!("mcp {} {}\n", pids[0], pids[1]));
        *self.ownership.lock().await = Some(ownership);
        result
    }

    fn requests(&self) -> Vec<Value> {
        fs::read_to_string(self.path.join("requests"))
            .unwrap()
            .lines()
            .map(|line| mimir_json::from_str(line).unwrap())
            .collect()
    }

    fn pids(&self) -> Vec<u32> {
        fs::read_to_string(self.path.join("pids"))
            .unwrap()
            .lines()
            .map(|line| line.parse().unwrap())
            .collect()
    }

    async fn stopped(&self) {
        let mut ownership = self
            .ownership
            .lock()
            .await
            .take()
            .expect("fixture announced ownership");
        let mut remaining = Vec::new();
        ownership.read_to_end(&mut remaining).await.unwrap();
        assert!(
            remaining.is_empty(),
            "unexpected ownership event after readiness"
        );
        for pid in self.pids() {
            let alive = fs::read_to_string(format!("/proc/{pid}/stat"))
                .is_ok_and(|state| state.split_whitespace().nth(2) != Some("Z"));
            assert!(
                !alive,
                "owned fixture process {pid} survived client cleanup"
            );
        }
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

#[tokio::test]
async fn startup_and_calls_share_ids_and_owned_process_group() {
    let fixture = Fixture::new();
    let mut client = fixture.start("").await.unwrap();
    assert_eq!(client.next_id, 4);
    assert_eq!(
        fs::read_to_string(fixture.path.join("pids.config")).unwrap(),
        fixture.path.join("unused config.toml").to_string_lossy()
    );
    let pids = fixture.pids();
    assert_eq!(client.child.id(), Some(pids[0]));
    assert_eq!(unsafe { libc::getpgid(pids[0] as i32) }, pids[0] as i32);
    assert_ne!(unsafe { libc::getpgrp() }, pids[0] as i32);
    client
        .notify("notifications/initialized", json!({}))
        .await
        .unwrap();
    assert_eq!(client.next_id, 4);
    client.tool("pending_experiences", json!({})).await.unwrap();
    assert_eq!(client.next_id, 5);
    client.next_id = u64::MAX;
    assert!(client
        .request("tools/list", json!({}))
        .await
        .unwrap_err()
        .to_string()
        .contains("ID overflow"));
    assert_eq!(client.next_id, u64::MAX);
    client.next_id = u64::MAX - 1;
    client.request("tools/list", json!({})).await.unwrap();
    assert_eq!(client.next_id, u64::MAX);
    drop(client);
    fixture.stopped().await;
    let requests = fixture.requests();
    assert_eq!(requests.len(), 7, "overflow calls must send nothing");
    let methods: Vec<_> = requests
        .iter()
        .map(|r| r["method"].as_str().unwrap())
        .collect();
    assert_eq!(
        &methods[..4],
        [
            "initialize",
            "notifications/initialized",
            "tools/list",
            "tools/call"
        ]
    );
    assert_eq!(requests[0]["id"], 1);
    assert!(requests[1].get("id").is_none());
    assert_eq!(requests[2]["id"], 2);
    assert_eq!(requests[3]["id"], 3);
    assert_eq!(
        requests[3]["params"],
        json!({"name":"learning_capabilities","arguments":{}})
    );
    assert!(requests[4].get("id").is_none());
    assert_eq!(requests[5]["id"], 4);
    assert_eq!(requests[6]["id"], json!(u64::MAX - 1));
}

#[tokio::test]
async fn rejected_capability_stops_before_selection_and_drops_owned_children() {
    let fixture = Fixture::new();
    let error = fixture
        .start("bad-capabilities")
        .await
        .err()
        .expect("incompatible startup succeeded");
    assert!(error.to_string().contains("source coverage is unavailable"));
    fixture.stopped().await;
    let requests = fixture.requests();
    assert_eq!(requests.len(), 4);
    assert_eq!(requests[3]["params"]["name"], "learning_capabilities");
}

#[tokio::test]
async fn complete_large_frames_and_notification_sequences_are_accepted() {
    let fixture = Fixture::new();
    let mut client = fixture.start("large-notifications").await.unwrap();
    let result = client
        .tool("get_experience", json!({"padding":"x".repeat(1048577)}))
        .await
        .unwrap();
    assert_eq!(result["revision"], 1);
    drop(client);
    fixture.stopped().await;
}
