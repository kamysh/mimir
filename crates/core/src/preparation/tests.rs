#[allow(dead_code)]
#[path = "../../../../tests/support/isolation.rs"]
mod isolation;

use super::*;
use crate::{
    config::{Config, EmbeddingBackend, EmbeddingsConfig},
    db,
    embed::{EmbedFuture, EmbeddingCancellation, EmbeddingProvider, OwnedEmbeddingBackend},
    graph::MemoryType,
    learning::{IndependentBasis, IndependentProvenance},
    MimirService,
};
use anyhow::Result;
use serde_json::json;
use std::sync::Mutex;
use uuid::Uuid;

struct FixedProvider(Mutex<Option<Result<Vec<Vec<f32>>>>>);

#[test]
fn operation_provider_identity_survives_credentials_and_execution_changes() {
    let mut configured = EmbeddingsConfig {
        backend: EmbeddingBackend::Voyage,
        model: "same-model".into(),
        api_key: Some("first-private-key".into()),
        batch_size: 0,
        cache_dir: None,
    };
    let original = operation_settings(Some(&configured));
    validate_operation_settings(&original).unwrap();
    for invalid in [
        json!({}),
        json!({"embeddings":null,"api_key":"secret"}),
        json!({"embeddings":{"backend":"voyage","model":"m","input_type":"document","truncation":true}}),
        json!({"embeddings":{"backend":"local","model":"unselected"}}),
    ] {
        assert!(validate_operation_settings(&invalid).is_err());
    }
    configured.api_key = Some("rotated-private-key".into());
    configured.cache_dir = Some("/different/execution-cache".into());
    configured.batch_size = 17;
    assert_eq!(original, operation_settings(Some(&configured)));
    assert!(!original.to_string().contains("private-key"));
    configured.model = "different-model".into();
    assert_ne!(original, operation_settings(Some(&configured)));
    configured.backend = EmbeddingBackend::Local;
    let local = operation_settings(Some(&configured));
    configured.model = "ignored-by-the-local-provider".into();
    assert_eq!(local, operation_settings(Some(&configured)));
}

#[tokio::test]
async fn token_cancellation_stops_owned_backfill_without_an_owner_row() -> Result<()> {
    use std::sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    };
    use tokio::sync::oneshot;
    struct DropSignal(Option<oneshot::Sender<()>>);
    impl Drop for DropSignal {
        fn drop(&mut self) {
            if let Some(sender) = self.0.take() {
                let _ = sender.send(());
            }
        }
    }
    struct Blocked {
        started: Mutex<Option<oneshot::Sender<()>>>,
        dropped: Mutex<Option<oneshot::Sender<()>>>,
        calls: Arc<AtomicUsize>,
    }
    impl EmbeddingProvider for Blocked {
        fn embed<'a>(&'a self, _: &'a [String], _: EmbeddingCancellation) -> EmbedFuture<'a> {
            Box::pin(async move {
                self.calls.fetch_add(1, Ordering::SeqCst);
                let _drop = DropSignal(self.dropped.lock().unwrap().take());
                self.started
                    .lock()
                    .unwrap()
                    .take()
                    .unwrap()
                    .send(())
                    .unwrap();
                std::future::pending().await
            })
        }
    }
    let (service, project) = service(None).await?;
    let belief = isolation::seed_belief_in_project(
        "existing backfill target explicitly cancelled",
        0.7,
        0.5,
        &project,
        MemoryType::Fact,
    )
    .await?;
    let before = serde_json::to_value(service.get_belief(belief.id).await?)?;
    let cfg = isolation::fixture().database_config();
    let client = db::connect(&cfg).await?;
    let key: String = client
        .query_one("SELECT gen_random_uuid()::text", &[])
        .await?
        .get(0);
    let token = service.reserve_operation(&key).await?.operation_token;
    let (started_tx, started_rx) = oneshot::channel();
    let (dropped_tx, dropped_rx) = oneshot::channel();
    let calls = Arc::new(AtomicUsize::new(0));
    let provider = Arc::new(OwnedEmbeddingBackend::for_test(Box::new(Blocked {
        started: Mutex::new(Some(started_tx)),
        dropped: Mutex::new(Some(dropped_tx)),
        calls: calls.clone(),
    })));
    let owner = Arc::new(service);
    let task = {
        let owner = owner.clone();
        let provider = provider.clone();
        let belief = belief.clone();
        tokio::spawn(async move {
            owner
                .embed_existing_belief(&provider, &belief, Some(token))
                .await
        })
    };
    started_rx.await?;
    assert!(matches!(
        owner.record_operation_cancellation(token).await?,
        crate::store::CancellationDecision::Recorded(_)
    ));
    let error = task.await?.unwrap_err();
    assert!(error
        .downcast_ref::<PreparationRequired>()
        .unwrap()
        .to_string()
        .contains("explicitly cancelled"));
    dropped_rx.await?;
    assert!(owner
        .embed_existing_belief(&provider, &belief, Some(token))
        .await
        .is_err());
    assert_eq!(
        calls.load(Ordering::SeqCst),
        1,
        "a cancelled token cannot start another provider job"
    );
    assert_eq!(
        serde_json::to_value(owner.get_belief(belief.id).await?)?,
        before
    );
    assert!(!owner.list_embedded_belief_ids().await?.contains(&belief.id));
    Ok(())
}

impl EmbeddingProvider for FixedProvider {
    fn embed<'a>(
        &'a self,
        _: &'a [String],
        cancellation: EmbeddingCancellation,
    ) -> EmbedFuture<'a> {
        Box::pin(async move {
            cancellation.check()?;
            self.0.lock().unwrap().take().unwrap()
        })
    }
}

#[tokio::test]
async fn backfill_missing_backend_and_invalid_vectors_preserve_the_stored_belief() -> Result<()> {
    use crate::validation::{Code, Segment};

    for (response, expected_code) in [
        (None, Code::MissingEvidence),
        (Some(Ok(vec![])), Code::MalformedInput),
        (Some(Ok(vec![vector(0), vector(1)])), Code::MalformedInput),
        (Some(Ok(vec![vec![]])), Code::InvalidNumber),
        (Some(Ok(vec![vec![0.0; 768]])), Code::InvalidNumber),
        (Some(Ok(vec![vec![f32::NAN; 768]])), Code::InvalidNumber),
        (
            Some(Ok(vec![vec![f32::INFINITY; 768]])),
            Code::InvalidNumber,
        ),
    ] {
        let (service, project) = service(response).await?;
        let belief = isolation::seed_belief_in_project(
            "existing belief waiting for its embedding",
            0.7,
            0.5,
            &project,
            MemoryType::Fact,
        )
        .await?;
        let before = serde_json::to_value(service.get_belief(belief.id).await?)?;
        let result = service.embed_and_store_belief(&belief).await;
        let after = serde_json::to_value(service.get_belief(belief.id).await?)?;
        let client = db::connect(&isolation::fixture().database_config()).await?;
        let count: i64 = client
            .query_one(
                "SELECT count(*) FROM public.belief_embeddings WHERE belief_id=$1",
                &[&belief.id],
            )
            .await?
            .get(0);
        service.delete_project(&project).await?;

        let error = result.expect_err("absent or unusable embeddings cannot report success");
        let required = error
            .downcast_ref::<PreparationRequired>()
            .expect("a pre-write embedding problem must offer a typed user decision");
        let issue = &required.correction().issues()[0];
        assert_eq!(issue.fault().code, expected_code);
        assert_eq!(issue.fault().path, vec![Segment::Key("embeddings".into())]);
        assert!(issue.suggested_correction().contains("user"));
        assert!(issue.suggested_correction().contains("cancel"));
        assert!(issue.suggested_correction().contains("Do not"));
        assert_eq!(count, 0, "a rejected result must not create a vector");
        assert_eq!(after, before, "backfill must preserve the stored belief");
    }
    Ok(())
}

#[tokio::test]
async fn backfill_success_means_the_requested_vector_was_stored() -> Result<()> {
    let expected = vector(3);
    let (service, project) = service(Some(Ok(vec![expected.clone()]))).await?;
    let belief = isolation::seed_belief_in_project(
        "existing belief with a usable backfill result",
        0.7,
        0.5,
        &project,
        MemoryType::Fact,
    )
    .await?;
    let before = serde_json::to_value(service.get_belief(belief.id).await?)?;
    let result = service.embed_and_store_belief(&belief).await;
    let after = serde_json::to_value(service.get_belief(belief.id).await?)?;
    let client = db::connect(&isolation::fixture().database_config()).await?;
    let stored = client
        .query_opt(
            "SELECT embedding FROM public.belief_embeddings WHERE belief_id=$1",
            &[&belief.id],
        )
        .await?
        .map(|row| row.get::<_, pgvector::Vector>(0).to_vec());
    service.delete_project(&project).await?;

    result?;
    assert_eq!(stored, Some(expected));
    assert_eq!(after, before);
    Ok(())
}

#[tokio::test]
async fn backfill_provider_failure_neither_claims_success_nor_replaces_a_vector() -> Result<()> {
    for previous in [None, Some(vector(5))] {
        let (service, project) = service(Some(Err(anyhow::anyhow!(
            "controlled backfill provider failure: keep the complete cause"
        ))))
        .await?;
        let belief = isolation::seed_belief_in_project(
            "existing belief whose provider fails",
            0.7,
            0.5,
            &project,
            MemoryType::Fact,
        )
        .await?;
        if let Some(vector) = &previous {
            service
                .store
                .insert_belief_embedding(belief.id, vector)
                .await?;
        }
        let before = serde_json::to_value(service.get_belief(belief.id).await?)?;
        let result = service.embed_and_store_belief(&belief).await;
        let after = serde_json::to_value(service.get_belief(belief.id).await?)?;
        let client = db::connect(&isolation::fixture().database_config()).await?;
        let stored = client
            .query_opt(
                "SELECT embedding FROM public.belief_embeddings WHERE belief_id=$1",
                &[&belief.id],
            )
            .await?
            .map(|row| row.get::<_, pgvector::Vector>(0).to_vec());
        service.delete_project(&project).await?;

        let error = result.expect_err("provider failure cannot report a completed backfill");
        assert!(error
            .to_string()
            .contains("controlled backfill provider failure: keep the complete cause"));
        assert_eq!(
            stored, previous,
            "failed work must preserve the prior vector"
        );
        assert_eq!(after, before);
    }
    Ok(())
}

#[tokio::test]
async fn deleted_backfill_target_does_not_start_embedding() -> Result<()> {
    struct CountCalls(std::sync::Arc<std::sync::atomic::AtomicUsize>);
    impl EmbeddingProvider for CountCalls {
        fn embed<'a>(&'a self, _: &'a [String], _: EmbeddingCancellation) -> EmbedFuture<'a> {
            Box::pin(async move {
                self.0.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                Ok(vec![vector(0)])
            })
        }
    }
    let calls = std::sync::Arc::new(std::sync::atomic::AtomicUsize::new(0));
    let (mut service, project) = service(None).await?;
    let belief = isolation::seed_belief_in_project(
        "deleted before backfill starts",
        0.7,
        0.5,
        &project,
        MemoryType::Fact,
    )
    .await?;
    service.delete_belief(belief.id).await?;
    service.embeddings = Some(OwnedEmbeddingBackend::for_test(Box::new(CountCalls(
        calls.clone(),
    ))));
    let result = service.embed_and_store_belief(&belief).await;
    let observed = calls.load(std::sync::atomic::Ordering::SeqCst);
    service.delete_project(&project).await?;
    assert!(result
        .unwrap_err()
        .is::<crate::store::BeliefEmbeddingTargetMissing>());
    assert_eq!(observed, 0, "deleted work must not start a backend call");
    Ok(())
}

#[tokio::test]
async fn backfill_revocation_terminates_only_its_blocked_worker() -> Result<()> {
    use std::os::unix::fs::PermissionsExt;
    use tokio::io::{AsyncBufReadExt, AsyncReadExt, AsyncWriteExt, BufReader};
    for delete_project in [false, true] {
        let (seed, project) = service(None).await?;
        let other_project = format!("{project}-other");
        let target = isolation::seed_belief_in_project(
            "backfill target",
            0.7,
            0.5,
            &project,
            MemoryType::Fact,
        )
        .await?;
        let survivor = isolation::seed_belief_in_project(
            "independent backfill target",
            0.7,
            0.5,
            &other_project,
            MemoryType::Fact,
        )
        .await?;
        let directory = std::env::temp_dir().join(&project);
        std::fs::create_dir(&directory)?;
        std::fs::set_permissions(&directory, std::fs::Permissions::from_mode(0o700))?;
        let socket = directory.join("ready.sock");
        let listener = tokio::net::UnixListener::bind(&socket)?;
        let program = directory.join("blocked-worker.py");
        std::fs::write(&program, format!(
            "#!/usr/bin/env python3\nimport sys,json,socket,os\njson.loads(sys.stdin.readline())\nprint(json.dumps({{'status':'started','version':1}}),flush=True)\ns=socket.socket(socket.AF_UNIX)\ns.connect({:?})\ns.sendall((str(os.getpid())+'\\n').encode())\ns.recv(1)\nv=[0.0]*768\nv[9]=1.0\nprint(json.dumps({{'status':'complete','vectors':[v]}}),flush=True)\nsys.stdin.read()\n", socket.to_str().unwrap()))?;
        std::fs::set_permissions(&program, std::fs::Permissions::from_mode(0o700))?;
        let cfg = Config {
            database: isolation::fixture().database_config(),
            embeddings: Some(EmbeddingsConfig {
                backend: EmbeddingBackend::Local,
                model: String::new(),
                api_key: None,
                batch_size: 0,
                cache_dir: Some(directory.join("model-cache").display().to_string()),
            }),
            llm: None,
            judge: None,
            email: None,
            retirement: None,
        };
        let first =
            std::sync::Arc::new(MimirService::connect_with_worker(&cfg, program.clone()).await?);
        let second = std::sync::Arc::new(MimirService::connect_with_worker(&cfg, program).await?);
        let first_task = {
            let owner = first.clone();
            let target = target.clone();
            tokio::spawn(async move { owner.embed_and_store_belief(&target).await })
        };
        let (first_socket, _) = listener.accept().await?;
        let mut first_socket = BufReader::new(first_socket);
        let mut first_pid = String::new();
        first_socket.read_line(&mut first_pid).await?;
        let second_task = {
            let owner = second.clone();
            let survivor = survivor.clone();
            tokio::spawn(async move { owner.embed_and_store_belief(&survivor).await })
        };
        let (second_socket, _) = listener.accept().await?;
        let mut second_socket = BufReader::new(second_socket);
        let mut second_pid = String::new();
        second_socket.read_line(&mut second_pid).await?;
        if delete_project {
            assert_eq!(seed.delete_project(&project).await?, 1);
        } else {
            assert!(seed.delete_belief(target.id).await?);
        }
        let stopped = first_task.await?;
        let mut byte = [0];
        assert_eq!(
            first_socket.read(&mut byte).await?,
            0,
            "cancelled worker is still running"
        );
        #[cfg(target_os = "linux")]
        {
            assert!(!std::path::Path::new(&format!("/proc/{}", first_pid.trim())).exists());
            assert!(std::path::Path::new(&format!("/proc/{}", second_pid.trim())).exists());
        }
        second_socket.write_all(b"x").await?;
        let completed = second_task.await?;
        let embedded = seed.list_embedded_belief_ids().await?;
        seed.delete_project(&project).await?;
        seed.delete_project(&other_project).await?;
        drop(first);
        drop(second);
        std::fs::remove_dir_all(directory)?;
        assert!(stopped
            .unwrap_err()
            .is::<crate::store::BeliefEmbeddingTargetMissing>());
        completed?;
        assert!(!embedded.contains(&target.id));
        assert!(
            embedded.contains(&survivor.id),
            "unrelated backfill was cancelled"
        );
    }
    Ok(())
}

#[tokio::test]
async fn project_revocation_terminates_only_its_blocked_worker() -> Result<()> {
    use std::os::unix::fs::PermissionsExt;
    use tokio::io::{AsyncBufReadExt, AsyncWriteExt, BufReader};
    let (seed, project) = service(None).await?;
    let other_project = format!("{project}-other");
    passage(&seed, Some(&other_project), 9, "worker-survives").await?;
    let directory = std::env::temp_dir().join(&project);
    std::fs::create_dir(&directory)?;
    std::fs::set_permissions(&directory, std::fs::Permissions::from_mode(0o700))?;
    let socket = directory.join("ready.sock");
    let listener = tokio::net::UnixListener::bind(&socket)?;
    let program = directory.join("blocked-worker.py");
    std::fs::write(&program, format!(
        "#!/usr/bin/env python3\nimport sys,json,socket,os\nrequest=json.loads(sys.stdin.readline())\nprint(json.dumps({{'status':'started','version':1}}),flush=True)\ns=socket.socket(socket.AF_UNIX)\ns.connect({:?})\ns.sendall((str(os.getpid())+'\\n').encode())\ns.recv(1)\nv=[0.0]*768\nv[9]=1.0\nprint(json.dumps({{'status':'complete','vectors':[v]}}),flush=True)\nsys.stdin.read()\n", socket.to_str().unwrap()))?;
    std::fs::set_permissions(&program, std::fs::Permissions::from_mode(0o700))?;
    let mut cfg = Config {
        database: isolation::fixture().database_config(),
        embeddings: Some(EmbeddingsConfig {
            backend: EmbeddingBackend::Local,
            model: String::new(),
            api_key: None,
            batch_size: 0,
            cache_dir: Some(directory.join("model-cache").display().to_string()),
        }),
        llm: None,
        judge: None,
        email: None,
        retirement: None,
    };
    let first =
        std::sync::Arc::new(MimirService::connect_with_worker(&cfg, program.clone()).await?);
    let second = std::sync::Arc::new(MimirService::connect_with_worker(&cfg, program).await?);
    let first_task = {
        let service = first.clone();
        let project = project.clone();
        tokio::spawn(async move {
            service
                .prepare_belief(
                    "first complete belief",
                    0.6,
                    0.4,
                    Some(&project),
                    MemoryType::Fact,
                    None,
                )
                .await
        })
    };
    let (first_control, _) = listener.accept().await?;
    let mut first_control = BufReader::new(first_control);
    let mut first_pid = String::new();
    first_control.read_line(&mut first_pid).await?;
    let second_task = {
        let service = second.clone();
        let project = other_project.clone();
        tokio::spawn(async move {
            service
                .prepare_belief(
                    "second complete belief",
                    0.6,
                    0.4,
                    Some(&project),
                    MemoryType::Fact,
                    None,
                )
                .await
        })
    };
    let (second_control, _) = listener.accept().await?;
    let mut second_control = BufReader::new(second_control);
    let mut second_pid = String::new();
    second_control.read_line(&mut second_pid).await?;
    cfg.embeddings = None;
    let deletion = MimirService::connect(&cfg).await?;
    assert_eq!(deletion.delete_project(&project).await?, 0);
    let error = first_task.await?.unwrap_err();
    let report = error
        .downcast_ref::<PreparationRequired>()
        .expect("revocation opens the user dialog");
    assert!(report.to_string().contains("ownership was revoked"));
    #[cfg(target_os = "linux")]
    {
        assert!(!std::path::Path::new(&format!("/proc/{}", first_pid.trim())).exists());
        assert!(std::path::Path::new(&format!("/proc/{}", second_pid.trim())).exists());
    }
    assert!(seed.list_beliefs(Some(&project)).await?.is_empty());
    second_control.write_all(b"x").await?;
    let prepared = second_task.await??;
    let published = second.publish_prepared_belief(&prepared).await?;
    assert_eq!(published.project.as_deref(), Some(other_project.as_str()));
    drop(first);
    drop(second);
    std::fs::remove_dir_all(directory)?;
    Ok(())
}

fn vector(axis: usize) -> Vec<f32> {
    let mut vector = vec![0.0; 768];
    vector[axis] = 1.0;
    vector
}

async fn review_request(service: &MimirService, project: &str) -> Result<crate::learning::Review> {
    use crate::learning::{Experience, ObservationSource, Outcome};
    let id: Uuid = db::connect(&isolation::fixture().database_config())
        .await?
        .query_one("SELECT gen_random_uuid()", &[])
        .await?
        .get(0);
    let source = Experience {
        id,
        project: project.into(),
        context: "review preparation".into(),
        action: "compare the observed outcome".into(),
        outcome: Outcome::Success,
        source: ObservationSource::ToolResult,
        evidence: vec!["complete test receipt".into()],
        belief_ids: vec![],
        pattern_id: None,
        learning_items: vec![],
        source_records: vec![],
    };
    service.record_experience(&source, 0).await?;
    Ok(serde_json::from_value(
        json!({"experience_id":id,"experience_revision":1,
        "reviewer":"preparation test","rationale":"checked independent fixture support",
        "candidates":[{"kind":"pattern","key":"procedure","situation":"review work","approach":"prepare first"},
            {"kind":"belief","key":"lesson","content":"the complete supported lesson","memory_type":"Fact"}]}),
    )?)
}

#[tokio::test]
async fn experience_evidence_cannot_replace_indexed_document_support_in_review() -> Result<()> {
    let (service, project) = service(Some(Ok(vec![vector(13)]))).await?;
    let review = review_request(&service, &project).await?;
    let error = service.review_experience(&review, 0).await.unwrap_err();
    let report = error.downcast_ref::<PreparationRequired>().unwrap();
    let issue = &report.correction().issues()[0];
    assert_eq!(
        issue.fault().path,
        vec![
            Segment::Key("review".into()),
            Segment::Key("candidates".into()),
            Segment::Index(1),
            Segment::Key("content".into())
        ]
    );
    assert!(issue.fault().message.contains("indexed document"));
    assert_eq!(
        service
            .get_experience(review.experience_id)
            .await?
            .unwrap()
            .reviewed_revision,
        0
    );
    assert!(service.list_beliefs(Some(&project)).await?.is_empty());
    Ok(())
}

#[tokio::test]
async fn service_review_publishes_complete_candidates_and_acknowledgement_together() -> Result<()> {
    let (service, project) = service(Some(Ok(vec![vector(14)]))).await?;
    let chunk = passage(&service, Some(&project), 14, "service-review-support").await?;
    let review = review_request(&service, &project).await?;
    let state = service.review_experience(&review, 0).await?;
    let id = state.candidate_ids["lesson"];
    assert_eq!(state.reviewed_revision, 1);
    assert!(service
        .get_pattern(state.candidate_ids["procedure"])
        .await?
        .is_some());
    assert_eq!(
        service.evidence_for_belief(id, None).await?[0].chunk_id,
        chunk.id
    );
    let client = db::connect(&isolation::fixture().database_config()).await?;
    assert_eq!(
        client
            .query_one(
                "SELECT count(*) FROM belief_embeddings WHERE belief_id=$1",
                &[&id]
            )
            .await?
            .get::<_, i64>(0),
        1
    );
    assert_eq!(
        service.review_experience(&review, 0).await?.candidate_ids,
        state.candidate_ids
    );
    Ok(())
}

struct SequenceProvider(Mutex<std::collections::VecDeque<Result<Vec<Vec<f32>>>>>);
impl EmbeddingProvider for SequenceProvider {
    fn embed<'a>(
        &'a self,
        _: &'a [String],
        cancellation: EmbeddingCancellation,
    ) -> EmbedFuture<'a> {
        Box::pin(async move {
            cancellation.check()?;
            self.0
                .lock()
                .unwrap()
                .pop_front()
                .expect("one response per declared candidate")
        })
    }
}

#[tokio::test]
async fn a_later_candidate_preparation_failure_leaves_the_whole_review_pending() -> Result<()> {
    let (mut service, project) = service(Some(Ok(vec![vector(15)]))).await?;
    passage(&service, Some(&project), 15, "first-candidate-support").await?;
    service.embeddings = Some(OwnedEmbeddingBackend::for_test(Box::new(SequenceProvider(
        Mutex::new(
            [
                Ok(vec![vector(15)]),
                Err(anyhow::anyhow!("second candidate preparation rejected")),
            ]
            .into_iter()
            .collect(),
        ),
    ))));
    let mut review = review_request(&service, &project).await?;
    review.candidates.push(crate::learning::Candidate::Belief {
        key: "second".into(),
        content: "another complete lesson".into(),
        memory_type: MemoryType::Fact,
    });
    let error = service.review_experience(&review, 0).await.unwrap_err();
    assert!(error
        .downcast_ref::<PreparationRequired>()
        .unwrap()
        .to_string()
        .contains("candidate second at index 2"));
    assert!(service.list_beliefs(Some(&project)).await?.is_empty());
    assert_eq!(
        service
            .get_experience(review.experience_id)
            .await?
            .unwrap()
            .reviewed_revision,
        0
    );
    let client = db::connect(&isolation::fixture().database_config()).await?;
    assert_eq!(
        client
            .query_one(
                "SELECT count(*) FROM mimir_review_candidates WHERE experience_id=$1",
                &[&review.experience_id]
            )
            .await?
            .get::<_, i64>(0),
        0
    );
    Ok(())
}

#[tokio::test]
async fn review_without_required_backend_publishes_neither_candidates_nor_acknowledgement(
) -> Result<()> {
    let (service, project) = service(None).await?;
    let review = review_request(&service, &project).await?;
    let error = service.review_experience(&review, 0).await.unwrap_err();
    let report = error
        .downcast_ref::<PreparationRequired>()
        .expect("review must open the user dialog");
    assert!(report.to_string().contains("candidate lesson at index 1"));
    assert_eq!(
        service
            .get_experience(review.experience_id)
            .await?
            .unwrap()
            .reviewed_revision,
        0
    );
    assert!(service.list_beliefs(Some(&project)).await?.is_empty());
    let client = db::connect(&isolation::fixture().database_config()).await?;
    assert_eq!(
        client
            .query_one(
                "SELECT count(*) FROM mimir_review_candidates WHERE experience_id=$1",
                &[&review.experience_id]
            )
            .await?
            .get::<_, i64>(0),
        0
    );
    Ok(())
}

#[tokio::test]
async fn prepared_review_rolls_back_all_publications_and_replays_without_embedding() -> Result<()> {
    let (service, project) = service(Some(Ok(vec![vector(10)]))).await?;
    let chunk = passage(&service, Some(&project), 10, "review-atomic-support").await?;
    let review = review_request(&service, &project).await?;
    let prepared = service
        .prepare_belief(
            "the complete supported lesson",
            0.5,
            0.0,
            Some(&project),
            MemoryType::Fact,
            None,
        )
        .await?;
    let id = prepared.belief.id;
    let mut values = std::collections::HashMap::new();
    values.insert("lesson".into(), prepared);
    let client = db::connect(&isolation::fixture().database_config()).await?;
    let suffix = id.simple();
    let name = format!("reject_review_{suffix}");
    client.batch_execute(&format!("CREATE FUNCTION {name}() RETURNS trigger LANGUAGE plpgsql AS $$ BEGIN IF NEW.experience_id='{experience}'::uuid THEN RAISE EXCEPTION 'controlled review receipt refusal'; END IF; RETURN NEW; END $$; CREATE TRIGGER {name} BEFORE INSERT ON mimir_review_versions FOR EACH ROW EXECUTE FUNCTION {name}();", experience=review.experience_id)).await?;
    let failed = service
        .store
        .review_experience_prepared(&review, 0, &values)
        .await;
    client
        .batch_execute(&format!(
            "DROP TRIGGER {name} ON mimir_review_versions; DROP FUNCTION {name}();"
        ))
        .await?;
    assert!(failed.is_err());
    no_publication(&service, id).await?;
    assert_eq!(
        service
            .get_experience(review.experience_id)
            .await?
            .unwrap()
            .reviewed_revision,
        0
    );
    assert_eq!(
        client
            .query_one(
                "SELECT count(*) FROM mimir_review_candidates WHERE experience_id=$1",
                &[&review.experience_id]
            )
            .await?
            .get::<_, i64>(0),
        0
    );
    let first = service
        .store
        .review_experience_prepared(&review, 0, &values)
        .await?;
    assert_eq!(first.candidate_ids["lesson"], id);
    assert_eq!(first.reviewed_revision, 1);
    assert!(service.get_belief(id).await?.is_some());
    assert_eq!(
        client
            .query_one(
                "SELECT count(*) FROM belief_embeddings WHERE belief_id=$1",
                &[&id]
            )
            .await?
            .get::<_, i64>(0),
        1
    );
    assert_eq!(
        service.evidence_for_belief(id, None).await?[0].chunk_id,
        chunk.id
    );
    // The injected provider has already consumed its only answer: any second
    // embedding attempt would panic instead of passing this replay check.
    let replay = service.review_experience(&review, 0).await?;
    assert_eq!(replay.candidate_ids, first.candidate_ids);
    assert_eq!(replay.review_revision, first.review_revision);
    Ok(())
}

#[tokio::test]
async fn source_change_during_preparation_prevents_complete_review_publication() -> Result<()> {
    let (service, project) = service(Some(Ok(vec![vector(12)]))).await?;
    passage(&service, Some(&project), 12, "stale-review-support").await?;
    let review = review_request(&service, &project).await?;
    let prepared = service
        .prepare_belief(
            "the complete supported lesson",
            0.5,
            0.0,
            Some(&project),
            MemoryType::Fact,
            None,
        )
        .await?;
    let id = prepared.belief.id;
    let mut changed = service
        .get_experience(review.experience_id)
        .await?
        .unwrap()
        .experience;
    changed
        .evidence
        .push("source corrected during preparation".into());
    service.record_experience(&changed, 1).await?;
    let mut values = std::collections::HashMap::new();
    values.insert("lesson".into(), prepared);
    assert!(service
        .store
        .review_experience_prepared(&review, 0, &values)
        .await
        .is_err());
    no_publication(&service, id).await?;
    assert_eq!(
        service
            .get_experience(review.experience_id)
            .await?
            .unwrap()
            .reviewed_revision,
        0
    );
    Ok(())
}

async fn service(response: Option<Result<Vec<Vec<f32>>>>) -> Result<(MimirService, String)> {
    let cfg = Config {
        database: isolation::fixture().database_config(),
        embeddings: response.as_ref().map(|_| EmbeddingsConfig {
            backend: EmbeddingBackend::Local,
            model: String::new(),
            api_key: None,
            batch_size: 0,
            cache_dir: None,
        }),
        llm: None,
        judge: None,
        email: None,
        retirement: None,
    };
    let backend = response.map(|value| {
        OwnedEmbeddingBackend::for_test(Box::new(FixedProvider(Mutex::new(Some(value)))))
    });
    let service = MimirService::connect_with_embeddings(&cfg, backend).await?;
    let identity: Uuid = db::connect(&cfg.database)
        .await?
        .query_one("SELECT gen_random_uuid()", &[])
        .await?
        .get(0);
    Ok((service, format!("required-preparation-{identity}")))
}

async fn passage(
    service: &MimirService,
    project: Option<&str>,
    axis: usize,
    suffix: &str,
) -> Result<DocumentChunk> {
    let cfg = isolation::fixture().database_config();
    let id: Uuid = db::connect(&cfg)
        .await?
        .query_one("SELECT gen_random_uuid()", &[])
        .await?
        .get(0);
    let chunk = DocumentChunk::with_id(
        id,
        format!("/required-preparation/{id}-{suffix}.md"),
        vec!["support".into()],
        format!(
            "Complete supporting passage {suffix}: {}",
            "π indexed evidence; ".repeat(150)
        ),
        None,
        project.map(str::to_owned),
    );
    service.store.insert_document_chunk(&chunk).await?;
    service
        .store
        .insert_chunk_embedding(id, &vector(axis))
        .await?;
    Ok(chunk)
}

async fn no_publication(service: &MimirService, id: Uuid) -> Result<()> {
    assert!(service.get_belief(id).await?.is_none());
    let client = db::connect(&isolation::fixture().database_config()).await?;
    let count: i64 = client
        .query_one(
            "SELECT count(*) FROM public.belief_embeddings WHERE belief_id=$1",
            &[&id],
        )
        .await?
        .get(0);
    assert_eq!(count, 0);
    assert!(service.evidence_for_belief(id, None).await?.is_empty());
    Ok(())
}

// A private fixture allocation for the token-linked publication path. Public
// callers cannot construct PreparedBelief or choose its owner identity.
async fn linked_preparation() -> Result<(MimirService, String, Uuid, PreparedBelief)> {
    let (service, project) = service(None).await?;
    let document = passage(&service, Some(&project), 0, "operation cancellation").await?;
    let client = db::connect(&isolation::fixture().database_config()).await?;
    let request_key: String = client
        .query_one("SELECT gen_random_uuid()::text", &[])
        .await?
        .get(0);
    let token = service
        .reserve_operation(&request_key)
        .await?
        .operation_token;
    let owner = client.query_one(
        "INSERT INTO mimir_embedding_owners(project,operation_token) VALUES($1,$2) RETURNING owner_token,reserved_at",
        &[&project,&token],
    ).await?;
    let mut belief = crate::graph::Belief::new_in_project(
        "complete token-owned belief".into(),
        0.7,
        0.5,
        project.clone(),
    )?;
    belief.id = owner.get(0);
    belief.created_at = owner.get(1);
    belief.last_activated_at = belief.created_at;
    belief.decay_accounted_at = belief.created_at;
    let prepared = PreparedBelief {
        belief,
        provenance: Some(IndependentProvenance {
            basis: IndependentBasis::UserInstruction,
            reference: "explicit independent fixture instruction".into(),
        }),
        vector: vector(0),
        support: vec![SupportingPassage {
            chunk: document,
            weight: crate::graph::Probability::new(1.0)?,
        }],
    };
    Ok((service, project, token, prepared))
}

#[tokio::test]
async fn cancelled_operation_cannot_publish_its_prepared_belief() -> Result<()> {
    let (service, project, token, prepared) = linked_preparation().await?;
    assert!(matches!(
        service.record_operation_cancellation(token).await?,
        crate::store::CancellationDecision::Recorded(_)
    ));
    let error = service
        .publish_prepared_belief(&prepared)
        .await
        .unwrap_err();
    assert!(error.downcast_ref::<PreparationRequired>().is_some());
    no_publication(&service, prepared.belief.id).await?;
    service.delete_project(&project).await?;
    Ok(())
}

#[tokio::test]
async fn cancellation_preserves_a_previously_committed_prepared_belief() -> Result<()> {
    let (service, project, token, prepared) = linked_preparation().await?;
    let published = service.publish_prepared_belief(&prepared).await?;
    let before = serde_json::to_value(service.get_belief(published.id).await?)?;
    assert!(matches!(
        service.record_operation_cancellation(token).await?,
        crate::store::CancellationDecision::Recorded(_)
    ));
    assert_eq!(
        serde_json::to_value(service.get_belief(published.id).await?)?,
        before
    );
    assert!(!service
        .evidence_for_belief(published.id, None)
        .await?
        .is_empty());
    service.delete_project(&project).await?;
    Ok(())
}

#[tokio::test]
async fn missing_backend_and_failed_embedding_publish_nothing() -> Result<()> {
    for response in [
        None,
        Some(Err(anyhow::anyhow!(
            "controlled provider failure: complete explanation"
        ))),
    ] {
        let (service, project) = service(response).await?;
        let result = service
            .add_belief_in_project(
                "a belief requiring preparation",
                0.7,
                0.5,
                &project,
                MemoryType::Fact,
            )
            .await;
        let stored = service.list_beliefs(Some(&project)).await?;
        service.delete_project(&project).await?;
        let error = result.unwrap_err();
        let required = error
            .downcast_ref::<PreparationRequired>()
            .expect("preparation returns a decision, not a generic tool failure");
        let report = serde_json::to_value(required.correction())?;
        assert_eq!(report["status"], "needs_input");
        assert_eq!(report["business_changes"], "none");
        assert_eq!(report["issues"][0]["fault"]["path"], json!(["embeddings"]));
        assert!(stored.is_empty());
    }
    Ok(())
}

#[tokio::test]
async fn invalid_vectors_and_missing_indexed_support_request_a_decision() -> Result<()> {
    for vectors in [
        vec![],
        vec![vec![]],
        vec![vector(0), vector(0)],
        vec![vec![0.0; 768]],
        vec![vec![f32::NAN; 768]],
        vec![vector(0)],
    ] {
        let (service, project) = service(Some(Ok(vectors))).await?;
        let other = format!("{project}-other");
        passage(&service, Some(&other), 0, "not this project").await?;
        let result = service
            .add_belief_in_project(
                "no supported publication",
                0.7,
                0.5,
                &project,
                MemoryType::Fact,
            )
            .await;
        let stored = service.list_beliefs(Some(&project)).await?;
        service.delete_project(&other).await?;
        service.delete_project(&project).await?;
        assert!(result.unwrap_err().is::<PreparationRequired>());
        assert!(stored.is_empty());
    }
    Ok(())
}

#[tokio::test]
async fn preparation_has_no_belief_and_publication_commits_complete_data() -> Result<()> {
    let (service, project) = service(Some(Ok(vec![vector(0)]))).await?;
    let first = passage(&service, Some(&project), 0, "first complete support").await?;
    let second = passage(&service, Some(&project), 0, "second complete support").await?;
    let origin = IndependentProvenance {
        basis: IndependentBasis::UserInstruction,
        reference: "explicit independent test instruction".into(),
    };
    let prepared = service
        .prepare_belief(
            "complete grounded belief",
            0.7,
            0.5,
            Some(&project),
            MemoryType::Fact,
            Some(&origin),
        )
        .await?;
    no_publication(&service, prepared.belief.id).await?;
    assert_eq!(prepared.support.len(), 2);
    assert!(prepared
        .support
        .iter()
        .any(|support| support.chunk == first));
    assert!(prepared
        .support
        .iter()
        .any(|support| support.chunk == second));
    let published = service.publish_prepared_belief(&prepared).await?;
    let stored = service.get_belief(published.id).await?.unwrap();
    let evidence = service.evidence_for_belief(published.id, None).await?;
    let client = db::connect(&isolation::fixture().database_config()).await?;
    let vector: pgvector::Vector = client
        .query_one(
            "SELECT embedding FROM public.belief_embeddings WHERE belief_id=$1",
            &[&published.id],
        )
        .await?
        .get(0);
    let explanation = service
        .explain_belief(published.id, 0, std::num::NonZeroUsize::new(1))
        .await?;
    service.delete_project(&project).await?;
    assert_eq!(
        serde_json::to_value(published)?,
        serde_json::to_value(stored)?
    );
    assert_eq!(vector.to_vec(), prepared.vector);
    assert_eq!(evidence.len(), 2);
    assert!(serde_json::to_string(&explanation)?.contains(&origin.reference));
    Ok(())
}

#[tokio::test]
async fn changed_support_refuses_the_entire_publication() -> Result<()> {
    let (service, project) = service(Some(Ok(vec![vector(0)]))).await?;
    let chunk = passage(&service, Some(&project), 0, "support removed before commit").await?;
    let prepared = service
        .prepare_belief(
            "must retain required support",
            0.7,
            0.5,
            Some(&project),
            MemoryType::Fact,
            None,
        )
        .await?;
    service.clear_document(&chunk.document_path).await?;
    let result = service.publish_prepared_belief(&prepared).await;
    no_publication(&service, prepared.belief.id).await?;
    service.delete_project(&project).await?;
    assert!(result.unwrap_err().is::<PreparationRequired>());
    Ok(())
}

#[tokio::test]
async fn deleting_the_project_revokes_preparation_even_with_global_support() -> Result<()> {
    let (service, project) = service(Some(Ok(vec![vector(7)]))).await?;
    let chunk = passage(
        &service,
        None,
        7,
        "global support survives project deletion",
    )
    .await?;
    let prepared = service
        .prepare_belief(
            "must not recreate a deleted project",
            0.7,
            0.5,
            Some(&project),
            MemoryType::Fact,
            None,
        )
        .await?;
    service.delete_project(&project).await?;
    let result = service.publish_prepared_belief(&prepared).await;
    let reappeared = service.get_belief(prepared.belief.id).await?;
    service.delete_project(&project).await?;
    service.clear_document(&chunk.document_path).await?;
    assert!(
        result.is_err(),
        "deletion must revoke in-flight work even when its supporting global document survives"
    );
    assert!(reappeared.is_none());
    Ok(())
}

#[tokio::test]
async fn vector_write_failure_rolls_back_belief_provenance_and_grounding() -> Result<()> {
    let (service, project) = service(Some(Ok(vec![vector(0)]))).await?;
    passage(&service, Some(&project), 0, "rollback support").await?;
    let prepared = service
        .prepare_belief(
            "atomic rollback",
            0.7,
            0.5,
            Some(&project),
            MemoryType::Fact,
            None,
        )
        .await?;
    let client = db::connect(&isolation::fixture().database_config()).await?;
    let suffix = prepared.belief.id.simple();
    let name = format!("reject_prepared_vector_{suffix}");
    client.batch_execute(&format!(
        "CREATE FUNCTION {name}() RETURNS trigger LANGUAGE plpgsql AS $$ BEGIN IF NEW.belief_id='{}'::uuid THEN RAISE EXCEPTION 'owned publication rollback probe'; END IF; RETURN NEW; END $$; CREATE TRIGGER {name} BEFORE INSERT ON public.belief_embeddings FOR EACH ROW EXECUTE FUNCTION {name}();", prepared.belief.id
    )).await?;
    let result = service.publish_prepared_belief(&prepared).await;
    client
        .batch_execute(&format!(
            "DROP TRIGGER {name} ON public.belief_embeddings; DROP FUNCTION {name}();"
        ))
        .await?;
    no_publication(&service, prepared.belief.id).await?;
    let owner: bool = client
        .query_one(
            "SELECT EXISTS(SELECT 1 FROM mimir_embedding_owners WHERE owner_token=$1)",
            &[&prepared.belief.id],
        )
        .await?
        .get(0);
    let published = service.publish_prepared_belief(&prepared).await?;
    let evidence = service.evidence_for_belief(published.id, None).await?;
    service.delete_project(&project).await?;
    let error = result.unwrap_err();
    assert!(
        !error.is::<PreparationRequired>(),
        "a write failure must not be labelled pre-execution correction"
    );
    assert!(
        owner,
        "rollback must preserve the original publication ownership"
    );
    assert_eq!(evidence.len(), 1);
    Ok(())
}

#[tokio::test]
async fn revoking_one_project_preserves_another_preparation_owner() -> Result<()> {
    let (first, project) = service(Some(Ok(vec![vector(8)]))).await?;
    let chunk = passage(&first, None, 8, "independent ownership").await?;
    let (second, other_project) = service(Some(Ok(vec![vector(8)]))).await?;
    let first_prepared = first
        .prepare_belief(
            "revoked work",
            0.7,
            0.5,
            Some(&project),
            MemoryType::Fact,
            None,
        )
        .await?;
    let second_prepared = second
        .prepare_belief(
            "independent work",
            0.7,
            0.5,
            Some(&other_project),
            MemoryType::Fact,
            None,
        )
        .await?;
    first.delete_project(&project).await?;
    let refused = first.publish_prepared_belief(&first_prepared).await;
    let published = second.publish_prepared_belief(&second_prepared).await?;
    no_publication(&first, first_prepared.belief.id).await?;
    second.delete_project(&other_project).await?;
    first.clear_document(&chunk.document_path).await?;
    assert!(refused.unwrap_err().is::<PreparationRequired>());
    assert_eq!(published.id, second_prepared.belief.id);
    Ok(())
}
