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
