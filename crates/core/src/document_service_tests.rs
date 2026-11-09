#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;
use super::*;
use crate::{
    config::{Config, EmbeddingBackend, EmbeddingsConfig},
    documents::DocumentChunk,
    embed::{EmbedFuture, EmbeddingCancellation, EmbeddingProvider},
};
use anyhow::Context;
use serde_json::{json, Value};
use std::sync::Mutex;
use std::{
    path::PathBuf,
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    },
};
use tokio::sync::oneshot;

fn config() -> Config {
    Config {
        database: isolation::fixture().database_config(),
        embeddings: Some(EmbeddingsConfig {
            backend: EmbeddingBackend::Local,
            model: String::new(),
            api_key: None,
            cache_dir: None,
        }),
        llm: None,
        judge: None,
        email: None,
        retirement: None,
    }
}

async fn identity() -> Result<Uuid> {
    Ok(db::connect(&config().database)
        .await?
        .query_one("SELECT gen_random_uuid()", &[])
        .await?
        .get(0))
}

fn vector() -> Vec<f32> {
    let mut vector = vec![0.0; 768];
    vector[0] = 1.0;
    vector
}

struct Fixed(Arc<AtomicUsize>);
impl EmbeddingProvider for Fixed {
    fn embed<'a>(&'a self, texts: &'a [String], _: EmbeddingCancellation) -> EmbedFuture<'a> {
        self.0.fetch_add(1, Ordering::SeqCst);
        Box::pin(async move { Ok(texts.iter().map(|_| vector()).collect()) })
    }
}

struct FirstFails(Arc<AtomicUsize>);
impl EmbeddingProvider for FirstFails {
    fn embed<'a>(&'a self, texts: &'a [String], _: EmbeddingCancellation) -> EmbedFuture<'a> {
        let first = self.0.fetch_add(1, Ordering::SeqCst) == 0;
        Box::pin(async move {
            if first {
                anyhow::bail!("controlled document provider failure");
            }
            Ok(texts.iter().map(|_| vector()).collect())
        })
    }
}

struct Stopped(Option<oneshot::Sender<()>>);
impl Drop for Stopped {
    fn drop(&mut self) {
        if let Some(signal) = self.0.take() {
            let _ = signal.send(());
        }
    }
}

struct Blocked {
    started: Mutex<Option<oneshot::Sender<()>>>,
    release: Mutex<Option<oneshot::Receiver<()>>>,
    stopped: Mutex<Option<oneshot::Sender<()>>>,
}
impl EmbeddingProvider for Blocked {
    fn embed<'a>(&'a self, texts: &'a [String], _: EmbeddingCancellation) -> EmbedFuture<'a> {
        let started = self.started.lock().unwrap().take();
        let release = self
            .release
            .lock()
            .unwrap()
            .take()
            .expect("one owned provider call");
        let stopped = self.stopped.lock().unwrap().take();
        Box::pin(async move {
            let _stopped = Stopped(stopped);
            if let Some(started) = started {
                let _ = started.send(());
            }
            release.await?;
            Ok(texts.iter().map(|_| vector()).collect())
        })
    }
}

async fn blocked() -> Result<(
    Arc<MimirService>,
    oneshot::Receiver<()>,
    oneshot::Sender<()>,
    oneshot::Receiver<()>,
)> {
    let (started_tx, started) = oneshot::channel();
    let (release, release_rx) = oneshot::channel();
    let (stopped_tx, stopped) = oneshot::channel();
    let service = MimirService::connect_with_embeddings(
        &config(),
        Some(OwnedEmbeddingBackend::for_test(Box::new(Blocked {
            started: Mutex::new(Some(started_tx)),
            release: Mutex::new(Some(release_rx)),
            stopped: Mutex::new(Some(stopped_tx)),
        }))),
    )
    .await?;
    Ok((Arc::new(service), started, release, stopped))
}

async fn service() -> Result<(MimirService, Arc<AtomicUsize>)> {
    let calls = Arc::new(AtomicUsize::new(0));
    Ok((
        MimirService::connect_with_embeddings(
            &config(),
            Some(OwnedEmbeddingBackend::for_test(Box::new(Fixed(
                calls.clone(),
            )))),
        )
        .await?,
        calls,
    ))
}

async fn file() -> Result<(PathBuf, String)> {
    let root = std::env::temp_dir().join(format!("mimir-document-recovery-{}", identity().await?));
    std::fs::create_dir(&root)?;
    let path = root.join("source.md");
    std::fs::write(
        &path,
        "# New document\nComplete first section.\n## Child\nComplete child section.\n",
    )?;
    let project = format!("document-recovery-{}", identity().await?);
    Ok((path, project))
}

async fn token(service: &MimirService, path: &str, project: &str) -> Result<Uuid> {
    let request = service.load_document_request(path, Some(project))?;
    let token = service
        .reserve_operation(&identity().await?.to_string())
        .await?
        .operation_token;
    assert!(matches!(
        service.bind_operation_request(token, &request).await?,
        crate::store::OperationBindingDecision::Bound(_)
    ));
    Ok(token)
}

fn completed(outcome: OperationOutcome) -> Value {
    match outcome {
        OperationOutcome::Completed { outcome, .. } => mimir_json::clone_value(outcome.reply()),
        other => panic!("document operation is not complete: {other:?}"),
    }
}

async fn old_document(service: &MimirService, path: &str, project: &str) -> Result<Uuid> {
    let id = identity().await?;
    let chunk = DocumentChunk::with_id(
        id,
        path.into(),
        vec!["Old document".into()],
        "# Old document\nOld complete section.".into(),
        None,
        Some(project.into()),
    );
    service
        .store
        .replace_document(path, &[chunk], &[vector()])
        .await?;
    Ok(id)
}

async fn preparation(token: Uuid) -> Result<DocumentPreparation> {
    let client = db::connect(&config().database).await?;
    let source: String = client.query_one("SELECT reply::text FROM mimir_operation_step_replies WHERE operation_token=$1 AND step=$2",
        &[&token, &"[\"store.prepare_document\",null]"]).await?.get(0);
    Ok(mimir_json::from_str(&source)?)
}

#[tokio::test]
async fn failed_embedding_preserves_old_index_and_retry_uses_saved_original_file() -> Result<()> {
    let calls = Arc::new(AtomicUsize::new(0));
    let service = MimirService::connect_with_embeddings(
        &config(),
        Some(OwnedEmbeddingBackend::for_test(Box::new(FirstFails(
            calls.clone(),
        )))),
    )
    .await?;
    let (path, project) = file().await?;
    let path_text = path.to_str().context("owned path is UTF-8")?;
    let old = old_document(&service, path_text, &project).await?;
    let token = token(&service, path_text, &project).await?;
    assert!(service
        .load_document_operation(token)
        .await
        .unwrap_err()
        .is::<PreparationRequired>());
    let prepared = preparation(token).await?;
    assert!(service.store.get_chunk_by_id(old).await?.is_some());
    for chunk in &prepared.chunks {
        assert!(service.store.get_chunk_by_id(chunk.id).await?.is_none());
    }
    std::fs::write(
        &path,
        "# Changed later\nThis is not the saved original file.\n",
    )?;
    assert_eq!(
        completed(service.load_document_operation(token).await?),
        json!({"loaded":2})
    );
    assert_eq!(preparation(token).await?, prepared);
    for chunk in &prepared.chunks {
        assert_eq!(
            service.store.get_chunk_by_id(chunk.id).await?.as_ref(),
            Some(chunk)
        );
    }
    assert_eq!(calls.load(Ordering::SeqCst), 2);
    service.delete_project(&project).await?;
    std::fs::remove_file(&path)?;
    std::fs::remove_dir(path.parent().unwrap())?;
    Ok(())
}

#[tokio::test]
async fn project_deletion_stops_owned_embedding_without_republishing_document() -> Result<()> {
    let (service, started, _release, stopped) = blocked().await?;
    let (path, project) = file().await?;
    let path_text = path.to_str().context("owned path is UTF-8")?;
    old_document(&service, path_text, &project).await?;
    let token = token(&service, path_text, &project).await?;
    let running = {
        let service = service.clone();
        tokio::spawn(async move { service.load_document_operation(token).await })
    };
    started.await?;
    let writer = MimirService::connect_with_embeddings(&config(), None).await?;
    writer.delete_project(&project).await?;
    stopped.await?;
    assert!(running.await?.unwrap_err().is::<PreparationRequired>());
    let prepared = preparation(token).await?;
    for chunk in prepared.chunks {
        assert!(writer.store.get_chunk_by_id(chunk.id).await?.is_none());
    }
    assert!(writer
        .read_operation_step(token, "[\"store.replace_document\",null]")
        .await?
        .is_none());
    std::fs::remove_file(&path)?;
    std::fs::remove_dir(path.parent().unwrap())?;
    Ok(())
}

#[tokio::test]
async fn complete_document_replacement_replays_original_answer_without_reembedding() -> Result<()> {
    let (service, calls) = service().await?;
    let (path, project) = file().await?;
    let path_text = path.to_str().context("owned test path must be UTF-8")?;
    let old = old_document(&service, path_text, &project).await?;
    let token = token(&service, path_text, &project).await?;
    assert_eq!(
        completed(service.load_document_operation(token).await?),
        json!({"loaded":2})
    );
    let client = db::connect(&config().database).await?;
    let source: String = client.query_one("SELECT reply::text FROM mimir_operation_step_replies WHERE operation_token=$1 AND step=$2",
        &[&token, &"[\"store.prepare_document\",null]"]).await?.get(0);
    let original: DocumentPreparation = mimir_json::from_str(&source)?;
    assert_eq!(original.previous.len(), 1);
    assert_eq!(original.previous[0].id, old);
    assert!(service.store.get_chunk_by_id(old).await?.is_none());
    for chunk in &original.chunks {
        assert_eq!(
            service.store.get_chunk_by_id(chunk.id).await?.as_ref(),
            Some(chunk)
        );
        assert!(client
            .query_opt(
                "SELECT 1 FROM chunk_embeddings WHERE chunk_id=$1",
                &[&chunk.id]
            )
            .await?
            .is_some());
    }
    let owners: i64 = client
        .query_one(
            "SELECT count(*) FROM mimir_embedding_owners WHERE operation_token=$1",
            &[&token],
        )
        .await?
        .get(0);
    assert_eq!(owners, 0);
    std::fs::write(
        &path,
        "# A later different file\nNot this original operation.\n",
    )?;
    assert_eq!(
        completed(service.load_document_operation(token).await?),
        json!({"loaded":2})
    );
    assert_eq!(calls.load(Ordering::SeqCst), 1);
    service.delete_project(&project).await?;
    std::fs::remove_file(&path)?;
    std::fs::remove_dir(path.parent().unwrap())?;
    Ok(())
}

#[tokio::test]
async fn cancellation_stops_embedding_and_preserves_original_index_and_preparation() -> Result<()> {
    let (service, started, _release, stopped) = blocked().await?;
    let (path, project) = file().await?;
    let path_text = path.to_str().context("owned path is UTF-8")?;
    let old = old_document(&service, path_text, &project).await?;
    let token = token(&service, path_text, &project).await?;
    let running = {
        let service = service.clone();
        tokio::spawn(async move { service.load_document_operation(token).await })
    };
    started.await?;
    let original = preparation(token).await?;
    service.record_operation_cancellation(token).await?;
    stopped.await?;
    assert!(matches!(
        running.await??,
        OperationOutcome::Cancelled { .. }
    ));
    assert!(service.store.get_chunk_by_id(old).await?.is_some());
    assert_eq!(preparation(token).await?, original);
    assert!(matches!(
        service.load_document_operation(token).await?,
        OperationOutcome::Cancelled { .. }
    ));
    for chunk in original.chunks {
        assert!(service.store.get_chunk_by_id(chunk.id).await?.is_none());
    }
    service.delete_project(&project).await?;
    std::fs::remove_file(&path)?;
    std::fs::remove_dir(path.parent().unwrap())?;
    Ok(())
}

#[tokio::test]
async fn concurrent_replacement_stops_embedding_and_preserves_the_winning_document() -> Result<()> {
    let (service, started, _release, stopped) = blocked().await?;
    let (path, project) = file().await?;
    let path_text = path.to_str().context("owned path is UTF-8")?;
    old_document(&service, path_text, &project).await?;
    let token = token(&service, path_text, &project).await?;
    let running = {
        let service = service.clone();
        tokio::spawn(async move { service.load_document_operation(token).await })
    };
    started.await?;
    let winner = old_document(&service, path_text, &project).await?;
    stopped.await?;
    assert!(running.await?.unwrap_err().is::<PreparationRequired>());
    assert!(service.store.get_chunk_by_id(winner).await?.is_some());
    let prepared = preparation(token).await?;
    for chunk in prepared.chunks {
        assert!(service.store.get_chunk_by_id(chunk.id).await?.is_none());
    }
    assert!(service
        .read_operation_step(token, "[\"store.replace_document\",null]")
        .await?
        .is_none());
    service.delete_project(&project).await?;
    std::fs::remove_file(&path)?;
    std::fs::remove_dir(path.parent().unwrap())?;
    Ok(())
}

#[tokio::test]
async fn rejected_final_answer_rolls_back_the_whole_replacement_and_keeps_preparation() -> Result<()>
{
    let (service, _) = service().await?;
    let (path, project) = file().await?;
    let path_text = path.to_str().context("owned path is UTF-8")?;
    let old = old_document(&service, path_text, &project).await?;
    let belief = isolation::seed_belief_in_project(
        "belief supported by the old document",
        0.5,
        0.0,
        &project,
        crate::graph::MemoryType::Fact,
    )
    .await?
    .id;
    service.add_evidence(belief, old, 0.7).await?;
    let supported = service.store.get_belief(belief).await?.unwrap();
    let evidence = service.store.get_evidence_for_beliefs(&[belief]).await?;
    let token = token(&service, path_text, &project).await?;
    let client = db::connect(&config().database).await?;
    let name = format!("mimir_test_document_{}", token.simple());
    client.batch_execute(&format!("CREATE FUNCTION {name}() RETURNS trigger LANGUAGE plpgsql AS $f$ BEGIN IF NEW.operation_token='{token}'::uuid AND NEW.step='@operation-result' THEN RAISE EXCEPTION 'fixture refuses document completion'; END IF; RETURN NEW; END $f$; CREATE TRIGGER {name} BEFORE INSERT ON mimir_operation_step_replies FOR EACH ROW EXECUTE FUNCTION {name}();")).await?;
    let failed = service.load_document_operation(token).await;
    // Remove this case's injected fault before assertions so a failing check
    // cannot leave a trigger that affects a later retry of this owned token.
    client
        .batch_execute(&format!(
            "DROP TRIGGER {name} ON mimir_operation_step_replies; DROP FUNCTION {name}();"
        ))
        .await?;
    assert!(failed.is_err());
    assert!(service.store.get_chunk_by_id(old).await?.is_some());
    assert_eq!(
        mimir_json::to_value(service.store.get_belief(belief).await?.unwrap())?,
        mimir_json::to_value(&supported)?
    );
    assert_eq!(
        service.store.get_evidence_for_beliefs(&[belief]).await?,
        evidence
    );
    let original = preparation(token).await?;
    for chunk in &original.chunks {
        assert!(service.store.get_chunk_by_id(chunk.id).await?.is_none());
        assert!(client
            .query_opt(
                "SELECT 1 FROM chunk_embeddings WHERE chunk_id=$1",
                &[&chunk.id]
            )
            .await?
            .is_none());
    }
    assert!(service
        .read_operation_step(token, "[\"store.replace_document\",null]")
        .await?
        .is_none());
    assert_eq!(
        completed(service.load_document_operation(token).await?),
        json!({"loaded":2})
    );
    assert_eq!(preparation(token).await?, original);
    assert!(service.store.get_chunk_by_id(old).await?.is_none());
    assert!(service
        .store
        .get_evidence_for_beliefs(&[belief])
        .await?
        .is_empty());
    let recomputed = service.store.get_belief(belief).await?.unwrap();
    assert!(recomputed.alpha < supported.alpha);
    assert!(recomputed.decay_accounted_at > original.reserved_at);
    service.delete_project(&project).await?;
    std::fs::remove_file(&path)?;
    std::fs::remove_dir(path.parent().unwrap())?;
    Ok(())
}

#[tokio::test]
async fn old_completed_plan_replays_but_unfinished_old_plan_requires_user_decision() -> Result<()> {
    let (service, calls) = service().await?;
    let (path, project) = file().await?;
    let path_text = path.to_str().context("owned path is UTF-8")?;
    let old = old_document(&service, path_text, &project).await?;
    let client = db::connect(&config().database).await?;
    let plan = json!({"operation":"load_document", "shape":[
        {"site":"store.replace_document","may_repeat":false},
        {"site":"store.insert_evidence","may_repeat":true}],
        "steps":[{"site":"store.replace_document","key":null,
            "id":"[\"store.replace_document\",null]"}]});
    for complete in [false, true] {
        let token = token(&service, path_text, &project).await?;
        let raw = mimir_json::to_string(&plan)?;
        client.execute("INSERT INTO mimir_operation_plans(operation_token,plan) VALUES($1,$2::text::jsonb)", &[&token,&raw]).await?;
        if complete {
            for key in ["[\"store.replace_document\",null]", "@operation-result"] {
                client.execute("INSERT INTO mimir_operation_step_replies(operation_token,step,reply) VALUES($1,$2,'{\"loaded\":17}'::jsonb)", &[&token,&key]).await?;
            }
            assert_eq!(
                completed(service.load_document_operation(token).await?),
                json!({"loaded":17})
            );
        } else {
            let error = service.load_document_operation(token).await.unwrap_err();
            assert!(error.is::<PreparationRequired>());
            assert!(format!("{error:#}").contains("ask the user"));
            let saved: i64 = client
                .query_one(
                    "SELECT count(*) FROM mimir_operation_step_replies WHERE operation_token=$1",
                    &[&token],
                )
                .await?
                .get(0);
            assert_eq!(saved, 0);
        }
        let retained: String = client
            .query_one(
                "SELECT plan::text FROM mimir_operation_plans WHERE operation_token=$1",
                &[&token],
            )
            .await?
            .get(0);
        assert_eq!(mimir_json::from_str::<Value>(&retained)?, plan);
        assert!(service.store.get_chunk_by_id(old).await?.is_some());
    }
    assert_eq!(calls.load(Ordering::SeqCst), 0);
    service.delete_project(&project).await?;
    std::fs::remove_file(&path)?;
    std::fs::remove_dir(path.parent().unwrap())?;
    Ok(())
}
