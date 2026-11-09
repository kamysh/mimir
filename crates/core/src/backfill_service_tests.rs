#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;
use super::*;
use crate::{
    config::{Config, EmbeddingBackend, EmbeddingsConfig},
    embed::{EmbedFuture, EmbeddingCancellation, EmbeddingProvider, OwnedEmbeddingBackend},
    graph::MemoryType,
};
use serde_json::{json, Value};
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Arc, Mutex,
};
use tokio::sync::oneshot;

fn config(enabled: bool) -> Config {
    Config {
        database: isolation::fixture().database_config(),
        embeddings: enabled.then(|| EmbeddingsConfig {
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
fn vector(axis: usize) -> Vec<f32> {
    let mut v = vec![0.0; 768];
    v[axis] = 1.0;
    v
}
async fn identity() -> Result<String> {
    Ok(db::connect(&config(false).database)
        .await?
        .query_one("SELECT gen_random_uuid()::text", &[])
        .await?
        .get(0))
}
async fn seed(project: &str, text: &str) -> Result<crate::graph::Belief> {
    isolation::seed_belief_in_project(text, 0.7, 0.5, project, MemoryType::Fact).await
}
async fn reserve(service: &MimirService) -> Result<Uuid> {
    Ok(service
        .reserve_operation(&identity().await?)
        .await?
        .operation_token)
}
fn completed(outcome: OperationOutcome) -> Value {
    match outcome {
        OperationOutcome::Completed { outcome, .. } => outcome.reply().clone(),
        other => panic!("not completed: {other:?}"),
    }
}
async fn stored(id: Uuid) -> Result<Option<Vec<f32>>> {
    Ok(db::connect(&config(false).database)
        .await?
        .query_opt(
            "SELECT embedding FROM belief_embeddings WHERE belief_id=$1",
            &[&id],
        )
        .await?
        .map(|row| row.get::<_, pgvector::Vector>(0).to_vec()))
}
struct Fixed {
    calls: Arc<AtomicUsize>,
    fail_at: Option<usize>,
}
impl EmbeddingProvider for Fixed {
    fn embed<'a>(&'a self, _: &'a [String], _: EmbeddingCancellation) -> EmbedFuture<'a> {
        Box::pin(async move {
            let call = self.calls.fetch_add(1, Ordering::SeqCst);
            if self.fail_at == Some(call) {
                return Err(anyhow!("explicit fixture provider failure"));
            }
            Ok(vec![vector(1)])
        })
    }
}
async fn fixed(fail_at: Option<usize>) -> Result<(MimirService, Arc<AtomicUsize>)> {
    let calls = Arc::new(AtomicUsize::new(0));
    Ok((
        MimirService::connect_with_embeddings(
            &config(true),
            Some(OwnedEmbeddingBackend::for_test(Box::new(Fixed {
                calls: calls.clone(),
                fail_at,
            }))),
        )
        .await?,
        calls,
    ))
}

#[tokio::test]
async fn saved_item_and_final_counts_survive_failure_new_sources_and_reconnect() -> Result<()> {
    let project = format!("registered-backfill-{}", identity().await?);
    let (service, calls) = fixed(Some(1)).await?;
    let first = seed(&project, "first original source").await?;
    let second = seed(&project, "second original source").await?;
    let token = reserve(&service).await?;
    assert!(service
        .reembed_operation(token)
        .await
        .unwrap_err()
        .is::<PreparationRequired>());
    assert_eq!(calls.load(Ordering::SeqCst), 2);
    let OperationOutcome::Pending { saved_replies, .. } =
        service.read_operation_outcome(token, None).await?
    else {
        panic!("partial prefix was lost")
    };
    assert_eq!(saved_replies.len(), 1);
    let later = seed(&project, "later source must not enter the original plan").await?;
    drop(service);
    let (reopened, retry_calls) = fixed(None).await?;
    assert_eq!(
        completed(reopened.reembed_operation(token).await?),
        json!({"embedded":2,"skipped":0})
    );
    assert_eq!(retry_calls.load(Ordering::SeqCst), 1);
    assert!(stored(first.id).await?.is_some() && stored(second.id).await?.is_some());
    assert!(stored(later.id).await?.is_none());
    reopened.delete_belief(first.id).await?;
    let no_backend = MimirService::connect(&config(false)).await?;
    assert_eq!(
        completed(no_backend.reembed_operation(token).await?),
        json!({"embedded":2,"skipped":0})
    );
    reopened.delete_project(&project).await?;
    Ok(())
}

struct DropSignal(Option<oneshot::Sender<()>>);
impl Drop for DropSignal {
    fn drop(&mut self) {
        if let Some(send) = self.0.take() {
            let _ = send.send(());
        }
    }
}
struct Blocked {
    text: String,
    started: Mutex<Option<oneshot::Sender<()>>>,
    stopped: Mutex<Option<oneshot::Sender<()>>>,
    calls: Arc<AtomicUsize>,
}
impl EmbeddingProvider for Blocked {
    fn embed<'a>(&'a self, texts: &'a [String], _: EmbeddingCancellation) -> EmbedFuture<'a> {
        Box::pin(async move {
            self.calls.fetch_add(1, Ordering::SeqCst);
            if texts[0] != self.text {
                return Ok(vec![vector(2)]);
            }
            let _drop = DropSignal(self.stopped.lock().unwrap().take());
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
async fn blocked(
    text: String,
) -> Result<(
    Arc<MimirService>,
    oneshot::Receiver<()>,
    oneshot::Receiver<()>,
    Arc<AtomicUsize>,
)> {
    let (started_tx, started_rx) = oneshot::channel();
    let (stop_tx, stop_rx) = oneshot::channel();
    let calls = Arc::new(AtomicUsize::new(0));
    let provider = Blocked {
        text,
        started: Mutex::new(Some(started_tx)),
        stopped: Mutex::new(Some(stop_tx)),
        calls: calls.clone(),
    };
    let service = MimirService::connect_with_embeddings(
        &config(true),
        Some(OwnedEmbeddingBackend::for_test(Box::new(provider))),
    )
    .await?;
    Ok((Arc::new(service), started_rx, stop_rx, calls))
}

#[tokio::test]
async fn concurrent_vector_stops_redundant_job_preserves_vector_and_continues() -> Result<()> {
    let project = format!("concurrent-backfill-{}", identity().await?);
    let a = seed(&project, "one original source").await?;
    let b = seed(&project, "another original source").await?;
    let (target, other) = if a.id < b.id { (a, b) } else { (b, a) };
    let (owner, started, stopped, calls) = blocked(target.content.clone()).await?;
    let token = reserve(&owner).await?;
    let PlanDecision::Ready(original) = owner.prepare_reembed_operation(token).await? else {
        panic!("original selection was not saved")
    };
    let sources = AgeStore::reembed_sources(&original)?;
    let pending = sources
        .iter()
        .filter(|source| !source.already_embedded)
        .count();
    for id in [target.id, other.id] {
        assert!(sources
            .iter()
            .any(|source| source.id == id && !source.already_embedded));
    }
    let initially_skipped = sources.len() - pending;
    let running = {
        let owner = owner.clone();
        tokio::spawn(async move { owner.reembed_operation(token).await })
    };
    started.await?;
    let writer = MimirService::connect(&config(false)).await?;
    let preserved = vector(7);
    writer
        .store
        .insert_belief_embedding(target.id, &preserved)
        .await?;
    stopped.await?;
    assert_eq!(
        completed(running.await??),
        json!({"embedded":pending-1,"skipped":initially_skipped+1})
    );
    assert_eq!(calls.load(Ordering::SeqCst), pending);
    assert_eq!(stored(target.id).await?, Some(preserved));
    assert_eq!(stored(other.id).await?, Some(vector(2)));
    writer.delete_project(&project).await?;
    Ok(())
}

#[tokio::test]
async fn product_deletion_stops_blocked_job_without_answer_or_vector() -> Result<()> {
    let project = format!("changed-backfill-{}", identity().await?);
    let target = seed(&project, "complete captured source").await?;
    let (owner, started, stopped, _) = blocked(target.content.clone()).await?;
    let token = reserve(&owner).await?;
    let running = {
        let owner = owner.clone();
        tokio::spawn(async move { owner.reembed_operation(token).await })
    };
    started.await?;
    let writer = MimirService::connect(&config(false)).await?;
    writer.delete_belief(target.id).await?;
    stopped.await?;
    assert!(running.await?.unwrap_err().is::<PreparationRequired>());
    assert!(stored(target.id).await?.is_none());
    let PlanDecision::Ready(plan) = owner.prepare_reembed_operation(token).await? else {
        panic!("original plan unavailable")
    };
    assert!(
        owner
            .store
            .commit_reembed_item(&plan.steps()[0], Some(vector(1)))
            .await
            .is_err(),
        "a late prepared result cannot bypass the transactional source guard"
    );
    let OperationOutcome::Pending { saved_replies, .. } =
        owner.read_operation_outcome(token, None).await?
    else {
        panic!("old operation was completed")
    };
    assert!(saved_replies.is_empty());
    writer.delete_project(&project).await?;
    Ok(())
}

#[tokio::test]
async fn changed_captured_source_requests_dialogue_before_provider_or_late_publication(
) -> Result<()> {
    let project = format!("stale-backfill-{}", identity().await?);
    let target = seed(&project, "complete original captured source").await?;
    let (owner, calls) = fixed(None).await?;
    let token = reserve(&owner).await?;
    let PlanDecision::Ready(plan) = owner.prepare_reembed_operation(token).await? else {
        panic!("original selection missing")
    };
    // Test-only mutation establishes an already changed starting state. AGE
    // custom writes do not promise SQL trigger delivery; normal product source
    // deletion is covered separately through the actual deletion method.
    let client = db::connect(&config(false).database).await?;
    let graph = config(false).database.dbname;
    client.query(&format!("SELECT * FROM ag_catalog.cypher('{graph}', $$ MATCH(n:Belief {{id:'{}'}}) SET n.content='changed test source' RETURN n.id $$) AS(id ag_catalog.agtype)",target.id),&[]).await?;
    assert!(owner
        .reembed_operation(token)
        .await
        .unwrap_err()
        .is::<PreparationRequired>());
    assert_eq!(calls.load(Ordering::SeqCst), 0);
    assert!(owner
        .store
        .commit_reembed_item(&plan.steps()[0], Some(vector(1)))
        .await
        .is_err());
    assert!(stored(target.id).await?.is_none());
    let OperationOutcome::Pending { saved_replies, .. } =
        owner.read_operation_outcome(token, None).await?
    else {
        panic!("stale work was completed")
    };
    assert!(saved_replies.is_empty());
    owner.delete_project(&project).await?;
    Ok(())
}

#[tokio::test]
async fn explicit_cancellation_preserves_committed_prefix_and_stops_pending_job() -> Result<()> {
    let project = format!("cancel-backfill-{}", identity().await?);
    let a = seed(&project, "first source").await?;
    let b = seed(&project, "second source").await?;
    let (earlier, target) = if a.id < b.id { (a, b) } else { (b, a) };
    let (owner, started, stopped, _) = blocked(target.content.clone()).await?;
    let token = reserve(&owner).await?;
    let running = {
        let owner = owner.clone();
        tokio::spawn(async move { owner.reembed_operation(token).await })
    };
    started.await?;
    owner.record_operation_cancellation(token).await?;
    stopped.await?;
    assert!(running.await?.unwrap_err().is::<PreparationRequired>());
    assert!(stored(earlier.id).await?.is_some());
    assert!(stored(target.id).await?.is_none());
    let OperationOutcome::Cancelled { saved_replies, .. } =
        owner.read_operation_outcome(token, None).await?
    else {
        panic!("cancellation missing")
    };
    assert_eq!(saved_replies.len(), 1);
    let binding = owner.read_operation_binding(token).await?.unwrap();
    assert_eq!(binding.request.operation(), "reembed");
    owner.delete_project(&project).await?;
    Ok(())
}

#[tokio::test]
async fn rejected_final_answer_rolls_back_vector_and_item_answer() -> Result<()> {
    let project = format!("rollback-backfill-{}", identity().await?);
    let target = seed(&project, "actual vector must share final commit").await?;
    let (owner, _) = fixed(None).await?;
    let token = reserve(&owner).await?;
    let client = db::connect(&config(false).database).await?;
    client.batch_execute(&format!("CREATE FUNCTION mimir_test_reject_backfill_result() RETURNS trigger LANGUAGE plpgsql AS $f$ BEGIN IF NEW.operation_token='{token}'::uuid AND NEW.step='@operation-result' THEN RAISE EXCEPTION 'fixture refuses final answer'; END IF; RETURN NEW; END $f$; CREATE TRIGGER mimir_test_reject_backfill_result BEFORE INSERT ON mimir_operation_step_replies FOR EACH ROW EXECUTE FUNCTION mimir_test_reject_backfill_result();")).await?;
    assert!(owner.reembed_operation(token).await.is_err());
    assert!(stored(target.id).await?.is_none());
    let count: i64 = client
        .query_one(
            "SELECT count(*) FROM mimir_operation_step_replies WHERE operation_token=$1",
            &[&token],
        )
        .await?
        .get(0);
    assert_eq!(count, 0);
    client.batch_execute("DROP TRIGGER mimir_test_reject_backfill_result ON mimir_operation_step_replies; DROP FUNCTION mimir_test_reject_backfill_result();").await?;
    assert_eq!(
        completed(owner.reembed_operation(token).await?),
        json!({"embedded":1,"skipped":0})
    );
    owner.delete_project(&project).await?;
    Ok(())
}

#[tokio::test]
async fn existing_vector_skips_without_provider_and_zero_pending_counts_are_saved() -> Result<()> {
    let project = format!("skip-backfill-{}", identity().await?);
    let target = seed(&project, "already completed by another operation").await?;
    let (owner, calls) = fixed(None).await?;
    let token = reserve(&owner).await?;
    owner.prepare_reembed_operation(token).await?;
    owner
        .store
        .insert_belief_embedding(target.id, &vector(5))
        .await?;
    let no_backend = MimirService::connect(&config(false)).await?;
    assert_eq!(
        completed(no_backend.reembed_operation(token).await?),
        json!({"embedded":0,"skipped":1})
    );
    assert_eq!(calls.load(Ordering::SeqCst), 0);
    let next = reserve(&no_backend).await?;
    assert_eq!(
        completed(no_backend.reembed_operation(next).await?),
        json!({"embedded":0,"skipped":1})
    );
    assert_eq!(stored(target.id).await?, Some(vector(5)));
    no_backend.delete_project(&project).await?;
    Ok(())
}

#[tokio::test]
async fn unfinished_saved_prefix_cannot_hide_a_later_source_deletion() -> Result<()> {
    let project = format!("lost-prefix-backfill-{}", identity().await?);
    let a = seed(&project, "first captured source").await?;
    let b = seed(&project, "second captured source").await?;
    let (first, last) = if a.id < b.id { (a, b) } else { (b, a) };
    let (owner, _) = fixed(Some(1)).await?;
    let token = reserve(&owner).await?;
    assert!(owner.reembed_operation(token).await.is_err());
    assert!(stored(first.id).await?.is_some());
    owner.delete_belief(first.id).await?;
    let (retry, calls) = fixed(None).await?;
    assert!(retry
        .reembed_operation(token)
        .await
        .unwrap_err()
        .is::<PreparationRequired>());
    assert_eq!(
        calls.load(Ordering::SeqCst),
        0,
        "a lost prefix source must stop remaining provider work"
    );
    let PlanDecision::Ready(plan) = retry.prepare_reembed_operation(token).await? else {
        panic!("original plan missing")
    };
    assert!(retry
        .store
        .commit_reembed_item(plan.steps().last().unwrap(), Some(vector(4)))
        .await
        .is_err());
    assert!(
        stored(last.id).await?.is_none(),
        "the final vector must roll back with a refused completion"
    );
    let OperationOutcome::Pending { saved_replies, .. } =
        retry.read_operation_outcome(token, None).await?
    else {
        panic!("unfinished operation was completed")
    };
    assert_eq!(
        saved_replies.len(),
        1,
        "the original acknowledged prefix stays intact"
    );
    retry.delete_project(&project).await?;
    Ok(())
}

#[tokio::test]
async fn empty_pending_selection_rechecks_initially_skipped_sources_before_completion() -> Result<()>
{
    let project = format!("lost-initial-skip-{}", identity().await?);
    let target = seed(&project, "initially embedded source later deleted").await?;
    let owner = MimirService::connect(&config(false)).await?;
    owner
        .store
        .insert_belief_embedding(target.id, &vector(3))
        .await?;
    let token = reserve(&owner).await?;
    owner.prepare_reembed_operation(token).await?;
    owner.delete_belief(target.id).await?;
    assert!(owner
        .reembed_operation(token)
        .await
        .unwrap_err()
        .is::<PreparationRequired>());
    assert!(matches!(
        owner.read_operation_outcome(token, None).await?,
        OperationOutcome::AwaitingCompletion(_)
    ));
    owner.delete_project(&project).await?;
    Ok(())
}
