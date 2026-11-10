//! Complete document removal and its original answer share one transaction.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;
use anyhow::{ensure, Result};
use mimir_core::{
    config::Config,
    db,
    documents::DocumentChunk,
    graph::{Edge, EdgeType, MemoryType},
    store::*,
    MimirService,
};
use serde_json::{json, Value};
use uuid::Uuid;

fn config() -> Config {
    Config {
        database: isolation::fixture().database_config(),
        embeddings: None,
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
struct Fixture {
    service: MimirService,
    store: AgeStore,
    project: String,
    path: String,
    other_path: String,
    belief: Uuid,
    child: Uuid,
    unrelated: Uuid,
    chunks: Vec<Uuid>,
    other: Uuid,
}
impl Fixture {
    async fn create() -> Result<Self> {
        let project = format!("document-removal-{}", identity().await?);
        let path = format!("/mimir-test/{project}.md");
        let other_path = format!("/mimir-test/{project}-other.md");
        let service = MimirService::connect(&config()).await?;
        let store = AgeStore::new(
            db::connect(&config().database).await?,
            config().database.dbname,
        )?;
        let belief = isolation::seed_belief_in_project(
            "supported belief",
            0.5,
            0.0,
            &project,
            MemoryType::Fact,
        )
        .await?
        .id;
        let child = isolation::seed_belief_in_project(
            "affected child",
            0.5,
            0.0,
            &project,
            MemoryType::Fact,
        )
        .await?
        .id;
        let unrelated = isolation::seed_belief_in_project(
            "unrelated belief",
            0.9,
            0.2,
            &project,
            MemoryType::Fact,
        )
        .await?
        .id;
        store
            .insert_edge(&Edge::new(belief, child, EdgeType::Supports, 1.0)?)
            .await?;
        let mut chunks = Vec::new();
        for _ in 0..2 {
            let chunk = DocumentChunk::with_id(
                identity().await?,
                path.clone(),
                vec![],
                "supporting passage".into(),
                None,
                Some(project.clone()),
            );
            store.insert_document_chunk(&chunk).await?;
            store
                .insert_chunk_embedding(chunk.id, &[1.0, 0.0, 0.0])
                .await?;
            service.add_evidence(belief, chunk.id, 0.7).await?;
            chunks.push(chunk.id);
        }
        let other = DocumentChunk::with_id(
            identity().await?,
            other_path.clone(),
            vec![],
            "unrelated passage".into(),
            None,
            Some(project.clone()),
        );
        store.insert_document_chunk(&other).await?;
        store
            .insert_chunk_embedding(other.id, &[0.0, 1.0, 0.0])
            .await?;
        Ok(Self {
            service,
            store,
            project,
            path,
            other_path,
            belief,
            child,
            unrelated,
            chunks,
            other: other.id,
        })
    }
    async fn plan_request(
        &self,
        request: OperationBindingRequest,
    ) -> Result<(Uuid, RegisteredStep)> {
        let token = self
            .service
            .reserve_operation(&identity().await?.to_string())
            .await?
            .operation_token;
        self.service.bind_operation_request(token, &request).await?;
        let PlanDecision::Ready(plan) = self
            .service
            .prepare_operation(token, &request, |_, _| Box::pin(async { Ok(vec![]) }))
            .await?
        else {
            panic!("no plan")
        };
        Ok((token, plan.steps()[0].clone()))
    }
    async fn plan(&self, path: &str) -> Result<(Uuid, RegisteredStep)> {
        self.plan_request(self.service.clear_document_request(path)?)
            .await
    }
    async fn state(&self) -> Result<Value> {
        let mut ids = self.chunks.clone();
        ids.push(self.other);
        let audit = db::connect(&config().database).await?;
        let vectors:Vec<_>=audit.query("SELECT chunk_id,embedding::text FROM public.chunk_embeddings WHERE chunk_id=ANY($1) ORDER BY chunk_id",&[&ids]).await?.into_iter().map(|r|(r.get::<_,Uuid>(0),r.get::<_,String>(1))).collect();
        Ok(
            json!({"chunks":self.store.get_chunk_ids_for_document(&self.path).await?,"other_chunks":self.store.get_chunk_ids_for_document(&self.other_path).await?,
            "vectors":vectors,"belief":self.store.get_belief(self.belief).await?,"child":self.store.get_belief(self.child).await?,"unrelated":self.store.get_belief(self.unrelated).await?,
            "evidence":self.store.get_evidence_for_beliefs(&[self.belief]).await?}),
        )
    }
    async fn cleanup(&self) -> Result<()> {
        self.store.delete_project(&self.project).await?;
        Ok(())
    }
}

#[tokio::test]
async fn removal_recomputes_beliefs_and_replay_preserves_a_later_document() -> Result<()> {
    let f = Fixture::create().await?;
    let checked=async {
        let before=f.state().await?;let (token,step)=f.plan(&f.path).await?;
        let not_before: chrono::DateTime<chrono::Utc> = db::connect(&config().database)
            .await?.query_one("SELECT clock_timestamp()", &[]).await?.get(0);
        let StepDecision::Done(first)=f.service.clear_document_operation(&step).await? else{panic!("no completion")};
        ensure!(first.reply==json!({"cleared":2}));let after=f.state().await?;
        ensure!(after["chunks"]==json!([]) && after["evidence"]==json!([]));
        ensure!(after["vectors"].as_array().unwrap().len()==1 && after["vectors"][0][0]==json!(f.other));
        ensure!(after["other_chunks"]==before["other_chunks"]&&after["unrelated"]==before["unrelated"]);
        ensure!(after["belief"]["alpha"].as_f64().unwrap()<before["belief"]["alpha"].as_f64().unwrap());
        ensure!(after["child"]["alpha"].as_f64().unwrap()<before["child"]["alpha"].as_f64().unwrap());
        for id in [f.belief, f.child] {
            ensure!(f.store.get_belief(id).await?.unwrap().decay_accounted_at >= not_before);
        }
        ensure!(after["belief"]["created_at"] == before["belief"]["created_at"]);
        let later=DocumentChunk::with_id(identity().await?,f.path.clone(),vec![],"replacement passage".into(),None,Some(f.project.clone()));
        f.store.insert_document_chunk(&later).await?;f.store.insert_chunk_embedding(later.id,&[0.0,0.0,1.0]).await?;
        let later_state=f.state().await?;
        let reopened=MimirService::connect(&config()).await?;
        let StepDecision::Done(replayed)=reopened.clear_document_operation(&step).await? else{panic!("no replay")};
        ensure!(first==replayed && f.state().await?==later_state);
        ensure!(f.store.get_chunk_ids_for_document(&f.path).await?==vec![later.id]);
        ensure!(db::connect(&config().database).await?.query_one("SELECT count(*) FROM public.chunk_embeddings WHERE chunk_id=$1",&[&later.id]).await?.get::<_,i64>(0)==1);
        ensure!(matches!(reopened.read_operation_outcome(token,None).await?,OperationOutcome::Completed{outcome,..} if outcome.reply()==&first.reply));
        Ok::<_,anyhow::Error>(())
    }.await;
    let cleanup = f.cleanup().await;
    checked?;
    cleanup
}

#[tokio::test]
async fn final_receipt_failure_rolls_back_chunks_vectors_evidence_and_posterior_counts(
) -> Result<()> {
    let f = Fixture::create().await?;
    let checked=async {
        let before=f.state().await?;let (token,step)=f.plan(&f.path).await?;
        let audit=db::connect(&config().database).await?;let constraint=format!("reject_clear_result_{}",token.simple());
        audit.batch_execute(&format!("ALTER TABLE mimir_operation_step_replies ADD CONSTRAINT {constraint} CHECK(operation_token <> '{token}'::uuid OR step <> '@operation-result') NOT VALID")).await?;
        let attempted=f.service.clear_document_operation(&step).await;
        audit.batch_execute(&format!("ALTER TABLE mimir_operation_step_replies DROP CONSTRAINT {constraint}")).await?;
        ensure!(attempted.is_err()&&f.state().await?==before);
        ensure!(f.service.read_operation_step(token,step.id()).await?.is_none());
        ensure!(matches!(f.service.read_operation_outcome(token,None).await?,OperationOutcome::Pending{..}));
        ensure!(matches!(f.service.clear_document_operation(&step).await?,StepDecision::Done(_)));
        Ok::<_,anyhow::Error>(())
    }.await;
    let cleanup = f.cleanup().await;
    checked?;
    cleanup
}

#[tokio::test]
async fn invalid_preparation_and_cancellation_cannot_change_any_document() -> Result<()> {
    let f = Fixture::create().await?;
    let checked = async {
        let before = f.state().await?;
        for (args, settings) in [
            (json!({}), json!({"resolved_path":f.path})),
            (
                json!({"path":f.path,"extra":true}),
                json!({"resolved_path":f.path}),
            ),
            (json!({"path":f.path}), json!({})),
            (json!({"path":f.path}), json!({"resolved_path":false})),
        ] {
            let request = OperationBindingRequest::new("clear_document".into(), args, settings)?;
            let (token, step) = f.plan_request(request).await?;
            let error = f.service.clear_document_operation(&step).await.unwrap_err();
            ensure!(error.to_string().contains(
                "Ask the user whether to cancel this unfinished token and reserve corrected work"
            ));
            ensure!(f.state().await? == before);
            ensure!(matches!(
                f.service.read_operation_outcome(token, None).await?,
                OperationOutcome::Pending { .. }
            ));
        }
        let (token, step) = f.plan(&f.path).await?;
        let CancellationDecision::Recorded(receipt) =
            f.service.record_operation_cancellation(token).await?
        else {
            panic!("no cancellation")
        };
        ensure!(
            f.service.clear_document_operation(&step).await? == StepDecision::Cancelled(receipt)
        );
        ensure!(f.state().await? == before);
        Ok::<_, anyhow::Error>(())
    }
    .await;
    let cleanup = f.cleanup().await;
    checked?;
    cleanup
}

#[tokio::test]
async fn original_resolved_path_survives_a_changed_symlink_before_execution() -> Result<()> {
    let f = Fixture::create().await?;
    let directory = isolation::fixture()
        .root
        .join(format!("document-path-{}", identity().await?));
    std::fs::create_dir(&directory)?;
    let first = directory.join("first.md");
    let second = directory.join("second.md");
    let alias = directory.join("alias.md");
    std::fs::write(&first, "first")?;
    std::fs::write(&second, "second")?;
    std::os::unix::fs::symlink(&first, &alias)?;
    let checked = async {
        let mut ids = Vec::new();
        for path in [&first, &second] {
            let chunk = DocumentChunk::with_id(
                identity().await?,
                path.to_str().unwrap().into(),
                vec![],
                "indexed passage".into(),
                None,
                Some(f.project.clone()),
            );
            f.store.insert_document_chunk(&chunk).await?;
            ids.push(chunk.id);
        }
        let (_, step) = f.plan(alias.to_str().unwrap()).await?;
        std::fs::remove_file(&alias)?;
        std::os::unix::fs::symlink(&second, &alias)?;
        let StepDecision::Done(answer) = f.service.clear_document_operation(&step).await? else {
            panic!("no removal")
        };
        ensure!(answer.reply == json!({"cleared":1}));
        ensure!(f
            .store
            .get_chunk_ids_for_document(first.to_str().unwrap())
            .await?
            .is_empty());
        ensure!(
            f.store
                .get_chunk_ids_for_document(second.to_str().unwrap())
                .await?
                == vec![ids[1]]
        );
        Ok::<_, anyhow::Error>(())
    }
    .await;
    let cleanup = f.cleanup().await;
    std::fs::remove_file(alias)?;
    std::fs::remove_file(first)?;
    std::fs::remove_file(second)?;
    std::fs::remove_dir(directory)?;
    checked?;
    cleanup
}
