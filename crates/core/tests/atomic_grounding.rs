//! Evidence, every affected posterior, and both saved answers share a commit.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;
use anyhow::{ensure, Result};
use mimir_core::{
    config::Config,
    db,
    documents::DocumentChunk,
    graph::{Belief, Edge, EdgeType},
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
    store: AgeStore,
    service: MimirService,
    project: String,
    belief: Uuid,
    child: Uuid,
    unrelated: Uuid,
    chunk: Uuid,
}
impl Fixture {
    async fn create() -> Result<Self> {
        let cfg = config();
        let service = MimirService::connect(&cfg).await?;
        let store = AgeStore::new(db::connect(&cfg.database).await?, cfg.database.dbname)?;
        let project = format!("grounding-operation-{}", identity().await?);
        let mut belief =
            Belief::new_in_project("supported fact".into(), 0.5, 0.0, project.clone())?;
        belief.id = identity().await?;
        let mut child =
            Belief::new_in_project("affected descendant".into(), 0.5, 0.0, project.clone())?;
        child.id = identity().await?;
        store.insert_belief(&belief).await?;
        store.insert_belief(&child).await?;
        let mut unrelated =
            Belief::new_in_project("unrelated record".into(), 0.9, 0.2, project.clone())?;
        unrelated.id = identity().await?;
        store.insert_belief(&unrelated).await?;
        store
            .insert_edge(&Edge::new(belief.id, child.id, EdgeType::Supports, 1.0)?)
            .await?;
        service.propagate_from(belief.id).await?;
        let chunk = DocumentChunk::with_id(
            identity().await?,
            format!("/mimir-test/{project}.md"),
            vec![],
            "An indexed passage supporting the fact".into(),
            None,
            Some(project.clone()),
        );
        store.insert_document_chunk(&chunk).await?;
        Ok(Self {
            store,
            service,
            project,
            belief: belief.id,
            child: child.id,
            unrelated: unrelated.id,
            chunk: chunk.id,
        })
    }
    fn args(&self) -> Value {
        json!({"belief_id":self.belief,"chunk_id":self.chunk})
    }
    async fn plan(&self, operation: &str, arguments: Value) -> Result<(Uuid, RegisteredStep)> {
        let token = self
            .service
            .reserve_operation(&identity().await?.to_string())
            .await?
            .operation_token;
        let binding = OperationBindingRequest::new(operation.into(), arguments, json!({}))?;
        self.service.bind_operation_request(token, &binding).await?;
        let PlanDecision::Ready(plan) = self
            .service
            .prepare_operation(token, &binding, |_, _| Box::pin(async { Ok(vec![]) }))
            .await?
        else {
            panic!("missing plan")
        };
        ensure!(plan.steps().len() == 1);
        Ok((token, plan.steps()[0].clone()))
    }
    async fn state(&self) -> Result<Value> {
        Ok(
            json!({"belief":self.store.get_belief(self.belief).await?,"child":self.store.get_belief(self.child).await?,
            "grounds":self.store.get_evidence_for_beliefs(&[self.belief]).await?,
            "unrelated":self.store.get_belief(self.unrelated).await?}),
        )
    }
    async fn pending(&self, token: Uuid, step: &RegisteredStep) -> Result<()> {
        ensure!(self
            .service
            .read_operation_step(token, step.id())
            .await?
            .is_none());
        ensure!(self
            .service
            .read_operation_step(token, "@operation-result")
            .await?
            .is_none());
        ensure!(matches!(
            self.service.read_operation_outcome(token, None).await?,
            OperationOutcome::Pending { .. }
        ));
        Ok(())
    }
    async fn cleanup(&self) -> Result<()> {
        self.store.delete_project(&self.project).await?;
        Ok(())
    }
}

#[tokio::test]
async fn addition_replays_original_answer_without_duplicating_evidence_or_probabilities(
) -> Result<()> {
    let f = Fixture::create().await?;
    let checked=async {
        let before=f.state().await?;
        let (token,step)=f.plan("add_evidence",f.args()).await?;
        let StepDecision::Done(first)=f.service.change_evidence_operation(&step).await? else {panic!("no result")};
        ensure!(first.reply==json!({"ok":true}));
        let after=f.state().await?;
        ensure!(after["unrelated"]==before["unrelated"],"unrelated record changed");
        ensure!(after["grounds"].as_array().unwrap().len()==1);
        ensure!(after["belief"]["alpha"].as_f64().unwrap()>before["belief"]["alpha"].as_f64().unwrap());
        ensure!(after["child"]["alpha"].as_f64().unwrap()>before["child"]["alpha"].as_f64().unwrap(),"descendant was not recomputed");
        let reopened=MimirService::connect(&config()).await?;
        let StepDecision::Done(replayed)=reopened.change_evidence_operation(&step).await? else {panic!("no replay")};
        ensure!(first==replayed && f.state().await?==after);
        ensure!(matches!(reopened.read_operation_outcome(token,None).await?,OperationOutcome::Completed{outcome,..} if outcome.reply()==&first.reply));
        // A deliberately separate operation remains a separate contribution.
        let (_,another)=f.plan("add_evidence",f.args()).await?;
        f.service.change_evidence_operation(&another).await?;
        ensure!(f.store.get_evidence_for_beliefs(&[f.belief]).await?.len()==2);
        Ok::<_,anyhow::Error>(())
    }.await;
    let cleanup = f.cleanup().await;
    checked?;
    cleanup
}

#[tokio::test]
async fn removal_replays_without_removing_evidence_added_after_its_completion() -> Result<()> {
    let f = Fixture::create().await?;
    let checked = async {
        let unrelated = f.state().await?["unrelated"].clone();
        for _ in 0..2 {
            f.service.add_evidence(f.belief, f.chunk, 0.5).await?;
        }
        let child_before = f.store.get_belief(f.child).await?.unwrap();
        let (token, step) = f.plan("delete_evidence", f.args()).await?;
        let StepDecision::Done(first) = f.service.change_evidence_operation(&step).await? else {
            panic!("no result")
        };
        ensure!(f
            .store
            .get_evidence_for_beliefs(&[f.belief])
            .await?
            .is_empty());
        ensure!(
            f.store.get_belief(f.child).await?.unwrap().alpha < child_before.alpha,
            "removal skipped recomputation"
        );
        f.service.add_evidence(f.belief, f.chunk, 0.7).await?;
        let later = f.state().await?;
        ensure!(later["unrelated"] == unrelated, "unrelated record changed");
        let StepDecision::Done(replayed) = f.service.change_evidence_operation(&step).await? else {
            panic!("no replay")
        };
        ensure!(
            first == replayed && f.state().await? == later,
            "retry performed another removal"
        );
        ensure!(matches!(
            f.service.read_operation_outcome(token, None).await?,
            OperationOutcome::Completed { .. }
        ));
        Ok::<_, anyhow::Error>(())
    }
    .await;
    let cleanup = f.cleanup().await;
    checked?;
    cleanup
}

#[tokio::test]
async fn rejected_final_receipt_rolls_back_evidence_and_all_affected_counts() -> Result<()> {
    let f = Fixture::create().await?;
    let checked=async {
        for operation in ["add_evidence","delete_evidence"] {
            if operation=="delete_evidence" { f.service.add_evidence(f.belief,f.chunk,0.5).await?; }
            let before=f.state().await?;
            let (token,step)=f.plan(operation,f.args()).await?;
            let audit=db::connect(&config().database).await?;
            let constraint=format!("reject_grounding_result_{}",token.simple());
            audit.batch_execute(&format!("ALTER TABLE mimir_operation_step_replies ADD CONSTRAINT {constraint} CHECK (operation_token <> '{token}'::uuid OR step <> '@operation-result') NOT VALID")).await?;
            let attempted=f.service.change_evidence_operation(&step).await;
            audit.batch_execute(&format!("ALTER TABLE mimir_operation_step_replies DROP CONSTRAINT {constraint}")).await?;
            ensure!(attempted.is_err());
            ensure!(f.state().await?==before,"evidence or posterior escaped rollback");
            f.pending(token,&step).await?;
            ensure!(matches!(f.service.change_evidence_operation(&step).await?,StepDecision::Done(_)));
        }
        Ok::<_,anyhow::Error>(())
    }.await;
    let cleanup = f.cleanup().await;
    checked?;
    cleanup
}

#[tokio::test]
async fn cancelled_evidence_change_keeps_all_data_and_saves_no_answer() -> Result<()> {
    let f = Fixture::create().await?;
    let checked = async {
        for operation in ["add_evidence", "delete_evidence"] {
            let before = f.state().await?;
            let (token, step) = f.plan(operation, f.args()).await?;
            let CancellationDecision::Recorded(cancellation) =
                f.service.record_operation_cancellation(token).await?
            else {
                panic!("not cancelled")
            };
            ensure!(
                f.service.change_evidence_operation(&step).await?
                    == StepDecision::Cancelled(cancellation)
            );
            ensure!(f.state().await? == before);
            ensure!(f
                .service
                .read_operation_step(token, step.id())
                .await?
                .is_none());
            ensure!(f
                .service
                .read_operation_step(token, "@operation-result")
                .await?
                .is_none());
        }
        Ok::<_, anyhow::Error>(())
    }
    .await;
    let cleanup = f.cleanup().await;
    checked?;
    cleanup
}

#[tokio::test]
async fn malformed_originals_missing_passages_and_wrong_steps_cannot_publish() -> Result<()> {
    let f = Fixture::create().await?;
    let checked = async {
        let before = f.state().await?;
        for args in [
            json!({"belief_id":f.belief}),
            json!({"belief_id":f.belief,"chunk_id":f.chunk,"weight":null}),
            json!({"belief_id":f.belief,"chunk_id":f.chunk,"weight":-0.1}),
            json!({"belief_id":f.belief,"chunk_id":f.chunk,"extra":true}),
            json!({"belief_id":f.belief,"chunk_id":identity().await?}),
        ] {
            let (token, step) = f.plan("add_evidence", args).await?;
            ensure!(f.service.change_evidence_operation(&step).await.is_err());
            ensure!(f.state().await? == before);
            f.pending(token, &step).await?;
        }
        let (token, step) = f.plan("delete_belief", json!({"id":f.belief})).await?;
        ensure!(f.service.change_evidence_operation(&step).await.is_err());
        ensure!(f.state().await? == before);
        f.pending(token, &step).await?;
        Ok::<_, anyhow::Error>(())
    }
    .await;
    let cleanup = f.cleanup().await;
    checked?;
    cleanup
}

#[tokio::test]
async fn repeated_numerical_states_leave_evidence_counts_and_token_pending() -> Result<()> {
    use mimir_core::{graph::MemoryType, inference::NumericalDecision};
    let f = Fixture::create().await?;
    let mut a = isolation::seed_belief("grounding cycle A", 0.1, 0.0, MemoryType::Fact).await?;
    let mut b = isolation::seed_belief("grounding cycle B", 0.1, 0.0, MemoryType::Fact).await?;
    if a.id > b.id {
        std::mem::swap(&mut a, &mut b);
    }
    f.store
        .insert_edge(&Edge::new(b.id, a.id, EdgeType::Defeats, 0.7)?)
        .await?;
    f.store
        .insert_edge(&Edge::new(a.id, b.id, EdgeType::Supports, 1.0)?)
        .await?;
    f.store
        .insert_edge(&Edge::new(f.belief, a.id, EdgeType::Supports, 0.0)?)
        .await?;
    let checked = async {
        let before = f.state().await?;
        let cyclic = mimir_json::to_value([
            f.store.get_belief(a.id).await?,
            f.store.get_belief(b.id).await?,
        ])?;
        let mut args = f.args();
        args["weight"] = json!(0.0);
        let (token, step) = f.plan("add_evidence", args).await?;
        let error = f
            .service
            .change_evidence_operation(&step)
            .await
            .unwrap_err();
        let decision = error
            .downcast_ref::<NumericalDecision>()
            .expect("actual numerical decision required");
        ensure!(decision
            .issue()
            .suggested_correction()
            .contains("Open a dialog"));
        ensure!(
            f.state().await? == before,
            "evidence or counts escaped rollback"
        );
        ensure!(
            mimir_json::to_value([
                f.store.get_belief(a.id).await?,
                f.store.get_belief(b.id).await?
            ])? == cyclic
        );
        f.pending(token, &step).await?;
        Ok::<_, anyhow::Error>(())
    }
    .await;
    let audit = db::connect(&config().database).await?;
    let cleanup_cycle=audit.query(&format!("SELECT * FROM ag_catalog.cypher('{}', $$ MATCH (n:Belief) WHERE n.id IN ['{}','{}'] DETACH DELETE n RETURN 1 $$) AS (ok ag_catalog.agtype)",config().database.dbname,a.id,b.id),&[]).await;
    let cleanup = f.cleanup().await;
    checked?;
    cleanup_cycle?;
    cleanup
}
