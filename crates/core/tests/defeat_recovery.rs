//! A saved defeat remains pending until all required posteriors are committed.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;

use anyhow::{ensure, Result};
use mimir_core::{
    config::Config,
    db,
    graph::{Edge, EdgeType, MemoryType},
    inference::EdgeCommittedDecision,
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
    source: Uuid,
    target: Uuid,
    child: Uuid,
    unrelated: Uuid,
}
impl Fixture {
    async fn create() -> Result<Self> {
        let project = format!("defeat-recovery-{}", identity().await?);
        let service = MimirService::connect(&config()).await?;
        let store = AgeStore::new(
            db::connect(&config().database).await?,
            config().database.dbname,
        )?;
        let mut ids = Vec::new();
        for (name, p) in [
            ("source", 0.8),
            ("target", 0.6),
            ("child", 0.4),
            ("unrelated", 0.9),
        ] {
            ids.push(
                isolation::seed_belief_in_project(name, p, 0.1, &project, MemoryType::Fact)
                    .await?
                    .id,
            );
        }
        store
            .insert_edge(&Edge::new(ids[1], ids[2], EdgeType::Supports, 1.0)?)
            .await?;
        service.propagate_from(ids[1]).await?;
        Ok(Self {
            service,
            store,
            project,
            source: ids[0],
            target: ids[1],
            child: ids[2],
            unrelated: ids[3],
        })
    }
    async fn plan(&self, operation: &str, args: Value) -> Result<OperationPlan> {
        let token = self
            .service
            .reserve_operation(&identity().await?.to_string())
            .await?
            .operation_token;
        let binding = OperationBindingRequest::new(operation.into(), args, json!({}))?;
        self.service.bind_operation_request(token, &binding).await?;
        let PlanDecision::Ready(plan) = self
            .service
            .prepare_operation(token, &binding, |_, _| Box::pin(async { Ok(vec![]) }))
            .await?
        else {
            panic!("no plan")
        };
        Ok(plan)
    }
    async fn defeat(&self) -> Result<OperationPlan> {
        self.plan(
            "record_defeat",
            json!({"from_id":self.source,"to_id":self.target,"weight":0.7}),
        )
        .await
    }
    async fn state(&self) -> Result<Value> {
        Ok(
            json!({"source":self.store.get_belief(self.source).await?,"target":self.store.get_belief(self.target).await?,
            "child":self.store.get_belief(self.child).await?,"unrelated":self.store.get_belief(self.unrelated).await?}),
        )
    }
    async fn edges(&self) -> Result<usize> {
        Ok(self
            .store
            .get_incoming_edges(&[self.target])
            .await?
            .iter()
            .filter(|(from, to, kind, _, _)| {
                *from == self.source && *to == self.target && *kind == EdgeType::Defeats
            })
            .count())
    }
    async fn pending_after_edge(&self, plan: &OperationPlan) -> Result<()> {
        let steps = plan.steps();
        ensure!(self
            .service
            .read_operation_step(plan.operation_token(), steps[0].id())
            .await?
            .is_some());
        ensure!(self
            .service
            .read_operation_step(plan.operation_token(), steps[1].id())
            .await?
            .is_none());
        ensure!(matches!(
            self.service
                .read_operation_outcome(plan.operation_token(), None)
                .await?,
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
async fn retry_after_edge_commit_preserves_one_defeat_and_original_completed_answer() -> Result<()>
{
    let f = Fixture::create().await?;
    let checked=async {
        let before=f.state().await?;
        let plan=f.defeat().await?;
        let steps=plan.steps();
        ensure!(steps.len()==2);
        ensure!(matches!(f.store.commit_defeat_step(&steps[0]).await?,StepDecision::Done(_)));
        f.pending_after_edge(&plan).await?;
        ensure!(f.edges().await?==1 && f.state().await?==before,"prefix changed posteriors or lost its edge");
        // A new owner resumes after the first owner's committed reply was lost.
        let reopened=MimirService::connect(&config()).await?;
        let not_before: chrono::DateTime<chrono::Utc> = db::connect(&config().database)
            .await?.query_one("SELECT clock_timestamp()", &[]).await?.get(0);
        let StepDecision::Done(first)=reopened.record_defeat_operation(&plan).await? else {panic!("no completion")};
        ensure!(first.reply==json!({"ok":true}));
        let after=f.state().await?;
        ensure!(after["source"]==before["source"] && after["unrelated"]==before["unrelated"]);
        ensure!(after["target"]["probability"]!=before["target"]["probability"]);
        ensure!(after["child"]["probability"]!=before["child"]["probability"],"descendant not recomputed");
        for id in [f.target, f.child] {
            ensure!(f.store.get_belief(id).await?.unwrap().decay_accounted_at >= not_before);
        }
        ensure!(after["target"]["created_at"] == before["target"]["created_at"]);
        // Completion readback and later retries must return the original reply.
        ensure!(matches!(reopened.read_operation_outcome(plan.operation_token(),None).await?,OperationOutcome::Completed{outcome,..} if outcome.reply()==&first.reply));
        let StepDecision::Done(replayed)=reopened.record_defeat_operation(&plan).await? else {panic!("no replay")};
        ensure!(first==replayed && f.edges().await?==1 && f.state().await?==after);
        Ok::<_,anyhow::Error>(())
    }.await;
    let cleanup = f.cleanup().await;
    checked?;
    cleanup
}

#[tokio::test]
async fn rejected_completion_rolls_back_posteriors_but_keeps_the_original_defeat() -> Result<()> {
    let f = Fixture::create().await?;
    let checked=async {
        let before=f.state().await?;
        let plan=f.defeat().await?;
        let token=plan.operation_token();
        let audit=db::connect(&config().database).await?;
        let constraint=format!("reject_defeat_result_{}",token.simple());
        audit.batch_execute(&format!("ALTER TABLE mimir_operation_step_replies ADD CONSTRAINT {constraint} CHECK(operation_token <> '{token}'::uuid OR step <> '@operation-result') NOT VALID")).await?;
        let attempted=f.service.record_defeat_operation(&plan).await;
        audit.batch_execute(&format!("ALTER TABLE mimir_operation_step_replies DROP CONSTRAINT {constraint}")).await?;
        ensure!(attempted.is_err());
        ensure!(f.edges().await?==1 && f.state().await?==before,"a posterior escaped final-step rollback");
        f.pending_after_edge(&plan).await?;
        ensure!(matches!(f.service.record_defeat_operation(&plan).await?,StepDecision::Done(_)));
        ensure!(f.edges().await?==1);
        Ok::<_,anyhow::Error>(())
    }.await;
    let cleanup = f.cleanup().await;
    checked?;
    cleanup
}

#[tokio::test]
async fn user_cancellation_after_the_edge_keeps_the_prefix_and_blocks_propagation() -> Result<()> {
    let f = Fixture::create().await?;
    let checked = async {
        let before = f.state().await?;
        let plan = f.defeat().await?;
        f.store.commit_defeat_step(&plan.steps()[0]).await?;
        let CancellationDecision::Recorded(receipt) = f
            .service
            .record_operation_cancellation(plan.operation_token())
            .await?
        else {
            panic!("not cancelled")
        };
        ensure!(
            f.service.record_defeat_operation(&plan).await? == StepDecision::Cancelled(receipt)
        );
        ensure!(f.edges().await? == 1 && f.state().await? == before);
        ensure!(f
            .service
            .read_operation_step(plan.operation_token(), plan.steps()[1].id())
            .await?
            .is_none());
        Ok::<_, anyhow::Error>(())
    }
    .await;
    let cleanup = f.cleanup().await;
    checked?;
    cleanup
}

#[tokio::test]
async fn standalone_propagation_replays_the_original_list_after_later_graph_changes() -> Result<()>
{
    let f = Fixture::create().await?;
    let checked = async {
        f.store
            .insert_edge(&Edge::new(f.source, f.target, EdgeType::Defeats, 0.7)?)
            .await?;
        let plan = f.plan("propagate_from", json!({"id":f.source})).await?;
        let step = &plan.steps()[0];
        let not_before: chrono::DateTime<chrono::Utc> = db::connect(&config().database)
            .await?.query_one("SELECT clock_timestamp()", &[]).await?.get(0);
        let StepDecision::Done(first) = f.service.propagate_operation(step).await? else {
            panic!("no propagation")
        };
        for id in [f.target, f.child] {
            ensure!(f.store.get_belief(id).await?.unwrap().decay_accounted_at >= not_before);
        }
        ensure!(first
            .reply
            .as_array()
            .unwrap()
            .iter()
            .any(|v| v["id"] == json!(f.child)));
        f.store
            .insert_edge(&Edge::new(f.source, f.child, EdgeType::Defeats, 0.9)?)
            .await?;
        f.service.propagate_from(f.source).await?;
        let later = f.state().await?;
        let StepDecision::Done(replayed) = f.service.propagate_operation(step).await? else {
            panic!("no replay")
        };
        ensure!(replayed == first && f.state().await? == later);
        Ok::<_, anyhow::Error>(())
    }
    .await;
    let cleanup = f.cleanup().await;
    checked?;
    cleanup
}

#[tokio::test]
async fn invalid_original_requests_cannot_write_an_edge_or_save_completion() -> Result<()> {
    let f = Fixture::create().await?;
    let checked = async {
        let before = f.state().await?;
        for arguments in [
            json!({"from_id":f.source,"to_id":f.target}),
            json!({"from_id":f.source,"to_id":f.target,"weight":-0.1}),
            json!({"from_id":f.source,"to_id":f.target,"weight":0.5,"extra":true}),
            json!({"from_id":f.source,"to_id":identity().await?,"weight":0.5}),
        ] {
            let plan = f.plan("record_defeat", arguments).await?;
            ensure!(f.service.record_defeat_operation(&plan).await.is_err());
            ensure!(f.state().await? == before && f.edges().await? == 0);
            for step in plan.steps() {
                ensure!(f
                    .service
                    .read_operation_step(plan.operation_token(), step.id())
                    .await?
                    .is_none());
            }
            ensure!(matches!(
                f.service
                    .read_operation_outcome(plan.operation_token(), None)
                    .await?,
                OperationOutcome::Pending { .. }
            ));
        }
        let plan = f
            .plan("propagate_from", json!({"id":identity().await?}))
            .await?;
        let error = f
            .service
            .propagate_operation(&plan.steps()[0])
            .await
            .unwrap_err();
        ensure!(error
            .downcast_ref::<mimir_core::interaction::RequestCorrection>()
            .is_some());
        ensure!(f.state().await? == before);
        ensure!(matches!(
            f.service
                .read_operation_outcome(plan.operation_token(), None)
                .await?,
            OperationOutcome::Pending { .. }
        ));
        let other = f.plan("propagate_from", json!({"id":f.source})).await?;
        ensure!(f.service.record_defeat_operation(&other).await.is_err());
        ensure!(f.state().await? == before && f.edges().await? == 0);
        Ok::<_, anyhow::Error>(())
    }
    .await;
    let cleanup = f.cleanup().await;
    checked?;
    cleanup
}

#[tokio::test]
async fn repeated_numerical_states_keep_the_defeat_pending_and_explain_how_to_resume() -> Result<()>
{
    let f = Fixture::create().await?;
    let first =
        isolation::seed_belief_in_project("cycle A", 0.1, 0.0, &f.project, MemoryType::Fact)
            .await?;
    let second =
        isolation::seed_belief_in_project("cycle B", 0.1, 0.0, &f.project, MemoryType::Fact)
            .await?;
    let (a, b) = if first.id < second.id {
        (first, second)
    } else {
        (second, first)
    };
    f.store
        .insert_edge(&Edge::new(b.id, a.id, EdgeType::Defeats, 0.7)?)
        .await?;
    f.store
        .insert_edge(&Edge::new(a.id, b.id, EdgeType::Supports, 1.0)?)
        .await?;
    let checked = async {
        let before = json!([
            f.store.get_belief(a.id).await?,
            f.store.get_belief(b.id).await?
        ]);
        let plan = f
            .plan(
                "record_defeat",
                json!({"from_id":f.source,"to_id":a.id,"weight":0.0}),
            )
            .await?;
        for _ in 0..2 {
            let error = f.service.record_defeat_operation(&plan).await.unwrap_err();
            let decision = error
                .downcast_ref::<EdgeCommittedDecision>()
                .expect("committed-prefix decision");
            let report = decision.response();
            ensure!(report["operation_token"] == json!(plan.operation_token()));
            ensure!(
                report["operation_status"] == "pending"
                    && report["posterior_publication"] == "not_performed"
            );
            ensure!(
                json!([
                    f.store.get_belief(a.id).await?,
                    f.store.get_belief(b.id).await?
                ]) == before
            );
            f.pending_after_edge(&plan).await?;
        }
        let edges = f.store.get_incoming_edges(&[a.id]).await?;
        ensure!(
            edges
                .iter()
                .filter(|(from, to, kind, _, _)| *from == f.source
                    && *to == a.id
                    && *kind == EdgeType::Defeats)
                .count()
                == 1
        );
        Ok::<_, anyhow::Error>(())
    }
    .await;
    let cleanup = f.cleanup().await;
    checked?;
    cleanup
}
