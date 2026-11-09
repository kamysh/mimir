//! A source version and its original response form one registered publication.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;
use anyhow::{ensure, Result};
use mimir_core::{
    assessment::{ItemKind, LearningItem},
    config::Config,
    db,
    graph::Belief,
    interaction::RequestCorrection,
    learning::*,
    learning_sources::SourceRecord,
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
async fn setup() -> Result<(AgeStore, MimirService)> {
    let cfg = config();
    Ok((
        AgeStore::new(
            db::connect(&cfg.database).await?,
            cfg.database.dbname.clone(),
        )?,
        MimirService::connect(&cfg).await?,
    ))
}
async fn experience(named_item: bool) -> Result<Experience> {
    let id = identity().await?;
    let mut e = Experience {
        id,
        project: format!("source-operation-{id}"),
        context: "observed request".into(),
        action: "keep the original incident".into(),
        outcome: Outcome::Unknown,
        source: ObservationSource::AgentReport,
        evidence: vec![],
        belief_ids: vec![],
        pattern_id: None,
        learning_items: vec![],
        source_records: vec![],
    };
    if named_item {
        e.evidence.push("event/1".into());
        e.source_records.push(SourceRecord {
            source_ref: "event/1".into(),
            actor: "agent".into(),
            provenance: ObservationSource::AgentReport,
            text: "I propose keeping the original incident.".into(),
            recorded_at: None,
        });
        e.learning_items.push(LearningItem {
            id: None,
            key: Some("proposal".into()),
            kind: ItemKind::Suggestion,
            source_ref: "event/1".into(),
            actor: "agent".into(),
            statement: "I propose keeping the original incident.".into(),
            conditions: "not yet verified".into(),
            predictions: vec![],
        });
    }
    Ok(e)
}
struct Prepared {
    token: Uuid,
    step: RegisteredStep,
    binding: OperationBindingRequest,
}
async fn plan(service: &MimirService, e: &Experience, expected: i64) -> Result<Prepared> {
    let token = service
        .reserve_operation(&identity().await?.to_string())
        .await?
        .operation_token;
    let binding = OperationBindingRequest::new(
        "record_experience".into(),
        json!({"experience":e,"expected_revision":expected}),
        json!({}),
    )?;
    service.bind_operation_request(token, &binding).await?;
    let PlanDecision::Ready(plan) = service
        .prepare_operation(token, &binding, |_, _| Box::pin(async { Ok(vec![]) }))
        .await?
    else {
        panic!("missing source plan")
    };
    ensure!(plan.steps().len() == 1);
    Ok(Prepared {
        token,
        step: plan.steps()[0].clone(),
        binding,
    })
}
async fn done(service: &MimirService, p: &Prepared) -> Result<StepReceipt> {
    let StepDecision::Done(reply) = service.record_experience_operation(&p.step).await? else {
        panic!("source not completed")
    };
    ensure!(service.read_operation_step(p.token, p.step.id()).await? == Some(reply.clone()));
    ensure!(
        service
            .read_operation_step(p.token, "@operation-result")
            .await?
            .expect("saved result")
            .reply
            == reply.reply
    );
    Ok(reply)
}
async fn pending(service: &MimirService, p: &Prepared) -> Result<()> {
    ensure!(service
        .read_operation_step(p.token, p.step.id())
        .await?
        .is_none());
    ensure!(service
        .read_operation_step(p.token, "@operation-result")
        .await?
        .is_none());
    ensure!(service
        .read_operation_cancellation(p.token)
        .await?
        .is_none());
    ensure!(matches!(
        service.read_operation_outcome(p.token, None).await?,
        OperationOutcome::Pending { .. }
    ));
    Ok(())
}
async fn owners(id: Uuid) -> Result<Value> {
    let rows=db::connect(&config().database).await?.query(
        "SELECT item_key,item_id,source_ref,actor FROM mimir_learning_item_owners WHERE experience_id=$1 ORDER BY item_key",&[&id]).await?;
    Ok(Value::Array(
        rows.iter()
            .map(|r| {
                json!({"key":r.get::<_,Option<&str>>(0),"id":r.get::<_,Uuid>(1),
        "source_ref":r.get::<_,&str>(2),"actor":r.get::<_,&str>(3)})
            })
            .collect(),
    ))
}

#[tokio::test]
async fn source_replay_keeps_original_incident_revision_and_postgres_item_id_after_a_later_correction(
) -> Result<()> {
    let (_, service) = setup().await?;
    let e = experience(true).await?;
    let first = plan(&service, &e, 0).await?;
    let original = done(&service, &first).await?;
    let state: ExperienceState = serde_json::from_value(original.reply.clone())?;
    ensure!(
        state.experience.id == e.id
            && state.revision == 1
            && state.review_revision == 0
            && state.reviewed_revision == 0
    );
    let allocated = state.item_ids["proposal"];
    ensure!(state.experience.learning_items[0].id == Some(allocated));
    ensure!(owners(e.id).await?[0]["id"] == json!(allocated));
    let mut correction = e.clone();
    correction.action = "add the observed correction".into();
    correction.learning_items[0].conditions = "updated interpretation".into();
    let corrected = plan(&service, &correction, 1).await?;
    let answer = done(&service, &corrected).await?;
    let new_state: ExperienceState = serde_json::from_value(answer.reply.clone())?;
    ensure!(new_state.revision == 2 && new_state.experience.id == e.id);
    ensure!(new_state.item_ids["proposal"] == allocated);
    let before = service.experience_history(e.id).await?;
    let ownership = owners(e.id).await?;
    let reopened = MimirService::connect(&config()).await?;
    ensure!(done(&reopened, &first).await? == original);
    ensure!(done(&reopened, &corrected).await? == answer);
    ensure!(service.experience_history(e.id).await? == before);
    ensure!(owners(e.id).await? == ownership);
    ensure!(
        service
            .get_experience(e.id)
            .await?
            .expect("current")
            .revision
            == 2
    );
    let changed = OperationBindingRequest::new(
        "record_experience".into(),
        json!({"experience":correction,"expected_revision":2}),
        json!({}),
    )?;
    ensure!(
        matches!(service.bind_operation_request(first.token,&changed).await?,OperationBindingDecision::ChangedRequest(original) if original.request==first.binding)
    );
    Ok(())
}

#[tokio::test]
async fn source_correction_retracts_active_review_once_and_preserves_history_and_other_projects(
) -> Result<()> {
    let (store, service) = setup().await?;
    let mut e = experience(false).await?;
    let mut target = Belief::new_in_project("source target".into(), 0.5, 0.0, e.project.clone())?;
    target.id = identity().await?;
    store.insert_belief(&target).await?;
    let mut foreign = Belief::new_in_project(
        "unrelated project".into(),
        0.7,
        0.4,
        format!("other-{}", e.id),
    )?;
    foreign.id = identity().await?;
    store.insert_belief(&foreign).await?;
    let foreign_before = serde_json::to_value(store.get_belief(foreign.id).await?)?;
    e.evidence.push("isolated fixture observed support".into());
    e.belief_ids.push(target.id);
    done(&service, &plan(&service, &e, 0).await?).await?;
    let review = Review {
        experience_id: e.id,
        experience_revision: 1,
        reviewer: "source test".into(),
        rationale: "observed support".into(),
        feedback: vec![Feedback {
            belief_id: target.id,
            verdict: Verdict::Support,
            weight: 1.0,
        }],
        links: vec![],
        superseded_beliefs: vec![],
        candidates: vec![],
        candidate_feedback: vec![],
        candidate_links: vec![],
        assessments: vec![],
        extracted_items: vec![],
        source_coverage: vec![],
    };
    service.review_experience(&review, 0).await?;
    ensure!(store.get_belief(target.id).await?.expect("target").alpha > target.alpha0);
    let history = service.experience_history(e.id).await?;
    let mut correction = e.clone();
    correction.action = "correct the observation".into();
    let p = plan(&service, &correction, 1).await?;
    let reply = done(&service, &p).await?;
    let state: ExperienceState = serde_json::from_value(reply.reply.clone())?;
    ensure!(state.revision == 2 && state.review_revision == 1 && state.reviewed_revision == 1);
    let after = store.get_belief(target.id).await?.expect("target");
    ensure!(after.alpha == target.alpha0 && after.beta == target.beta0);
    let corrected_history = service.experience_history(e.id).await?;
    ensure!(corrected_history["reviews"] == history["reviews"]);
    ensure!(
        corrected_history["experiences"]
            .as_array()
            .expect("experience versions")
            .len()
            == 2
    );
    let stable = serde_json::to_value(&after)?;
    ensure!(done(&service, &p).await? == reply);
    ensure!(serde_json::to_value(store.get_belief(target.id).await?.expect("target"))? == stable);
    ensure!(serde_json::to_value(store.get_belief(foreign.id).await?)? == foreign_before);
    Ok(())
}

#[tokio::test]
async fn stale_and_malformed_source_requests_remain_pending_with_user_controlled_repair(
) -> Result<()> {
    let (_, service) = setup().await?;
    let e = experience(true).await?;
    done(&service, &plan(&service, &e, 0).await?).await?;
    let history = service.experience_history(e.id).await?;
    let ownership = owners(e.id).await?;
    for (mut bad, expected) in [(e.clone(), 1), (e.clone(), 0), (e.clone(), -1)] {
        if expected == 1 {
            bad.project = "wrong project".into();
        }
        if expected == 0 {
            bad.action = "changed with stale revision".into();
        }
        let p = plan(&service, &bad, expected).await?;
        let error = service
            .record_experience_operation(&p.step)
            .await
            .unwrap_err();
        let refused = error
            .downcast_ref::<RequestCorrection>()
            .expect("normal source correction");
        ensure!(refused.correction().issues()[0]
            .suggested_correction()
            .contains("ask the user whether to cancel"));
        pending(&service, &p).await?;
        ensure!(service.experience_history(e.id).await? == history);
        ensure!(owners(e.id).await? == ownership);
    }
    let mut blank = experience(false).await?;
    blank.context = " \t\n".into();
    let error = service.record_experience(&blank, 0).await.unwrap_err();
    let refused = error
        .downcast_ref::<RequestCorrection>()
        .expect("normal blank-context correction");
    ensure!(
        refused.correction().issues()[0].fault().path
            == vec![
                mimir_core::validation::Segment::Key("experience".into()),
                mimir_core::validation::Segment::Key("context".into())
            ]
    );
    ensure!(service.get_experience(blank.id).await?.is_none());
    Ok(())
}

#[tokio::test]
async fn final_answer_failure_rolls_back_source_version_and_item_ownership_before_retry(
) -> Result<()> {
    let (_, service) = setup().await?;
    let e = experience(true).await?;
    let p = plan(&service, &e, 0).await?;
    let audit = db::connect(&config().database).await?;
    let name = format!("fail_source_answer_{}", identity().await?.simple());
    audit.batch_execute(&format!("CREATE FUNCTION public.{name}() RETURNS trigger LANGUAGE plpgsql AS $body$ BEGIN IF NEW.operation_token='{}'::uuid AND NEW.step='@operation-result' THEN RAISE EXCEPTION 'controlled source final-answer failure'; END IF; RETURN NEW; END $body$; CREATE TRIGGER {name} BEFORE INSERT ON public.mimir_operation_step_replies FOR EACH ROW EXECUTE FUNCTION public.{name}();",p.token)).await?;
    let failed = service.record_experience_operation(&p.step).await;
    audit.batch_execute(&format!("DROP TRIGGER {name} ON public.mimir_operation_step_replies; DROP FUNCTION public.{name}();")).await?;
    ensure!(failed.is_err());
    pending(&service, &p).await?;
    ensure!(service.get_experience(e.id).await?.is_none());
    ensure!(owners(e.id)
        .await?
        .as_array()
        .expect("ownership")
        .is_empty());
    let reply = done(&service, &p).await?;
    ensure!(reply.reply["revision"] == json!(1));
    let count: i64 = audit
        .query_one(
            "SELECT count(*) FROM mimir_experiences WHERE project=$1",
            &[&e.project],
        )
        .await?
        .get(0);
    ensure!(count == 1);
    let versions: i64 = audit
        .query_one(
            "SELECT count(*) FROM mimir_experience_versions WHERE experience_id=$1",
            &[&e.id],
        )
        .await?
        .get(0);
    ensure!(versions == 1);
    Ok(())
}
