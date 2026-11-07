//! Whole-closure deletion in the maintained disposable PostgreSQL fixture.
#[allow(dead_code)]
#[path = "../../../tests/support/isolation.rs"]
mod isolation;
use anyhow::Result;
use mimir_core::{
    config::Config,
    db,
    documents::DocumentChunk,
    graph::{Belief, Pattern},
    learning::*,
    store::*,
    MimirService,
};
use serde_json::json;
use uuid::Uuid;

fn config() -> Config {
    Config {
        database: isolation::fixture().database_config(),
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
    }
}
struct Owned {
    project: String,
    belief: Uuid,
    pattern: Uuid,
    chunk: Uuid,
    experience: Uuid,
}
async fn seed(store: &AgeStore, service: &MimirService) -> Result<Owned> {
    let audit = db::connect(&config().database).await?;
    let ids = audit
        .query_one(
            "SELECT gen_random_uuid(),gen_random_uuid(),gen_random_uuid(),gen_random_uuid()",
            &[],
        )
        .await?;
    let (belief, pattern, chunk, experience) = (ids.get(0), ids.get(1), ids.get(2), ids.get(3));
    let project = format!("atomic-project-{experience}");
    let mut b = Belief::new_in_project("owned belief".into(), 0.7, 0.5, project.clone())?;
    b.id = belief;
    store.insert_belief(&b).await?;
    store
        .insert_belief_embedding(belief, &[0.1, 0.2, 0.3])
        .await?;
    let mut p = Pattern::new_in_project(
        "owned situation".into(),
        "owned approach".into(),
        0.5,
        project.clone(),
    )?;
    p.id = pattern;
    store.insert_pattern(&p).await?;
    store
        .insert_document_chunk(&DocumentChunk::with_id(
            chunk,
            format!("/{project}.md"),
            vec![],
            "owned supporting passage".into(),
            None,
            Some(project.clone()),
        ))
        .await?;
    store
        .insert_chunk_embedding(chunk, &[0.1, 0.2, 0.3])
        .await?;
    service
        .record_experience(
            &Experience {
                id: experience,
                project: project.clone(),
                context: "owned source".into(),
                action: "test atomic deletion".into(),
                outcome: Outcome::Success,
                source: ObservationSource::ToolResult,
                evidence: vec!["private fixture".into()],
                belief_ids: vec![],
                pattern_id: None,
                learning_items: vec![],
                source_records: vec![],
            },
            0,
        )
        .await?;
    Ok(Owned {
        project,
        belief,
        pattern,
        chunk,
        experience,
    })
}
async fn present(store: &AgeStore, owned: &Owned, expected: bool) -> Result<()> {
    assert_eq!(store.get_belief(owned.belief).await?.is_some(), expected);
    assert_eq!(store.get_pattern(owned.pattern).await?.is_some(), expected);
    assert_eq!(
        store.get_chunk_by_id(owned.chunk).await?.is_some(),
        expected
    );
    let audit = db::connect(&config().database).await?;
    for (table, column, id) in [
        ("belief_embeddings", "belief_id", owned.belief),
        ("chunk_embeddings", "chunk_id", owned.chunk),
        ("mimir_experiences", "id", owned.experience),
        (
            "mimir_experience_versions",
            "experience_id",
            owned.experience,
        ),
    ] {
        assert_eq!(
            audit
                .query_opt(
                    &format!("SELECT 1 FROM public.{table} WHERE {column}=$1"),
                    &[&id]
                )
                .await?
                .is_some(),
            expected,
            "{table}"
        );
    }
    Ok(())
}
async fn setup() -> Result<(AgeStore, MimirService)> {
    let cfg = config();
    let service = MimirService::connect(&cfg).await?;
    let store = AgeStore::new(db::connect(&cfg.database).await?, cfg.database.dbname)?;
    Ok((store, service))
}
async fn admitted(service: &MimirService, owned: &Owned) -> Result<(Uuid, RegisteredStep)> {
    let token = service.reserve_operation().await?.operation_token;
    let request = OperationBindingRequest::new(
        "delete_project".into(),
        json!({"project":owned.project}),
        json!({}),
    )?;
    service.bind_operation_request(token, &request).await?;
    let PlanDecision::Ready(plan) = service
        .prepare_operation(token, &request, |_, _| Box::pin(async { Ok(vec![]) }))
        .await?
    else {
        panic!("plan missing")
    };
    let steps = plan.steps();
    assert_eq!(steps.len(), 1);
    Ok((token, steps[0].clone()))
}

#[tokio::test]
async fn deletion_and_original_result_commit_once_without_touching_another_project() -> Result<()> {
    let (store, service) = setup().await?;
    let removed = seed(&store, &service).await?;
    let retained = seed(&store, &service).await?;
    present(&store, &removed, true).await?;
    present(&store, &retained, true).await?;
    let retained_before = serde_json::to_value(store.get_belief(retained.belief).await?)?;
    let (token, step) = admitted(&service, &removed).await?;
    let StepDecision::Done(first) = service.delete_project_operation(&step).await? else {
        panic!("deletion did not complete")
    };
    assert_eq!(first.reply, json!({"deleted":2}));
    present(&store, &removed, false).await?;
    present(&store, &retained, true).await?;
    assert_eq!(
        serde_json::to_value(store.get_belief(retained.belief).await?)?,
        retained_before
    );
    drop(service);
    let reopened = MimirService::connect(&config()).await?;
    let StepDecision::Done(retry) = reopened.delete_project_operation(&step).await? else {
        panic!("retry missing")
    };
    assert_eq!(retry, first);
    let OperationOutcome::Completed { outcome, .. } =
        reopened.read_operation_outcome(token, None).await?
    else {
        panic!("result missing")
    };
    assert_eq!(outcome.reply(), &json!({"deleted":2}));
    assert_eq!(reopened.delete_project(&retained.project).await?, 2);
    present(&store, &retained, false).await?;
    Ok(())
}

#[tokio::test]
async fn rejecting_the_result_rolls_back_graph_vectors_learning_and_step_answer() -> Result<()> {
    let (store, service) = setup().await?;
    let owned = seed(&store, &service).await?;
    let (token, step) = admitted(&service, &owned).await?;
    let audit = db::connect(&config().database).await?;
    let constraint = format!("reject_project_result_{}", token.simple());
    audit.batch_execute(&format!("ALTER TABLE mimir_operation_step_replies ADD CONSTRAINT {constraint} CHECK (operation_token <> '{token}'::uuid OR step <> '@operation-result') NOT VALID")).await?;
    let attempted = service.delete_project_operation(&step).await;
    audit
        .batch_execute(&format!(
            "ALTER TABLE mimir_operation_step_replies DROP CONSTRAINT {constraint}"
        ))
        .await?;
    assert!(attempted.is_err());
    present(&store, &owned, true).await?;
    assert!(service
        .read_operation_step(token, step.id())
        .await?
        .is_none());
    assert!(matches!(
        service.read_operation_outcome(token, None).await?,
        OperationOutcome::Pending { .. }
    ));
    let StepDecision::Done(saved) = service.delete_project_operation(&step).await? else {
        panic!("retry failed")
    };
    assert_eq!(saved.reply, json!({"deleted":2}));
    present(&store, &owned, false).await?;
    Ok(())
}
