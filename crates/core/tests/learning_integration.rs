//! Run only against a disposable database; intentionally uses real AGE and migrations.
use mimir_core::{
    config::{Config, DatabaseConfig, SslMode},
    graph::{EdgeType, MemoryType},
    learning::*,
    MimirService,
};
use uuid::Uuid;

async fn service() -> MimirService {
    let dbname = std::env::var("MIMIR_DBNAME").expect("isolated MIMIR_DBNAME required");
    assert!(
        dbname.starts_with("mimir_learning_test"),
        "refusing non-test database"
    );
    MimirService::connect(&Config {
        database: DatabaseConfig {
            host: std::env::var("MIMIR_HOST").unwrap(),
            port: std::env::var("MIMIR_PORT").unwrap().parse().unwrap(),
            user: std::env::var("MIMIR_USER").unwrap(),
            dbname,
            ssl_mode: SslMode::Disable,
            ssl_root_cert: None,
            ssl_client_cert: None,
            ssl_client_key: None,
        },
        embeddings: None,
    })
    .await
    .unwrap()
}
fn experience(project: &str) -> Experience {
    Experience {
        id: Uuid::new_v4(),
        project: project.into(),
        context: "keyboard session lifecycle".into(),
        action: "restart stale process".into(),
        outcome: Outcome::Success,
        source: ObservationSource::ToolResult,
        evidence: vec!["test receipt: new process loaded changed configuration".into()],
        belief_ids: vec![],
        pattern_id: None,
    }
}
fn review(e: &Experience) -> Review {
    Review {
        experience_id: e.id,
        experience_revision: 1,
        reviewer: "test-reviewer".into(),
        rationale: "intervention compared with observed result".into(),
        feedback: vec![],
        links: vec![],
        superseded_beliefs: vec![],
    }
}
#[tokio::test]
async fn learning_cycle_retry_revision_causal_projection_and_retraction() {
    let svc = service().await;
    let project = format!("learning-{}", Uuid::new_v4());
    let a = svc
        .add_belief_in_project(
            "restart stale process",
            0.8,
            0.0,
            &project,
            MemoryType::Experiential,
        )
        .await
        .unwrap();
    let b = svc
        .add_belief_in_project(
            "keyboard layout updates",
            0.3,
            0.0,
            &project,
            MemoryType::Experiential,
        )
        .await
        .unwrap();
    let mut e = experience(&project);
    e.belief_ids = vec![a.id, b.id];
    let first = svc.record_experience(&e, 0).await.unwrap();
    assert_eq!(first.revision, 1);
    assert_eq!(svc.record_experience(&e, 0).await.unwrap().revision, 1);
    let mut r = review(&e);
    r.links.push(LearningLink {
        from_id: a.id,
        to_id: b.id,
        relation: EdgeType::Causes,
        weight: 0.8,
    });
    let done = svc.review_experience(&r, 0).await.unwrap();
    assert_eq!(done.reviewed_revision, 1);
    let after = svc.get_belief(b.id).await.unwrap().unwrap();
    assert!(after.probability.value() > b.probability.value());
    svc.review_experience(&r, 0).await.unwrap();
    assert_eq!(
        svc.get_belief(b.id).await.unwrap().unwrap().alpha,
        after.alpha
    );
    assert!(svc
        .pending_experiences(Some(&project), 10)
        .await
        .unwrap()
        .is_empty());
    let off = svc.query_intervention(a.id, 0.0).await.unwrap();
    let on = svc.query_intervention(a.id, 1.0).await.unwrap();
    let value = |xs: Vec<(Uuid, mimir_core::graph::Probability)>| {
        xs.into_iter()
            .find(|(id, _)| *id == b.id)
            .unwrap()
            .1
            .value()
    };
    assert!(value(on) > value(off));
    assert_eq!(
        svc.get_belief(b.id).await.unwrap().unwrap().alpha,
        after.alpha,
        "intervention is read-only"
    );
    e.outcome = Outcome::Failure;
    e.evidence = vec!["later independent check disproved the result".into()];
    svc.record_experience(&e, 1).await.unwrap();
    assert!(
        svc.review_experience(&r, 1).await.is_err(),
        "stale result refused"
    );
    assert!(svc.query_intervention(a.id, 1.0).await.unwrap().is_empty());
    assert!((svc.get_belief(b.id).await.unwrap().unwrap().alpha - b.alpha).abs() < 1e-9);
    assert_eq!(
        svc.pending_experiences(Some(&project), 10)
            .await
            .unwrap()
            .len(),
        1
    );
    let history = svc.experience_history(e.id).await.unwrap();
    assert_eq!(history["experiences"].as_array().unwrap().len(), 2);
    assert_eq!(history["reviews"].as_array().unwrap().len(), 1);
    svc.delete_project(&project).await.unwrap();
    assert!(svc.get_experience(e.id).await.unwrap().is_none());
}
#[tokio::test]
async fn supersession_is_reversible_and_feedback_survives_propagation() {
    let svc = service().await;
    let project = format!("learning-{}", Uuid::new_v4());
    let a = svc
        .add_belief_in_project(
            "keyboard stale advice",
            0.99,
            0.99,
            &project,
            MemoryType::Experiential,
        )
        .await
        .unwrap();
    let b = svc
        .add_belief_in_project(
            "keyboard corrected advice",
            0.8,
            0.0,
            &project,
            MemoryType::Experiential,
        )
        .await
        .unwrap();
    svc.add_edge(b.id, a.id, EdgeType::Supports, 0.2)
        .await
        .unwrap();
    let e = experience(&project);
    svc.record_experience(&e, 0).await.unwrap();
    let mut r = review(&e);
    r.feedback.push(Feedback {
        belief_id: a.id,
        verdict: Verdict::Defeat,
        weight: 1.0,
    });
    r.superseded_beliefs.push(a.id);
    svc.review_experience(&r, 0).await.unwrap();
    assert!(!svc
        .query_relevant("keyboard", 10, Some(&project), None)
        .await
        .unwrap()
        .iter()
        .any(|x| x.id == a.id));
    let before = svc.get_belief(a.id).await.unwrap().unwrap();
    svc.propagate_from(b.id).await.unwrap();
    let after = svc.get_belief(a.id).await.unwrap().unwrap();
    assert_eq!(before.beta, after.beta);
    r.feedback.clear();
    r.superseded_beliefs.clear();
    r.rationale = "review was mistaken; retract it".into();
    svc.review_experience(&r, 1).await.unwrap();
    assert!(svc
        .query_relevant("keyboard", 10, Some(&project), None)
        .await
        .unwrap()
        .iter()
        .any(|x| x.id == a.id));
    assert!((svc.get_belief(a.id).await.unwrap().unwrap().beta - a.beta0).abs() < 1e-9);
    svc.delete_project(&project).await.unwrap();
}
#[tokio::test]
async fn scoped_pattern_outcomes_replace_instead_of_accumulate() {
    let svc = service().await;
    let project = format!("learning-{}", Uuid::new_v4());
    let p = svc
        .add_pattern_in_project(
            "keyboard session lifecycle",
            "restart stale process",
            0.99,
            Some(&project),
        )
        .await
        .unwrap();
    let mut e = experience(&project);
    e.pattern_id = Some(p.id);
    svc.record_experience(&e, 0).await.unwrap();
    svc.record_experience(&e, 0).await.unwrap();
    let context = svc
        .query_learning_context("keyboard", &project, 5)
        .await
        .unwrap();
    assert_eq!(context.patterns[0].successes, 1);
    assert_eq!(context.patterns[0].observed_success_probability, 2.0 / 3.0);
    e.outcome = Outcome::Failure;
    svc.record_experience(&e, 1).await.unwrap();
    let context = svc
        .query_learning_context("keyboard", &project, 5)
        .await
        .unwrap();
    assert_eq!(context.patterns[0].successes, 0);
    assert_eq!(context.patterns[0].failures, 1);
    assert_eq!(context.patterns[0].observed_success_probability, 1.0 / 3.0);
    let mut report = experience(&project);
    report.pattern_id = Some(p.id);
    report.source = ObservationSource::AgentReport;
    svc.record_experience(&report, 0).await.unwrap();
    assert_eq!(
        svc.query_learning_context("keyboard", &project, 5)
            .await
            .unwrap()
            .patterns[0]
            .unknown,
        1
    );
    let mut foreign = experience("another-project");
    foreign.pattern_id = Some(p.id);
    assert!(svc.record_experience(&foreign, 0).await.is_err());
    let foreign_belief = svc
        .add_belief_in_project(
            "other",
            0.5,
            0.5,
            "another-project",
            MemoryType::Experiential,
        )
        .await
        .unwrap();
    let mut r = review(&e);
    r.experience_revision = 2;
    r.feedback.push(Feedback {
        belief_id: foreign_belief.id,
        verdict: Verdict::Support,
        weight: 1.0,
    });
    assert!(svc.review_experience(&r, 0).await.is_err());
    assert_eq!(
        svc.get_experience(e.id)
            .await
            .unwrap()
            .unwrap()
            .review_revision,
        0,
        "failure must not acknowledge work"
    );
    svc.delete_belief(foreign_belief.id).await.unwrap();
    svc.delete_project(&project).await.unwrap();
}

#[tokio::test]
async fn concurrent_review_conflict_is_atomic_and_keeps_manual_edges() {
    let svc = service().await;
    let other = service().await;
    let project = format!("learning-{}", Uuid::new_v4());
    let a = svc
        .add_belief_in_project("cause", 0.8, 0.0, &project, MemoryType::Experiential)
        .await
        .unwrap();
    let b = svc
        .add_belief_in_project("effect", 0.2, 0.0, &project, MemoryType::Experiential)
        .await
        .unwrap();
    svc.add_edge(a.id, b.id, EdgeType::Supports, 0.3)
        .await
        .unwrap();
    let e = experience(&project);
    svc.record_experience(&e, 0).await.unwrap();
    let mut r1 = review(&e);
    r1.links.push(LearningLink {
        from_id: a.id,
        to_id: b.id,
        relation: EdgeType::Causes,
        weight: 0.8,
    });
    let mut r2 = r1.clone();
    r2.links[0].weight = 0.2;
    r2.rationale = "competing assessment".into();
    let (x, y) = tokio::join!(
        svc.review_experience(&r1, 0),
        other.review_experience(&r2, 0)
    );
    assert_ne!(x.is_ok(), y.is_ok(), "only one revision may win");
    let mut retraction = review(&e);
    retraction.rationale = "remove the learned link only".into();
    svc.review_experience(&retraction, 1).await.unwrap();
    let b_after = svc.get_belief(b.id).await.unwrap().unwrap();
    assert!(
        (b_after.alpha - (b.alpha0 + 0.3 * 0.8 * mimir_core::graph::EVIDENCE_UNIT)).abs() < 1e-9,
        "manual support survives"
    );
    assert!(
        svc.query_intervention(a.id, 1.0).await.unwrap().is_empty(),
        "learned causal edge removed"
    );
    svc.delete_project(&project).await.unwrap();
}

#[tokio::test]
async fn incremental_queue_handles_more_than_two_hundred_experiences() {
    let svc = service().await;
    let project = format!("learning-{}", Uuid::new_v4());
    for _ in 0..201 {
        svc.record_experience(&experience(&project), 0)
            .await
            .unwrap();
    }
    let mut reviewed = 0;
    loop {
        let batch = svc.pending_experiences(Some(&project), 30).await.unwrap();
        if batch.is_empty() {
            break;
        }
        assert!(batch.len() <= 30);
        for item in batch {
            svc.review_experience(&review(&item.experience), item.review_revision)
                .await
                .unwrap();
            reviewed += 1;
        }
    }
    assert_eq!(reviewed, 201);
    svc.delete_project(&project).await.unwrap();
}

#[tokio::test]
async fn contradiction_review_changes_detection_without_triggering_evidence_propagation() {
    let svc = service().await;
    let project = format!("learning-{}", Uuid::new_v4());
    let a = svc.add_belief_in_project("claim A", 0.8, 0.1, &project, MemoryType::Experiential).await.unwrap();
    let b = svc.add_belief_in_project("claim B", 0.7, 0.1, &project, MemoryType::Experiential).await.unwrap();
    // Legacy support insertion deliberately does not trigger propagation.
    svc.add_edge(a.id, b.id, EdgeType::Supports, 1.0).await.unwrap();
    let e = experience(&project);
    svc.record_experience(&e, 0).await.unwrap();
    let mut r = review(&e);
    r.links.push(LearningLink { from_id:a.id, to_id:b.id, relation:EdgeType::Contradicts, weight:1.0 });
    svc.review_experience(&r, 0).await.unwrap();
    assert_eq!(svc.get_belief(b.id).await.unwrap().unwrap().alpha, b.alpha);
    assert!(!svc.get_contradictions(Some(&project)).await.unwrap().is_empty());
    r.links.clear();
    svc.review_experience(&r, 1).await.unwrap();
    assert!(svc.get_contradictions(Some(&project)).await.unwrap().is_empty());
    svc.delete_project(&project).await.unwrap();
}
