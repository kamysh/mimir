//! Run only against a disposable database; intentionally uses real AGE and migrations.
#[allow(dead_code)] // Shared guard exposes helpers for several test targets.
#[path = "../../../tests/support/isolation.rs"]
mod isolation;

use mimir_core::{
    config::Config,
    db,
    graph::{EdgeType, MemoryType},
    learning::*,
    store::AgeStore,
    MimirService,
};
use uuid::Uuid;

// Both pager tests include global beliefs. Keep their offset-based reads from
// racing with the other test's temporary global belief.
static PAGE_TEST_LOCK: tokio::sync::Mutex<()> = tokio::sync::Mutex::const_new(());

async fn service() -> MimirService {
    MimirService::connect(&Config {
        database: isolation::fixture().database_config(),
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
        retirement: None,
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
        learning_items: vec![],
        source_records: vec![],
    }
}

/// Candidate-publication checks exercise required preparation through the real
/// owned worker protocol. The indexed passage and vector are explicit fixture
/// data, not a production flag that bypasses grounding.
struct GroundedReviewService {
    service: Option<MimirService>,
    directory: std::path::PathBuf,
}
impl std::ops::Deref for GroundedReviewService {
    type Target = MimirService;
    fn deref(&self) -> &Self::Target {
        self.service.as_ref().unwrap()
    }
}
impl Drop for GroundedReviewService {
    fn drop(&mut self) {
        drop(self.service.take());
        std::fs::remove_dir_all(&self.directory).expect("remove this test's worker fixture");
    }
}

async fn grounded_service(project: &str) -> GroundedReviewService {
    use mimir_core::config::{EmbeddingBackend, EmbeddingsConfig};
    use std::os::unix::fs::PermissionsExt;
    let fixture = isolation::fixture();
    let database = fixture.database_config();
    let client = db::connect(&database).await.unwrap();
    let id: Uuid = client
        .query_one("SELECT gen_random_uuid()", &[])
        .await
        .unwrap()
        .get(0);
    let directory = fixture.root.join(format!("review-worker-{id}"));
    std::fs::create_dir(&directory).unwrap();
    std::fs::set_permissions(&directory, std::fs::Permissions::from_mode(0o700)).unwrap();
    let program = directory.join("worker.py");
    std::fs::write(&program, "#!/usr/bin/env python3\nimport json,sys\nfor line in sys.stdin:\n request=json.loads(line)\n print(json.dumps({'status':'started','version':1}),flush=True)\n vector=[0.0]*768\n vector[100]=1.0\n print(json.dumps({'status':'complete','vectors':[vector for text in request['texts']]}),flush=True)\n").unwrap();
    std::fs::set_permissions(&program, std::fs::Permissions::from_mode(0o700)).unwrap();
    let service = MimirService::connect_with_worker(
        &Config {
            database: database.clone(),
            embeddings: Some(EmbeddingsConfig {
                backend: EmbeddingBackend::Local,
                model: String::new(),
                api_key: None,
                cache_dir: Some(directory.join("cache").display().to_string()),
            }),
            llm: None,
            judge: None,
            email: None,
            retirement: None,
        },
        program,
    )
    .await
    .unwrap();
    let store = AgeStore::new(client, database.dbname).unwrap();
    let chunk = mimir_core::documents::DocumentChunk::with_id(
        id,
        format!("/review-fixture/{id}.md"),
        vec![],
        "Indexed supporting passage for this candidate-publication fixture".into(),
        None,
        Some(project.into()),
    );
    store.insert_document_chunk(&chunk).await.unwrap();
    let mut vector = vec![0.0; 768];
    vector[100] = 1.0;
    store.insert_chunk_embedding(id, &vector).await.unwrap();
    GroundedReviewService {
        service: Some(service),
        directory,
    }
}

#[tokio::test]
async fn subscribed_queue_keeps_work_arriving_before_initial_scan() {
    let svc = service().await;
    let cfg = isolation::fixture().database_config();
    let mut subscription = db::ReviewQueueSubscription::connect(&cfg).await.unwrap();

    // The constructor has observed LISTEN acknowledgement. Insert at the
    // controlled boundary before the very first pending-queue scan.
    let project = format!("startup-queue-{}", Uuid::new_v4());
    let source = experience(&project);
    svc.record_experience(&source, 0).await.unwrap();
    let selected = svc
        .pending_experiences(Some(&project), std::num::NonZeroUsize::new(1))
        .await
        .unwrap();
    assert_eq!(selected.len(), 1);
    assert_eq!(selected[0].experience.id, source.id);
    // The wake must survive the scan as well, so the later idle-wait stage
    // cannot miss the change by registering its waiter after that scan.
    subscription.changed().await.unwrap();
    drop(subscription);
    svc.delete_project(&project).await.unwrap();
}

#[tokio::test]
async fn empty_review_queue_wakes_on_a_later_committed_experience() {
    use std::future::{poll_fn, Future};
    let svc = service().await;
    let cfg = isolation::fixture().database_config();
    let mut subscription = db::ReviewQueueSubscription::connect(&cfg).await.unwrap();
    let project = format!("idle-queue-{}", Uuid::new_v4());
    assert!(svc
        .pending_experiences(Some(&project), std::num::NonZeroUsize::new(1))
        .await
        .unwrap()
        .is_empty());
    let wake = subscription.changed();
    tokio::pin!(wake);
    // Polling once establishes an actual waiting listener before insertion.
    // No elapsed-time guess is needed to establish that an empty queue waits.
    assert!(poll_fn(|cx| std::task::Poll::Ready(wake.as_mut().poll(cx).is_pending())).await);
    let source = experience(&project);
    svc.record_experience(&source, 0).await.unwrap();
    wake.await.unwrap();
    let selected = svc
        .pending_experiences(Some(&project), std::num::NonZeroUsize::new(1))
        .await
        .unwrap();
    assert_eq!(selected.len(), 1);
    assert_eq!(selected[0].experience.id, source.id);
    svc.delete_project(&project).await.unwrap();
}

#[tokio::test]
async fn reconnected_listener_finds_work_without_a_saved_notification() {
    use std::future::{poll_fn, Future};
    let svc = service().await;
    let cfg = isolation::fixture().database_config();
    let project = format!("reconnected-queue-{}", Uuid::new_v4());
    let reviewed = experience(&project);
    svc.record_experience(&reviewed, 0).await.unwrap();
    svc.review_experience(&review(&reviewed), 0).await.unwrap();
    let subscription = db::ReviewQueueSubscription::connect(&cfg).await.unwrap();
    assert!(svc
        .pending_experiences(Some(&project), std::num::NonZeroUsize::new(1))
        .await
        .unwrap()
        .is_empty());
    drop(subscription);

    // No listener owns this commit's hint. A reconnect must scan rather than
    // wait for an old notification that PostgreSQL does not retain.
    let source = experience(&project);
    svc.record_experience(&source, 0).await.unwrap();
    let mut reconnected = db::ReviewQueueSubscription::connect(&cfg).await.unwrap();
    let selected = svc
        .pending_experiences(Some(&project), std::num::NonZeroUsize::new(1))
        .await
        .unwrap();
    assert_eq!(selected.len(), 1);
    assert_eq!(selected[0].experience.id, source.id);
    let wake = reconnected.changed();
    tokio::pin!(wake);
    assert!(poll_fn(|cx| std::task::Poll::Ready(wake.as_mut().poll(cx).is_pending())).await);
    svc.delete_project(&project).await.unwrap();
}

#[tokio::test]
async fn pending_queue_notifications_follow_commit_and_contain_no_source() {
    use std::future::poll_fn;
    use tokio_postgres::{AsyncMessage, Notification};

    async fn signals_before_barrier(
        listener: &tokio_postgres::Client,
        received: &mut tokio::sync::mpsc::UnboundedReceiver<Notification>,
    ) -> usize {
        // A committed notification after the tested operation provides an
        // observable boundary. No elapsed-time guess is needed to test absence.
        listener
            .query_one(
                "SELECT pg_notify($1, 'test-barrier')",
                &[&db::REVIEW_QUEUE_CHANNEL],
            )
            .await
            .unwrap();
        let mut signals = 0;
        loop {
            let notification = received.recv().await.expect("notification reader stopped");
            assert_eq!(notification.channel(), db::REVIEW_QUEUE_CHANNEL);
            if notification.payload() == "test-barrier" {
                return signals;
            }
            assert!(
                notification.payload().is_empty(),
                "source data leaked in wake"
            );
            signals += 1;
        }
    }

    let _service = service().await; // Apply the actual embedded migrations.
    let fixture = isolation::fixture();
    let cfg = fixture.database_config();
    let mut writer = db::connect(&cfg).await.unwrap();
    let password_file = std::fs::read_to_string(cfg.pgpassfile.as_ref().unwrap()).unwrap();
    // The guarded fixture writes one generated hexadecimal password; no live
    // credential resolution, installed configuration, or external account.
    let password = password_file.trim_end().rsplit(':').next().unwrap();
    let mut pg = tokio_postgres::Config::new();
    pg.host(&cfg.host)
        .port(cfg.port)
        .user(&cfg.user)
        .dbname(&cfg.dbname)
        .password(password);
    let (listener, mut connection) = pg.connect(tokio_postgres::NoTls).await.unwrap();
    let (sent, mut received) = tokio::sync::mpsc::unbounded_channel();
    let reader = tokio::spawn(async move {
        while let Some(message) = poll_fn(|cx| connection.poll_message(cx)).await {
            if let AsyncMessage::Notification(notification) = message.unwrap() {
                sent.send(notification).unwrap();
            }
        }
    });
    listener
        .batch_execute(&format!("LISTEN {}", db::REVIEW_QUEUE_CHANNEL))
        .await
        .unwrap();
    let project = format!("private-queue-source-{}", Uuid::new_v4());

    let tx = writer.transaction().await.unwrap();
    let discarded: Uuid = tx
        .query_one(
            "INSERT INTO mimir_experiences(id,project,revision) VALUES(gen_random_uuid(),$1,1) RETURNING id",
            &[&project],
        )
        .await
        .unwrap()
        .get(0);
    assert_eq!(signals_before_barrier(&listener, &mut received).await, 0);
    tx.rollback().await.unwrap();
    assert_eq!(signals_before_barrier(&listener, &mut received).await, 0);
    assert!(!writer
        .query_one(
            "SELECT EXISTS(SELECT 1 FROM mimir_experiences WHERE id=$1)",
            &[&discarded]
        )
        .await
        .unwrap()
        .get::<_, bool>(0));

    let tx = writer.transaction().await.unwrap();
    let id: Uuid = tx
        .query_one(
            "INSERT INTO mimir_experiences(id,project,revision) VALUES(gen_random_uuid(),$1,1) RETURNING id",
            &[&project],
        )
        .await
        .unwrap()
        .get(0);
    assert_eq!(signals_before_barrier(&listener, &mut received).await, 0);
    tx.commit().await.unwrap();
    assert_eq!(signals_before_barrier(&listener, &mut received).await, 1);
    assert!(writer
        .query_one("SELECT EXISTS(SELECT 1 FROM mimir_experiences WHERE id=$1 AND reviewed_revision<revision)", &[&id])
        .await.unwrap().get::<_, bool>(0));

    for (statement, expected) in [
        ("UPDATE mimir_experiences SET revision=2 WHERE id=$1", 1),
        (
            "UPDATE mimir_experiences SET revision=revision WHERE id=$1",
            0,
        ),
        (
            "UPDATE mimir_experiences SET updated_at=clock_timestamp() WHERE id=$1",
            0,
        ),
        (
            "UPDATE mimir_experiences SET review_revision=1 WHERE id=$1",
            0,
        ),
        (
            "UPDATE mimir_experiences SET reviewed_revision=2 WHERE id=$1",
            0,
        ),
        (
            "UPDATE mimir_experiences SET reviewed_revision=1 WHERE id=$1",
            1,
        ),
    ] {
        writer.execute(statement, &[&id]).await.unwrap();
        assert_eq!(
            signals_before_barrier(&listener, &mut received).await,
            expected,
            "{statement}"
        );
    }
    writer
        .execute(
            "UPDATE mimir_experiences SET project=project || '-changed' WHERE id=$1",
            &[&id],
        )
        .await
        .unwrap();
    assert_eq!(signals_before_barrier(&listener, &mut received).await, 1);

    // Notifications are hints, not a count of net changes. A transaction can
    // stage a real source change and restore it before committing.
    let tx = writer.transaction().await.unwrap();
    tx.execute(
        "UPDATE mimir_experiences SET revision=3 WHERE id=$1",
        &[&id],
    )
    .await
    .unwrap();
    tx.execute(
        "UPDATE mimir_experiences SET revision=2 WHERE id=$1",
        &[&id],
    )
    .await
    .unwrap();
    tx.commit().await.unwrap();
    assert_eq!(signals_before_barrier(&listener, &mut received).await, 1);

    let tx = writer.transaction().await.unwrap();
    tx.execute(
        "UPDATE mimir_experiences SET revision=3 WHERE id=$1",
        &[&id],
    )
    .await
    .unwrap();
    tx.rollback().await.unwrap();
    assert_eq!(signals_before_barrier(&listener, &mut received).await, 0);

    writer
        .execute("DELETE FROM mimir_experiences WHERE id=$1", &[&id])
        .await
        .unwrap();
    let completed: Uuid = writer.query_one("INSERT INTO mimir_experiences(id,project,revision,reviewed_revision) VALUES(gen_random_uuid(),$1,1,1) RETURNING id", &[&project]).await.unwrap().get(0);
    assert_eq!(signals_before_barrier(&listener, &mut received).await, 0);
    writer
        .execute("DELETE FROM mimir_experiences WHERE id=$1", &[&completed])
        .await
        .unwrap();
    drop(listener);
    reader.await.unwrap();
}

#[tokio::test]
async fn sql_pages_cover_large_filtered_corpus_without_a_total_cutoff() {
    let _page_guard = PAGE_TEST_LOCK.lock().await;
    let svc = service().await;
    let project = format!("paging-{}", Uuid::new_v4());
    let mut expected = std::collections::HashSet::new();
    for n in 0..207 {
        let b = isolation::seed_belief_in_project(
            &format!("{n}: {}", "long evidence ".repeat(300)),
            0.5,
            0.1,
            &project,
            MemoryType::Fact,
        )
        .await
        .unwrap();
        expected.insert(b.id.to_string());
    }
    let mut seen = std::collections::HashSet::new();
    let mut offset = 0;
    loop {
        let page = svc
            .list_beliefs_page(Some(&project), Some(MemoryType::Fact), 10, offset)
            .await
            .unwrap();
        let beliefs = page["beliefs"].as_array().unwrap();
        assert!(beliefs.len() <= 10);
        for b in beliefs {
            assert!(
                seen.insert(b["id"].as_str().unwrap().to_owned()),
                "duplicate page entry"
            );
        }
        match page["next_offset"].as_u64() {
            Some(next) => {
                assert!(next as usize > offset);
                offset = next as usize;
            }
            None => break,
        }
    }
    assert!(expected.is_subset(&seen)); // Global beliefs may also be visible.
    let larger = svc
        .list_beliefs_page(Some(&project), None, 11, 0)
        .await
        .unwrap();
    assert_eq!(larger["beliefs"].as_array().unwrap().len(), 11);
    let empty = svc
        .list_beliefs_page(Some(&project), None, 10, 100_000)
        .await
        .unwrap();
    assert!(empty["beliefs"].as_array().unwrap().is_empty());
    assert!(empty["next_offset"].is_null());
    svc.delete_project(&project).await.unwrap();
}

#[tokio::test]
async fn sql_pager_handles_single_last_and_global_project_visibility() {
    let _page_guard = PAGE_TEST_LOCK.lock().await;
    let svc = service().await;
    let project = format!("paging-{}", Uuid::new_v4());
    let foreign = format!("paging-{}", Uuid::new_v4());
    let global = isolation::seed_belief("pager global marker", 0.5, 0.0, MemoryType::Fact)
        .await
        .unwrap();
    let a = isolation::seed_belief_in_project(
        "pager local first",
        0.5,
        0.0,
        &project,
        MemoryType::Fact,
    )
    .await
    .unwrap();
    let b = isolation::seed_belief_in_project(
        "pager local second",
        0.5,
        0.0,
        &project,
        MemoryType::Fact,
    )
    .await
    .unwrap();
    let outside =
        isolation::seed_belief_in_project("pager foreign", 0.5, 0.0, &foreign, MemoryType::Fact)
            .await
            .unwrap();

    let mut offset = 0;
    let mut seen = Vec::new();
    loop {
        let page = svc
            .list_beliefs_page(Some(&project), Some(MemoryType::Fact), 1, offset)
            .await
            .unwrap();
        assert_eq!(page["offset"], offset);
        let beliefs = page["beliefs"].as_array().unwrap();
        assert_eq!(beliefs.len(), 1);
        seen.push(beliefs[0]["id"].as_str().unwrap().to_owned());
        match page["next_offset"].as_u64() {
            Some(next) => offset = next as usize,
            None => break,
        }
    }
    for wanted in [global.id, a.id, b.id] {
        assert!(seen.contains(&wanted.to_string()));
    }
    assert!(!seen.contains(&outside.id.to_string()));
    let full = svc
        .list_beliefs_page(Some(&project), Some(MemoryType::Fact), 10, 0)
        .await
        .unwrap();
    assert_eq!(full["beliefs"].as_array().unwrap().len(), 3);
    let last = svc
        .list_beliefs_page(Some(&project), Some(MemoryType::Fact), 10, 2)
        .await
        .unwrap();
    assert_eq!(last["beliefs"].as_array().unwrap().len(), 1);
    assert!(last["next_offset"].is_null());
    assert_eq!(
        svc.list_beliefs_page(Some(&project), Some(MemoryType::Fact), 10, 0)
            .await
            .unwrap(),
        full
    );
    assert!(svc
        .list_beliefs_page(Some(&project), None, 0, 0)
        .await
        .is_err());
    let larger = svc
        .list_beliefs_page(Some(&project), None, 11, 0)
        .await
        .unwrap();
    assert_eq!(
        larger["beliefs"].as_array().unwrap().len(),
        (larger["total"].as_u64().unwrap() as usize).min(11)
    );
    let beyond = svc
        .list_beliefs_page(Some(&project), None, 1, usize::MAX)
        .await
        .unwrap();
    assert!(beyond["beliefs"].as_array().unwrap().is_empty());
    assert!(beyond["next_offset"].is_null());
    svc.delete_project(&project).await.unwrap();
    svc.delete_project(&foreign).await.unwrap();
    svc.delete_belief(global.id).await.unwrap();
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
        candidates: vec![],
        candidate_feedback: vec![],
        candidate_links: vec![],
        assessments: vec![],
        extracted_items: vec![],
        source_coverage: vec![],
    }
}

#[tokio::test]
async fn typed_assessments_replace_retract_and_preserve_legacy_probability() {
    use mimir_core::assessment::{Assessment, Axis, ItemKind, LearningItem, Prediction};
    let project = format!("assessment-{}", Uuid::new_v4());
    let svc = grounded_service(&project).await;
    let mut e = experience(&project);
    e.learning_items.push(LearningItem {
        id: None,
        key: Some("duration-estimate".into()),
        kind: ItemKind::Estimate,
        source_ref: "task/event/1#span0".into(),
        actor: "worker".into(),
        statement: "complete within 30 minutes".into(),
        conditions: "fixed scope".into(),
        predictions: vec![Prediction {
            quantity: "duration".into(),
            value: 30.,
            unit: "minutes".into(),
            probability: Some(0.8),
            lower: None,
            upper: None,
            horizon: "this task".into(),
            recorded_at: "2026-10-28T00:00:00Z".into(),
            inferred: false,
        }],
    });
    let recorded = svc.record_experience(&e, 0).await.unwrap();
    let item_id = recorded.item_ids["duration-estimate"];
    e = recorded.experience;
    let mut duplicate = e.clone();
    duplicate.id = Uuid::new_v4();
    assert!(svc.record_experience(&duplicate, 0).await.is_err());
    assert!(svc.get_experience(duplicate.id).await.unwrap().is_none());
    let mut moved = e.clone();
    moved.learning_items[0].actor = "another actor".into();
    assert!(svc.record_experience(&moved, 1).await.is_err());
    let mut r = review(&e);
    r.candidates.push(Candidate::Belief {
        key: "lesson".into(),
        content: "30 minutes suffices under fixed scope".into(),
        memory_type: MemoryType::Experiential,
    });
    r.assessments.push(Assessment {
        target: BeliefTarget::Candidate {
            candidate_key: "lesson".into(),
        },
        scope: "fixed-scope-v1".into(),
        rubric: "benefit-v1".into(),
        correctness: Axis {
            value: Some(1.),
            weight: 1.,
        },
        usefulness: Axis {
            value: Some(1.),
            weight: 1.,
        },
        evidence_indices: vec![0],
        item_ids: vec![item_id],
        item_keys: vec![],
        rationale: "observed completion with clear net benefit".into(),
    });
    let first = svc.review_experience(&r, 0).await.unwrap();
    let id = first.candidate_ids["lesson"];
    let score = svc
        .lesson_assessment(&project, id, "fixed-scope-v1", "benefit-v1")
        .await
        .unwrap();
    assert!((score["scores"]["correctness"].as_f64().unwrap() - 2. / 3.).abs() < 1e-12);
    assert_eq!(score["scores"]["usefulness"], 0.5);
    let retrieved = svc
        .query_learning_context(
            "30 minutes fixed scope",
            &project,
            std::num::NonZeroUsize::new(5),
        )
        .await
        .unwrap();
    assert!(retrieved
        .assessments
        .iter()
        .any(|a| a["belief_id"] == id.to_string() && a["scores"]["usefulness"] == 0.5));
    assert!(!retrieved.assessments_truncated);
    assert_eq!(
        svc.review_experience(&r, 0).await.unwrap().review_revision,
        1
    );
    assert_eq!(
        svc.lesson_assessment(&project, id, "fixed-scope-v1", "benefit-v1")
            .await
            .unwrap(),
        score
    );
    assert_eq!(
        svc.get_belief(id)
            .await
            .unwrap()
            .unwrap()
            .probability
            .value(),
        2.0 / 3.0 // the indexed document remains independent of the assessment
    );
    assert!(svc
        .lesson_assessment("foreign", id, "fixed-scope-v1", "benefit-v1")
        .await
        .is_err());
    // A later judgment corrects the SAME incident, rather than adding a failure.
    r.assessments[0].correctness.value = Some(0.);
    r.assessments[0].usefulness.value = Some(-0.5);
    assert!(svc.review_experience(&r, 0).await.is_err());
    svc.review_experience(&r, 1).await.unwrap();
    let corrected = svc
        .lesson_assessment(&project, id, "fixed-scope-v1", "benefit-v1")
        .await
        .unwrap();
    assert!((corrected["scores"]["correctness"].as_f64().unwrap() - 1. / 3.).abs() < 1e-12);
    assert_eq!(corrected["scores"]["usefulness"], -0.25);
    assert_eq!(corrected["scores"]["incidents"], 1);
    let page = svc
        .lesson_assessment_history(
            &project,
            id,
            "fixed-scope-v1",
            "benefit-v1",
            0,
            std::num::NonZeroUsize::new(1),
        )
        .await
        .unwrap();
    assert_eq!(page["entries"][0]["active"], false);
    assert_eq!(page["next_offset"], 1);
    let page = svc
        .lesson_assessment_history(
            &project,
            id,
            "fixed-scope-v1",
            "benefit-v1",
            1,
            std::num::NonZeroUsize::new(1),
        )
        .await
        .unwrap();
    assert_eq!(page["entries"][0]["active"], true);
    // Reconnect proves persistence; correcting source invalidates its old review.
    let reopened = service().await;
    assert_eq!(
        reopened
            .lesson_assessment(&project, id, "fixed-scope-v1", "benefit-v1")
            .await
            .unwrap(),
        corrected
    );
    e.evidence[0] = "original measurement used wrong run; outcome unresolved".into();
    e.outcome = Outcome::Unknown;
    reopened.record_experience(&e, 1).await.unwrap();
    assert!(reopened.review_experience(&r, 2).await.is_err());
    let prior = reopened
        .lesson_assessment(&project, id, "fixed-scope-v1", "benefit-v1")
        .await
        .unwrap();
    assert_eq!(prior["scores"]["correctness"], 0.5);
    assert_eq!(prior["scores"]["usefulness"], 0.0);
    assert_eq!(prior["scores"]["incidents"], 0);
    r.experience_revision = 2;
    r.assessments[0].correctness = Axis {
        value: None,
        weight: 0.,
    };
    r.assessments[0].usefulness = Axis {
        value: None,
        weight: 0.,
    };
    reopened.review_experience(&r, 2).await.unwrap();
    let unresolved = reopened
        .lesson_assessment(&project, id, "fixed-scope-v1", "benefit-v1")
        .await
        .unwrap();
    assert_eq!(unresolved["scores"]["correctness"], 0.5);
    assert_eq!(unresolved["scores"]["usefulness"], 0.0);
    assert_eq!(unresolved["scores"]["unresolved_correctness"], 1);
    let mut bad = r.clone();
    bad.assessments[0].evidence_indices = vec![99];
    assert!(reopened.review_experience(&bad, 3).await.is_err());
    bad = r.clone();
    bad.assessments.push(bad.assessments[0].clone());
    assert!(reopened.review_experience(&bad, 3).await.is_err());
    bad = r.clone();
    bad.feedback.push(Feedback {
        belief_id: id,
        verdict: Verdict::Support,
        weight: 1.,
    });
    assert!(reopened.review_experience(&bad, 3).await.is_err());
    // Failed writes did not advance the review pointer or change assessment.
    assert_eq!(
        reopened
            .get_experience(e.id)
            .await
            .unwrap()
            .unwrap()
            .review_revision,
        3
    );
    assert_eq!(
        reopened
            .lesson_assessment(&project, id, "fixed-scope-v1", "benefit-v1")
            .await
            .unwrap(),
        unresolved
    );
    // Legacy JSON keeps exactly the old shape when typed fields are absent.
    let legacy = experience(&project);
    assert!(serde_json::to_value(&legacy)
        .unwrap()
        .get("learning_items")
        .is_none());
    assert!(serde_json::to_value(review(&legacy))
        .unwrap()
        .get("assessments")
        .is_none());
    reopened.delete_project(&project).await.unwrap();
}

/// Fixed Step-11 scenarios exercise the real ledger, candidate ownership, and
/// later retrieval. The deterministic chooser checks whether a retrieved lesson
/// applies; it is not a claim about an LLM's later behavior.
#[tokio::test]
async fn offline_learning_scenario_matrix() {
    let project = format!("learning-scenarios-{}", Uuid::new_v4());
    let svc = grounded_service(&project).await;
    let foreign = format!("learning-scenarios-{}", Uuid::new_v4());
    let foreign_belief = isolation::seed_belief_in_project(
        "foreign keyboard claim",
        0.5,
        0.0,
        &foreign,
        MemoryType::Fact,
    )
    .await
    .unwrap();
    let lesson = "For a stale keyboard indicator, restart the layout process after checking its loaded configuration";
    let capture =
        |tag: &str, outcome: Outcome, source: ObservationSource, evidence: &str| Experience {
            id: Uuid::new_v4(),
            project: project.clone(),
            context: format!("{tag}: stale keyboard indicator"),
            action: "restart layout process".into(),
            outcome,
            source,
            evidence: vec![evidence.into()],
            belief_ids: vec![],
            pattern_id: None,
            learning_items: vec![],
            source_records: vec![],
        };
    let assess = |e: &Experience, verdict: Option<Verdict>| {
        let mut r = review(e);
        r.candidates.push(Candidate::Belief {
            key: "layout-lesson".into(),
            content: lesson.into(),
            memory_type: MemoryType::Experiential,
        });
        if let Some(verdict) = verdict {
            r.candidate_feedback.push(CandidateFeedback {
                target: BeliefTarget::Candidate {
                    candidate_key: "layout-lesson".into(),
                },
                verdict,
                weight: 0.75,
            });
        }
        r
    };

    // One observed success creates one review-owned contribution. The same
    // review and source retry cannot manufacture another observation.
    let success = capture(
        "success",
        Outcome::Success,
        ObservationSource::ToolResult,
        "Observed process ID changed and the indicator loaded the new layout",
    );
    assert_eq!(
        svc.record_experience(&success, 0).await.unwrap().revision,
        1
    );
    let success_review = assess(&success, Some(Verdict::Support));
    let applied = svc.review_experience(&success_review, 0).await.unwrap();
    let success_id = applied.candidate_ids["layout-lesson"];
    let supported = svc.get_belief(success_id).await.unwrap().unwrap();
    assert!(supported.alpha > supported.beta);
    assert_eq!(
        svc.record_experience(&success, 0).await.unwrap().revision,
        1
    );
    assert_eq!(
        svc.review_experience(&success_review, 0)
            .await
            .unwrap()
            .candidate_ids["layout-lesson"],
        success_id
    );
    assert_eq!(
        svc.get_belief(success_id).await.unwrap().unwrap().alpha,
        supported.alpha
    );
    assert_eq!(
        svc.experience_history(success.id).await.unwrap()["reviews"]
            .as_array()
            .unwrap()
            .len(),
        1
    );
    // A separate connection stands in for the later session; no in-process
    // review state is handed to the chooser.
    let later_session = service().await;
    let retrieved = later_session
        .query_learning_context(
            "stale keyboard indicator",
            &project,
            std::num::NonZeroUsize::new(20),
        )
        .await
        .unwrap();
    let retrieved_lesson = retrieved.beliefs.iter().any(|b| b.id == success_id);
    assert!(
        retrieved_lesson,
        "fresh retrieval missed the learned lesson"
    );
    let choose = |situation: &str, found: bool| {
        if situation.contains("keyboard indicator") && found {
            "restart layout process"
        } else {
            "investigate current situation"
        }
    };
    assert_eq!(
        choose("stale keyboard indicator", retrieved_lesson),
        "restart layout process"
    );
    let unrelated = later_session
        .query_learning_context(
            "disk quota exceeded",
            &project,
            std::num::NonZeroUsize::new(20),
        )
        .await
        .unwrap();
    let unrelated_retrieved_lesson = unrelated.beliefs.iter().any(|b| b.id == success_id);
    assert_eq!(
        choose("disk quota exceeded", unrelated_retrieved_lesson),
        "investigate current situation"
    );

    // Failure, unknown outcome, and a confounded apparent success are different
    // evidence classes. The last two must not become positive causal feedback.
    for (tag, outcome, source, evidence, verdict) in [
        (
            "failure",
            Outcome::Failure,
            ObservationSource::ToolResult,
            "Observed restart did not change the indicator",
            Some(Verdict::Defeat),
        ),
        (
            "unknown",
            Outcome::Unknown,
            ObservationSource::AgentReport,
            "Agent guessed the restart worked; no result was observed",
            None,
        ),
        (
            "confounded",
            Outcome::Success,
            ObservationSource::UserFeedback,
            "User saw an update after restart and simultaneous RDP reconnect; cause unresolved",
            None,
        ),
    ] {
        let e = capture(tag, outcome, source, evidence);
        svc.record_experience(&e, 0).await.unwrap();
        let r = assess(&e, verdict);
        let applied = svc.review_experience(&r, 0).await.unwrap();
        let id = applied.candidate_ids["layout-lesson"];
        let belief = svc.get_belief(id).await.unwrap().unwrap();
        match verdict {
            Some(Verdict::Defeat) => assert!(belief.beta > belief.alpha),
            None => assert_eq!((belief.alpha, belief.beta), (2.0, 1.0)),
            _ => unreachable!(),
        }
        assert_eq!(
            svc.get_experience(e.id)
                .await
                .unwrap()
                .unwrap()
                .experience
                .source,
            source
        );
        assert!(
            svc.query_intervention(id, 1.0).await.unwrap().is_empty(),
            "uncertain or confounded observation created a causal edge"
        );
    }

    // A correction keeps incident identity, retracts the old contribution,
    // rejects the old revision, and permits one replacement interpretation.
    let mut corrected = capture(
        "correction",
        Outcome::Success,
        ObservationSource::UserFeedback,
        "User initially reported the indicator changed",
    );
    svc.record_experience(&corrected, 0).await.unwrap();
    let old = assess(&corrected, Some(Verdict::Support));
    let first = svc.review_experience(&old, 0).await.unwrap();
    let id = first.candidate_ids["layout-lesson"];
    corrected.outcome = Outcome::Failure;
    corrected.evidence = vec!["User correction: indicator was still stale".into()];
    assert_eq!(
        svc.record_experience(&corrected, 1).await.unwrap().revision,
        2
    );
    assert_eq!(svc.get_belief(id).await.unwrap().unwrap().alpha, 2.0);
    assert!(svc.review_experience(&old, 1).await.is_err());
    let mut replacement = review(&corrected);
    replacement.experience_revision = 2;
    replacement.feedback.push(Feedback {
        belief_id: id,
        verdict: Verdict::Defeat,
        weight: 0.75,
    });
    svc.review_experience(&replacement, 1).await.unwrap();
    assert!(svc.get_belief(id).await.unwrap().unwrap().beta > 1.0);
    assert_eq!(
        svc.experience_history(corrected.id).await.unwrap()["reviews"]
            .as_array()
            .unwrap()
            .len(),
        2
    );

    // Cross-project feedback cannot acknowledge the queued source or mutate
    // the foreign belief, even when supplied with a valid source revision.
    let cross = capture(
        "cross-scope",
        Outcome::Success,
        ObservationSource::ToolResult,
        "Observed local result",
    );
    svc.record_experience(&cross, 0).await.unwrap();
    let mut bad = review(&cross);
    bad.feedback.push(Feedback {
        belief_id: foreign_belief.id,
        verdict: Verdict::Support,
        weight: 1.0,
    });
    assert!(svc.review_experience(&bad, 0).await.is_err());
    let state = svc.get_experience(cross.id).await.unwrap().unwrap();
    assert_eq!((state.review_revision, state.reviewed_revision), (0, 0));
    assert_eq!(
        svc.get_belief(foreign_belief.id)
            .await
            .unwrap()
            .unwrap()
            .alpha,
        foreign_belief.alpha
    );
    svc.delete_project(&project).await.unwrap();
    svc.delete_project(&foreign).await.unwrap();
}

/// Characterization of the known provenance gap: an ordinary foreground
/// belief has no incident owner. The server cannot infer from content alone
/// that the same report produced both its prior and this review's feedback.
/// Keep this visible as a release blocker for automated capture, not as a
/// passing claim of semantic deduplication.
#[tokio::test]
async fn standalone_foreground_belief_can_still_double_count_one_incident() {
    let svc = service().await;
    let project = format!("learning-overlap-{}", Uuid::new_v4());
    let belief = isolation::seed_belief_in_project(
        "Restarting the stale keyboard process fixes the indicator",
        0.7,
        0.2,
        &project,
        MemoryType::Experiential,
    )
    .await
    .unwrap();
    let mut e = experience(&project);
    e.belief_ids.push(belief.id);
    svc.record_experience(&e, 0).await.unwrap();
    let before = svc.get_belief(belief.id).await.unwrap().unwrap();
    let mut r = review(&e);
    r.feedback.push(Feedback {
        belief_id: belief.id,
        verdict: Verdict::Support,
        weight: 0.75,
    });
    svc.review_experience(&r, 0).await.unwrap();
    let after = svc.get_belief(belief.id).await.unwrap().unwrap();
    assert!(
        before.alpha > 1.0,
        "standalone prior already has evidence mass"
    );
    assert!(
        after.alpha > before.alpha,
        "review added the same report again"
    );
    assert!(
        svc.explain_belief(belief.id, 0, std::num::NonZeroUsize::new(10))
            .await
            .unwrap()["candidate_provenance"]
            .is_null(),
        "standalone belief unexpectedly gained incident provenance"
    );
    svc.delete_project(&project).await.unwrap();
}
#[tokio::test]
async fn learning_cycle_retry_revision_causal_projection_and_retraction() {
    let svc = service().await;
    let project = format!("learning-{}", Uuid::new_v4());
    let a = isolation::seed_belief_in_project(
        "restart stale process",
        0.8,
        0.0,
        &project,
        MemoryType::Experiential,
    )
    .await
    .unwrap();
    let b = isolation::seed_belief_in_project(
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
        .pending_experiences(Some(&project), std::num::NonZeroUsize::new(10))
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
        svc.pending_experiences(Some(&project), std::num::NonZeroUsize::new(10))
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
async fn atomic_candidates_retry_retraction_and_observed_pattern_use() {
    let project = format!("learning-{}", Uuid::new_v4());
    let svc = grounded_service(&project).await;
    let e = experience(&project);
    svc.record_experience(&e, 0).await.unwrap();
    let mut r = review(&e);
    r.candidates = vec![
        Candidate::Belief {
            key: "lesson".into(),
            content: "restart stale keyboard process".into(),
            memory_type: MemoryType::Experiential,
        },
        Candidate::Pattern {
            key: "procedure".into(),
            situation: "keyboard session lifecycle".into(),
            approach: "restart stale process".into(),
        },
    ];
    r.candidate_feedback.push(CandidateFeedback {
        target: BeliefTarget::Candidate {
            candidate_key: "lesson".into(),
        },
        verdict: Verdict::Support,
        weight: 0.75,
    });
    let first = svc.review_experience(&r, 0).await.unwrap();
    let belief_id = first.candidate_ids["lesson"];
    let pattern_id = first.candidate_ids["procedure"];
    assert!((svc.get_belief(belief_id).await.unwrap().unwrap().alpha - 5.0).abs() < 1e-9);
    assert_eq!(
        svc.review_experience(&r, 0).await.unwrap().candidate_ids,
        first.candidate_ids
    );
    assert_eq!(
        svc.review_experience(&r, 1).await.unwrap().review_revision,
        1
    );
    let candidate = svc
        .explain_belief(belief_id, 0, std::num::NonZeroUsize::new(10))
        .await
        .unwrap();
    assert_eq!(candidate["candidate_provenance"]["active"], true);
    let before_use = svc
        .query_learning_context(
            "keyboard session lifecycle",
            &project,
            std::num::NonZeroUsize::new(10),
        )
        .await
        .unwrap();
    let result = before_use
        .patterns
        .iter()
        .find(|p| p.pattern.id == pattern_id)
        .unwrap();
    assert_eq!((result.successes, result.failures), (0, 0));
    assert_eq!(result.observed_success_probability, 0.5);
    assert!(result.candidate_provenance.as_ref().unwrap().active);

    let mut altered = r.clone();
    altered.candidates[0] = Candidate::Belief {
        key: "lesson".into(),
        content: "different claim".into(),
        memory_type: MemoryType::Experiential,
    };
    assert!(svc.review_experience(&altered, 1).await.is_err());
    assert_eq!(
        svc.get_belief(belief_id).await.unwrap().unwrap().content,
        "restart stale keyboard process"
    );

    let mut use_record = experience(&project);
    use_record.pattern_id = Some(pattern_id);
    svc.record_experience(&use_record, 0).await.unwrap();
    let observed = svc
        .query_learning_context(
            "keyboard session lifecycle",
            &project,
            std::num::NonZeroUsize::new(10),
        )
        .await
        .unwrap();
    let result = observed
        .patterns
        .iter()
        .find(|p| p.pattern.id == pattern_id)
        .unwrap();
    assert_eq!((result.successes, result.failures), (1, 0));

    let mut retract = review(&e);
    retract.rationale = "retract interpretation, retain original observation".into();
    svc.review_experience(&retract, 1).await.unwrap();
    let after = svc.get_belief(belief_id).await.unwrap().unwrap();
    // Retracting the incident leaves its independently indexed support intact.
    assert!((after.alpha - 2.0).abs() < 1e-9);
    assert_eq!(
        svc.explain_belief(belief_id, 0, std::num::NonZeroUsize::new(10))
            .await
            .unwrap()["candidate_provenance"]["active"],
        false
    );
    let after = svc
        .query_learning_context(
            "keyboard session lifecycle",
            &project,
            std::num::NonZeroUsize::new(10),
        )
        .await
        .unwrap();
    let result = after
        .patterns
        .iter()
        .find(|p| p.pattern.id == pattern_id)
        .unwrap();
    assert!(!result.candidate_provenance.as_ref().unwrap().active);
    assert_eq!((result.successes, result.failures), (1, 0));
    assert!(svc.delete_pattern(pattern_id).await.unwrap());
    assert!(
        svc.review_experience(&r, 2).await.is_err(),
        "deleted pattern identity must not be recreated by a later review"
    );
    svc.delete_project(&project).await.unwrap();
}

#[tokio::test]
async fn complete_candidate_keys_survive_publication_and_exact_retry() {
    let svc = service().await;
    let project = format!("complete-candidate-key-{}", Uuid::new_v4());
    let e = experience(&project);
    svc.record_experience(&e, 0).await.unwrap();
    let key = "complete-procedure-".repeat(20);
    let mut r = review(&e);
    r.candidates = vec![Candidate::Pattern {
        key: key.clone(),
        situation: "preserve the full caller key".into(),
        approach: "publish once and recover the original identity".into(),
    }];
    let original = svc.review_experience(&r, 0).await.unwrap();
    assert!(original.candidate_ids.contains_key(&key));
    assert_eq!(
        svc.review_experience(&r, 0).await.unwrap().candidate_ids,
        original.candidate_ids
    );
    r.candidates = vec![Candidate::Pattern {
        key: String::new(),
        situation: "missing identity".into(),
        approach: "must still be refused".into(),
    }];
    assert!(r.validate().is_err());
    let provenance = mimir_core::learning::IndependentProvenance {
        basis: mimir_core::learning::IndependentBasis::Document,
        reference: "document-reference/".repeat(200),
    };
    provenance.validate().unwrap();
    svc.delete_project(&project).await.unwrap();
}

#[tokio::test]
async fn source_correction_deactivates_candidate_support_without_deleting_identity() {
    let project = format!("learning-{}", Uuid::new_v4());
    let svc = grounded_service(&project).await;
    let mut e = experience(&project);
    svc.record_experience(&e, 0).await.unwrap();
    let mut r = review(&e);
    r.candidates.push(Candidate::Belief {
        key: "hypothesis".into(),
        content: "candidate may help".into(),
        memory_type: MemoryType::Fact,
    });
    r.candidate_feedback.push(CandidateFeedback {
        target: BeliefTarget::Candidate {
            candidate_key: "hypothesis".into(),
        },
        verdict: Verdict::Support,
        weight: 1.0,
    });
    let reviewed = svc.review_experience(&r, 0).await.unwrap();
    let id = reviewed.candidate_ids["hypothesis"];
    assert!((svc.get_belief(id).await.unwrap().unwrap().alpha - 6.0).abs() < 1e-9);
    e.outcome = Outcome::Failure;
    e.evidence = vec!["corrected external result".into()];
    svc.record_experience(&e, 1).await.unwrap();
    assert_eq!(
        svc.get_experience(e.id)
            .await
            .unwrap()
            .unwrap()
            .reviewed_revision,
        1
    );
    assert!((svc.get_belief(id).await.unwrap().unwrap().alpha - 2.0).abs() < 1e-9);
    assert_eq!(
        svc.explain_belief(id, 0, std::num::NonZeroUsize::new(10))
            .await
            .unwrap()["candidate_provenance"]["active"],
        false
    );
    assert!(
        svc.review_experience(&r, 1).await.is_err(),
        "stale source review must fail"
    );
    assert!(svc.get_belief(id).await.unwrap().is_some());
    svc.delete_project(&project).await.unwrap();
}

#[tokio::test]
async fn rejected_candidate_review_rolls_back_node_and_acknowledgement() {
    let project = format!("learning-{}", Uuid::new_v4());
    let svc = grounded_service(&project).await;
    let e = experience(&project);
    svc.record_experience(&e, 0).await.unwrap();
    let mut r = review(&e);
    r.candidates.push(Candidate::Belief {
        key: "rolled-back".into(),
        content: "unique rollback candidate".into(),
        memory_type: MemoryType::Fact,
    });
    r.feedback.push(Feedback {
        belief_id: Uuid::new_v4(),
        verdict: Verdict::Support,
        weight: 1.0,
    });
    assert!(svc.review_experience(&r, 0).await.is_err());
    assert_eq!(
        svc.get_experience(e.id)
            .await
            .unwrap()
            .unwrap()
            .reviewed_revision,
        0
    );
    let page = svc
        .list_beliefs_page(Some(&project), None, 10, 0)
        .await
        .unwrap();
    assert!(!page["beliefs"]
        .as_array()
        .unwrap()
        .iter()
        .any(|b| b["content"] == "unique rollback candidate"));
    r.feedback.clear();
    let applied = svc.review_experience(&r, 0).await.unwrap();
    assert_eq!(applied.reviewed_revision, 1);
    assert!(svc
        .get_belief(applied.candidate_ids["rolled-back"])
        .await
        .unwrap()
        .is_some());
    assert!(svc
        .delete_belief(applied.candidate_ids["rolled-back"])
        .await
        .unwrap());
    let mut reuse = r.clone();
    reuse.rationale = "try to resurrect deleted identity".into();
    assert!(svc.review_experience(&reuse, 1).await.is_err());
    assert_eq!(
        svc.get_experience(e.id)
            .await
            .unwrap()
            .unwrap()
            .review_revision,
        1
    );
    svc.delete_project(&project).await.unwrap();
}

#[tokio::test]
async fn deleting_candidate_recomputes_linked_belief_and_keeps_tombstone() {
    let project = format!("learning-{}", Uuid::new_v4());
    let svc = grounded_service(&project).await;
    let target =
        isolation::seed_belief_in_project("downstream claim", 0.5, 0.0, &project, MemoryType::Fact)
            .await
            .unwrap();
    let e = experience(&project);
    svc.record_experience(&e, 0).await.unwrap();
    let mut r = review(&e);
    r.candidates.push(Candidate::Belief {
        key: "source".into(),
        content: "candidate source".into(),
        memory_type: MemoryType::Fact,
    });
    r.candidate_feedback.push(CandidateFeedback {
        target: BeliefTarget::Candidate {
            candidate_key: "source".into(),
        },
        verdict: Verdict::Support,
        weight: 0.5,
    });
    r.candidate_links.push(CandidateLink {
        from: BeliefTarget::Candidate {
            candidate_key: "source".into(),
        },
        to: BeliefTarget::Existing {
            belief_id: target.id,
        },
        relation: EdgeType::Supports,
        weight: 1.0,
    });
    let applied = svc.review_experience(&r, 0).await.unwrap();
    let source = applied.candidate_ids["source"];
    assert!(svc.get_belief(target.id).await.unwrap().unwrap().alpha > target.alpha0);
    assert!(svc.delete_belief(source).await.unwrap());
    assert!((svc.get_belief(target.id).await.unwrap().unwrap().alpha - target.alpha0).abs() < 1e-8);
    let history = svc.experience_history(e.id).await.unwrap();
    let replayed = svc.review_experience(&r, 0).await.unwrap();
    assert_eq!(
        serde_json::to_value(&replayed).unwrap(),
        serde_json::to_value(&applied).unwrap()
    );
    assert!(svc.get_belief(source).await.unwrap().is_none());
    assert!((svc.get_belief(target.id).await.unwrap().unwrap().alpha - target.alpha0).abs() < 1e-8);
    assert_eq!(svc.experience_history(e.id).await.unwrap(), history);
    let mut later = r.clone();
    later.rationale = "try to reuse deleted candidate".into();
    assert!(svc.review_experience(&later, 1).await.is_err());
    svc.delete_project(&project).await.unwrap();
}

#[tokio::test]
async fn project_deletion_removes_pattern_only_candidate_and_ledger() {
    let svc = service().await;
    let project = format!("learning-{}", Uuid::new_v4());
    let e = experience(&project);
    svc.record_experience(&e, 0).await.unwrap();
    let mut r = review(&e);
    r.candidates.push(Candidate::Pattern {
        key: "procedure".into(),
        situation: "pattern-only cleanup".into(),
        approach: "delete project".into(),
    });
    let applied = svc.review_experience(&r, 0).await.unwrap();
    let id = applied.candidate_ids["procedure"];
    assert!(svc.get_pattern(id).await.unwrap().is_some());
    assert_eq!(svc.delete_project(&project).await.unwrap(), 0);
    assert!(svc.get_pattern(id).await.unwrap().is_none());
    assert!(svc.get_experience(e.id).await.unwrap().is_none());
}

#[tokio::test]
async fn review_recompute_stays_in_project_and_keeps_external_incoming_support() {
    let svc = service().await;
    let own = format!("learning-{}", Uuid::new_v4());
    let foreign = format!("learning-{}", Uuid::new_v4());
    let seed = isolation::seed_belief_in_project("local seed", 0.5, 0.0, &own, MemoryType::Fact)
        .await
        .unwrap();
    let foreign_node =
        isolation::seed_belief_in_project("foreign bridge", 0.5, 0.0, &foreign, MemoryType::Fact)
            .await
            .unwrap();
    let own_tail = isolation::seed_belief_in_project("own tail", 0.5, 0.0, &own, MemoryType::Fact)
        .await
        .unwrap();
    svc.add_edge(seed.id, foreign_node.id, EdgeType::Supports, 1.0)
        .await
        .unwrap();
    svc.add_edge(foreign_node.id, own_tail.id, EdgeType::Supports, 1.0)
        .await
        .unwrap();
    svc.add_edge(foreign_node.id, seed.id, EdgeType::Supports, 0.5)
        .await
        .unwrap();
    let e = experience(&own);
    svc.record_experience(&e, 0).await.unwrap();
    let mut r = review(&e);
    r.feedback.push(Feedback {
        belief_id: seed.id,
        verdict: Verdict::Support,
        weight: 0.5,
    });
    svc.review_experience(&r, 0).await.unwrap();
    let current_seed = svc.get_belief(seed.id).await.unwrap().unwrap();
    let current_foreign = svc.get_belief(foreign_node.id).await.unwrap().unwrap();
    let current_tail = svc.get_belief(own_tail.id).await.unwrap().unwrap();
    assert!((current_seed.alpha - (seed.alpha0 + 2.0 + 0.5 * 0.5 * 4.0)).abs() < 1e-8);
    assert_eq!(
        (current_foreign.alpha, current_foreign.beta),
        (foreign_node.alpha, foreign_node.beta)
    );
    assert_eq!(
        (current_tail.alpha, current_tail.beta),
        (own_tail.alpha, own_tail.beta)
    );
    svc.delete_project(&own).await.unwrap();
    svc.delete_project(&foreign).await.unwrap();
}

#[tokio::test]
async fn grounding_removal_recomputes_without_erasing_independent_support() {
    let svc = service().await;
    let project = format!("learning-{}", Uuid::new_v4());
    let parent = isolation::seed_belief_in_project(
        "parent grounding source",
        0.5,
        0.0,
        &project,
        MemoryType::Fact,
    )
    .await
    .unwrap();
    let target = isolation::seed_belief_in_project(
        "target grounding claim",
        0.5,
        0.0,
        &project,
        MemoryType::Fact,
    )
    .await
    .unwrap();
    svc.add_edge(parent.id, target.id, EdgeType::Supports, 0.5)
        .await
        .unwrap();
    let chunk = mimir_core::documents::DocumentChunk::new(
        "grounding-removal.md".into(),
        vec![],
        "observed receipt".into(),
        None,
        Some(project.clone()),
    );
    let config = Config {
        database: isolation::fixture().database_config(),
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
        retirement: None,
    };
    let raw = AgeStore::new(
        db::connect(&config.database).await.unwrap(),
        config.database.dbname,
    )
    .unwrap();
    raw.insert_document_chunk(&chunk).await.unwrap();
    svc.add_evidence(target.id, chunk.id, 0.8).await.unwrap();
    let grounded = svc.get_belief(target.id).await.unwrap().unwrap();
    assert!((grounded.alpha - (target.alpha0 + 0.8 + 0.5 * 0.5 * 4.0)).abs() < 1e-8);
    raw.delete_evidence(chunk.id, target.id).await.unwrap();
    let after = svc.get_belief(target.id).await.unwrap().unwrap();
    assert!((after.alpha - (target.alpha0 + 0.5 * 0.5 * 4.0)).abs() < 1e-8);
    assert_eq!(after.beta, grounded.beta);
    svc.add_evidence(target.id, chunk.id, 0.8).await.unwrap();
    raw.delete_document_chunks(&[chunk.id]).await.unwrap();
    let after_chunk_delete = svc.get_belief(target.id).await.unwrap().unwrap();
    assert!((after_chunk_delete.alpha - after.alpha).abs() < 1e-8);
    svc.delete_project(&project).await.unwrap();
}
#[tokio::test]
async fn supersession_is_reversible_and_feedback_survives_propagation() {
    let svc = service().await;
    let project = format!("learning-{}", Uuid::new_v4());
    let a = isolation::seed_belief_in_project(
        "keyboard stale advice",
        0.99,
        0.99,
        &project,
        MemoryType::Experiential,
    )
    .await
    .unwrap();
    let b = isolation::seed_belief_in_project(
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
        .query_relevant(
            "keyboard",
            std::num::NonZeroUsize::new(10),
            Some(&project),
            None
        )
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
        .query_relevant(
            "keyboard",
            std::num::NonZeroUsize::new(10),
            Some(&project),
            None
        )
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
        .query_learning_context("keyboard", &project, std::num::NonZeroUsize::new(5))
        .await
        .unwrap();
    assert_eq!(context.patterns[0].successes, 1);
    assert_eq!(context.patterns[0].observed_success_probability, 2.0 / 3.0);
    e.outcome = Outcome::Failure;
    svc.record_experience(&e, 1).await.unwrap();
    let context = svc
        .query_learning_context("keyboard", &project, std::num::NonZeroUsize::new(5))
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
        svc.query_learning_context("keyboard", &project, std::num::NonZeroUsize::new(5))
            .await
            .unwrap()
            .patterns[0]
            .unknown,
        1
    );
    let mut foreign = experience("another-project");
    foreign.pattern_id = Some(p.id);
    assert!(svc.record_experience(&foreign, 0).await.is_err());
    let foreign_belief = isolation::seed_belief_in_project(
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
    let a =
        isolation::seed_belief_in_project("cause", 0.8, 0.0, &project, MemoryType::Experiential)
            .await
            .unwrap();
    let b =
        isolation::seed_belief_in_project("effect", 0.2, 0.0, &project, MemoryType::Experiential)
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
        let batch = svc
            .pending_experiences(Some(&project), std::num::NonZeroUsize::new(30))
            .await
            .unwrap();
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
    let a =
        isolation::seed_belief_in_project("claim A", 0.8, 0.1, &project, MemoryType::Experiential)
            .await
            .unwrap();
    let b =
        isolation::seed_belief_in_project("claim B", 0.7, 0.1, &project, MemoryType::Experiential)
            .await
            .unwrap();
    // Legacy support insertion deliberately does not trigger propagation.
    svc.add_edge(a.id, b.id, EdgeType::Supports, 1.0)
        .await
        .unwrap();
    let e = experience(&project);
    svc.record_experience(&e, 0).await.unwrap();
    let mut r = review(&e);
    r.links.push(LearningLink {
        from_id: a.id,
        to_id: b.id,
        relation: EdgeType::Contradicts,
        weight: 1.0,
    });
    svc.review_experience(&r, 0).await.unwrap();
    assert_eq!(svc.get_belief(b.id).await.unwrap().unwrap().alpha, b.alpha);
    assert!(!svc
        .get_contradictions(Some(&project))
        .await
        .unwrap()
        .is_empty());
    r.links.clear();
    svc.review_experience(&r, 1).await.unwrap();
    assert!(svc
        .get_contradictions(Some(&project))
        .await
        .unwrap()
        .is_empty());
    svc.delete_project(&project).await.unwrap();
}

#[tokio::test]
async fn source_coverage_is_atomic_revision_owned_and_preserves_unresolved_items() {
    use mimir_core::{
        assessment::{ItemKind, LearningItem},
        learning_sources::{Coverage, CoverageStatus, SourceRecord},
    };
    let svc = service().await;
    let mut e = experience(&format!("sources-{}", Uuid::new_v4()));
    e.source = ObservationSource::AgentReport;
    e.outcome = Outcome::Unknown;
    e.source_records = vec![SourceRecord {
        recorded_at: None,
        source_ref: "event/1".into(),
        actor: "agent".into(),
        provenance: ObservationSource::AgentReport,
        text: "I suggest testing first. Estimate: 30 minutes.".into(),
    }];
    e.evidence = vec!["event/1".into()];
    svc.record_experience(&e, 0).await.unwrap();
    let mut r = review(&e);
    assert!(
        svc.review_experience(&r, 0).await.is_err(),
        "legacy reviewer must not silently skip source extraction"
    );
    let item = LearningItem {
        id: None,
        key: Some("testing-suggestion".into()),
        kind: ItemKind::Suggestion,
        source_ref: "event/1".into(),
        actor: "agent".into(),
        statement: "I suggest testing first.".into(),
        conditions: "untried".into(),
        predictions: vec![],
    };
    r.extracted_items.push(item.clone());
    let mut legacy = r.clone();
    legacy.feedback.push(Feedback {
        belief_id: Uuid::new_v4(),
        verdict: Verdict::Support,
        weight: 1.0,
    });
    // Supply coverage so the rejection specifically concerns legacy evidence.
    legacy.source_coverage.push(Coverage {
        source_ref: "event/1".into(),
        status: CoverageStatus::Unresolved,
        reason: "pending".into(),
    });
    assert!(svc
        .review_experience(&legacy, 0)
        .await
        .unwrap_err()
        .to_string()
        .contains("source reviews use typed"));

    r.source_coverage.push(Coverage {
        source_ref: "event/1".into(),
        status: CoverageStatus::Complete,
        reason: "extracted suggestion".into(),
    });
    assert!(
        svc.review_experience(&r, 0).await.is_err(),
        "complete item needs an assessment"
    );
    r.source_coverage[0].status = CoverageStatus::Unresolved;
    r.source_coverage[0].reason = "Suggestion is untried; estimate still needs analysis".into();
    let first = svc.review_experience(&r, 0).await.unwrap();
    assert_eq!(first.review_revision, 1);
    assert_eq!(
        svc.review_experience(&r, 0).await.unwrap().review_revision,
        1
    );
    let receipt = svc.learning_review(e.id).await.unwrap();
    assert_eq!(
        receipt["review"]["source_coverage"][0]["status"],
        "unresolved"
    );
    assert!(
        !svc.pending_experiences(Some(&e.project), std::num::NonZeroUsize::new(10))
            .await
            .unwrap()
            .iter()
            .any(|s| s.experience.id == e.id),
        "unresolved review must not hot-loop unchanged evidence"
    );
    let mut changed = e.clone();
    changed.source_records[0].text = "Rewritten original".into();
    assert!(svc.record_experience(&changed, 1).await.is_err());
    e.source_records.push(SourceRecord {
        recorded_at: None,
        source_ref: "correction/1".into(),
        actor: "human".into(),
        provenance: ObservationSource::UserFeedback,
        text: "Testing was not attempted; actual duration unknown".into(),
    });
    e.evidence.push("correction/1".into());
    svc.record_experience(&e, 1).await.unwrap();
    assert!(svc.learning_review(e.id).await.unwrap()["review"].is_null());
    assert!(svc.review_experience(&r, 1).await.is_err());
    r.experience_revision = 2;
    r.source_coverage.push(Coverage {
        source_ref: "correction/1".into(),
        status: CoverageStatus::Complete,
        reason: "No additional decision, suggestion or estimate".into(),
    });
    let mut omitted = r.clone();
    omitted.extracted_items.clear();
    assert!(
        svc.review_experience(&omitted, 1).await.is_err(),
        "correction cannot discard extracted item"
    );
    let mut invented = r.clone();
    invented.extracted_items[0].statement = "Never said".into();
    assert!(svc.review_experience(&invented, 1).await.is_err());
    svc.review_experience(&r, 1).await.unwrap();
    assert_eq!(
        svc.learning_review(e.id).await.unwrap()["review"]["extracted_items"][0]["id"],
        first.item_ids["testing-suggestion"].to_string()
    );
}

#[tokio::test]
async fn complete_large_source_review_is_stored_and_read_back_without_caps() {
    use mimir_core::{
        assessment::{ItemKind, LearningItem},
        learning_sources::{Coverage, CoverageStatus, SourceRecord},
    };
    let svc = service().await;
    let mut e = experience(&format!("large-review-{}", Uuid::new_v4()));
    e.source = ObservationSource::AgentReport;
    e.outcome = Outcome::Unknown;
    e.source_records = (0..65)
        .map(|n| SourceRecord {
            recorded_at: None,
            source_ref: format!("source-{n}"),
            actor: "fixture".into(),
            provenance: ObservationSource::AgentReport,
            text: format!("Recommendation {n}: {}", "source text ".repeat(1200)),
        })
        .collect();
    e.evidence = e
        .source_records
        .iter()
        .map(|s| s.source_ref.clone())
        .collect();
    svc.record_experience(&e, 0).await.unwrap();
    let mut r = review(&e);
    r.source_coverage = e
        .source_records
        .iter()
        .map(|s| Coverage {
            source_ref: s.source_ref.clone(),
            status: CoverageStatus::Unresolved,
            reason: "No independent outcome evidence".into(),
        })
        .collect();
    r.extracted_items = e
        .source_records
        .iter()
        .map(|s| LearningItem {
            id: None,
            key: Some(s.source_ref.clone()),
            kind: ItemKind::Suggestion,
            source_ref: s.source_ref.clone(),
            actor: s.actor.clone(),
            statement: s.text.clone(),
            conditions: "Untried suggestion".into(),
            predictions: vec![],
        })
        .collect();
    assert!(serde_json::to_vec(&r).unwrap().len() > 65536);
    let applied = svc.review_experience(&r, 0).await.unwrap();
    assert_eq!(applied.review_revision, 1);
    for item in &mut r.extracted_items {
        item.id = Some(applied.item_ids[item.key.as_ref().unwrap()]);
    }
    let receipt = svc.learning_review(e.id).await.unwrap();
    assert_eq!(receipt["review"], serde_json::to_value(&r).unwrap());
    assert!(!svc
        .pending_experiences(Some(&e.project), std::num::NonZeroUsize::new(101))
        .await
        .unwrap()
        .iter()
        .any(|s| s.experience.id == e.id));
    svc.delete_project(&e.project).await.unwrap();
}

async fn item_database_client() -> tokio_postgres::Client {
    db::connect(&isolation::fixture().database_config())
        .await
        .unwrap()
}

fn postgres_item_fixture(project: &str) -> (Experience, Review) {
    use mimir_core::learning_sources::SourceRecord;
    let mut e = experience(project);
    e.outcome = Outcome::Unknown;
    e.source = ObservationSource::AgentReport;
    e.evidence = vec!["event/1".into()];
    e.source_records = vec![SourceRecord {
        source_ref: "event/1".into(),
        actor: "agent".into(),
        provenance: ObservationSource::AgentReport,
        text: "I estimate 30 minutes.".into(),
        recorded_at: None,
    }];
    let r = serde_json::from_value(serde_json::json!({
        "experience_id":e.id,"experience_revision":1,"reviewer":"postgres-item-fixture",
        "rationale":"Retain an estimate without inventing observed correctness",
        "extracted_items":[{"key":"estimate-1","kind":"estimate","source_ref":"event/1",
            "actor":"agent","statement":"I estimate 30 minutes.","conditions":"Unobserved"}],
        "candidates":[{"kind":"belief","key":"lesson","content":"An estimate needs outcome evidence"}],
        "assessments":[{"target":{"candidate_key":"lesson"},"scope":"task","rubric":"observed-outcome",
            "correctness":{"value":null,"weight":0},"usefulness":{"value":null,"weight":0},
            "evidence_indices":[0],"item_keys":["estimate-1"],"rationale":"Outcome absent"}],
        "source_coverage":[{"source_ref":"event/1","status":"complete","reason":"Retained the estimate"}]
    })).unwrap();
    (e, r)
}

#[tokio::test]
async fn postgres_item_ids_isolate_keys_and_keep_concurrent_retries_stable() {
    let project = format!("postgres-items-{}", Uuid::new_v4());
    let svc = grounded_service(&project).await;
    let other = grounded_service(&project).await;
    let (e, r) = postgres_item_fixture(&project);
    svc.record_experience(&e, 0).await.unwrap();
    let (a, b) = tokio::join!(svc.review_experience(&r, 0), other.review_experience(&r, 0));
    let a = a.unwrap();
    let b = b.unwrap();
    let assigned = a.item_ids["estimate-1"];
    assert_eq!(b.item_ids["estimate-1"], assigned);
    assert_eq!(a.review_revision, 1);
    assert_eq!(b.review_revision, 1);
    assert_eq!(
        service()
            .await
            .review_experience(&r, 0)
            .await
            .unwrap()
            .item_ids["estimate-1"],
        assigned
    );

    let canonical = svc.learning_review(e.id).await.unwrap()["review"].clone();
    assert_eq!(canonical["extracted_items"][0]["id"], assigned.to_string());
    assert_eq!(canonical["extracted_items"][0]["key"], "estimate-1");
    assert_eq!(
        canonical["assessments"][0]["item_ids"][0],
        assigned.to_string()
    );
    assert!(canonical["assessments"][0].get("item_keys").is_none());
    let mut correction: Review = serde_json::from_value(canonical).unwrap();
    correction.extracted_items[0].conditions = "Still waiting for independent evidence".into();
    let corrected = svc.review_experience(&correction, 1).await.unwrap();
    assert_eq!(corrected.item_ids["estimate-1"], assigned);
    assert_eq!(corrected.review_revision, 2);
    let history = svc.experience_history(e.id).await.unwrap();
    assert_eq!(history["reviews"].as_array().unwrap().len(), 2);

    let (e2, r2) = postgres_item_fixture(&project);
    svc.record_experience(&e2, 0).await.unwrap();
    let second = svc.review_experience(&r2, 0).await.unwrap();
    assert_ne!(second.item_ids["estimate-1"], assigned);
    let client = item_database_client().await;
    let rows = client.query("SELECT item_id FROM mimir_learning_item_owners WHERE experience_id=$1 AND item_key='estimate-1'", &[&e.id]).await.unwrap();
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0].get::<_, Uuid>(0), assigned);
    let default: String = client.query_one("SELECT pg_get_expr(d.adbin,d.adrelid) FROM pg_attrdef d JOIN pg_attribute a ON a.attrelid=d.adrelid AND a.attnum=d.adnum WHERE d.adrelid='mimir_learning_item_owners'::regclass AND a.attname='item_id'", &[]).await.unwrap().get(0);
    assert!(default.contains("gen_random_uuid()"));
    svc.delete_project(&project).await.unwrap();
}

#[tokio::test]
async fn postgres_item_ids_roll_back_allocations_and_reject_invented_uuids() {
    let client = item_database_client().await;
    let project = format!("postgres-items-{}", Uuid::new_v4());
    let svc = grounded_service(&project).await;
    let (e, mut r) = postgres_item_fixture(&project);
    svc.record_experience(&e, 0).await.unwrap();
    r.extracted_items[0].statement = "An invented quotation".into();
    let rejected = svc.review_experience(&r, 0).await.unwrap_err();
    assert!(
        rejected.to_string().contains("item estimate-1"),
        "feedback must use the stable key of the rolled-back allocation"
    );
    let count: i64 = client
        .query_one(
            "SELECT count(*) FROM mimir_learning_item_owners WHERE experience_id=$1",
            &[&e.id],
        )
        .await
        .unwrap()
        .get(0);
    assert_eq!(
        count, 0,
        "quotation refusal must roll back PostgreSQL allocation"
    );
    assert_eq!(
        svc.get_experience(e.id)
            .await
            .unwrap()
            .unwrap()
            .review_revision,
        0
    );
    r.extracted_items[0].statement = "I estimate 30 minutes.".into();
    r.extracted_items[0].actor = "nested-speaker".into();
    let rejected = svc.review_experience(&r, 0).await.unwrap_err();
    let refusal = rejected
        .downcast_ref::<mimir_core::validation::Refusal>()
        .unwrap();
    assert_eq!(refusal.fault.code, mimir_core::validation::Code::WrongActor);
    assert_eq!(
        refusal.fault.path,
        vec![
            mimir_core::validation::Segment::Key("extracted_items".into()),
            mimir_core::validation::Segment::Index(0),
            mimir_core::validation::Segment::Key("actor".into())
        ]
    );
    assert!(refusal.fault.message.contains("estimate-1"));
    assert!(refusal.fault.message.contains("expected \"agent\""));
    let count: i64 = client
        .query_one(
            "SELECT count(*) FROM mimir_learning_item_owners WHERE experience_id=$1",
            &[&e.id],
        )
        .await
        .unwrap()
        .get(0);
    assert_eq!(
        count, 0,
        "actor refusal must roll back PostgreSQL allocation"
    );
    r.extracted_items[0].actor = "agent".into();
    r.assessments[0].item_keys.push("missing-key".into());
    assert!(svc.review_experience(&r, 0).await.is_err());
    let count: i64 = client
        .query_one(
            "SELECT count(*) FROM mimir_learning_item_owners WHERE experience_id=$1",
            &[&e.id],
        )
        .await
        .unwrap()
        .get(0);
    assert_eq!(count, 0, "reference refusal must roll back allocation");
    r.assessments[0].item_keys.pop();
    let supplied = Uuid::new_v4();
    r.extracted_items[0].id = Some(supplied);
    assert!(svc.review_experience(&r, 0).await.is_err());
    r.extracted_items[0].key = None;
    assert!(svc.review_experience(&r, 0).await.is_err());
    assert_eq!(
        svc.get_experience(e.id)
            .await
            .unwrap()
            .unwrap()
            .review_revision,
        0
    );
    r.extracted_items[0].id = None;
    r.extracted_items[0].key = Some("estimate-1".into());
    let applied = svc.review_experience(&r, 0).await.unwrap();
    let assigned = applied.item_ids["estimate-1"];
    let mut wrong_id = r.clone();
    wrong_id.extracted_items[0].id = Some(supplied);
    assert!(svc.review_experience(&wrong_id, 1).await.is_err());
    let mut wrong_owner = r.clone();
    wrong_owner.extracted_items[0].actor = "another actor".into();
    assert!(svc.review_experience(&wrong_owner, 1).await.is_err());
    let mut omitted = r.clone();
    omitted.extracted_items.clear();
    assert!(svc.review_experience(&omitted, 1).await.is_err());
    assert_eq!(
        svc.learning_review(e.id).await.unwrap()["review"]["extracted_items"][0]["id"],
        assigned.to_string()
    );
    svc.delete_project(&project).await.unwrap();
}

#[tokio::test]
async fn postgres_item_ids_record_and_correct_experiences_without_reallocation() {
    use mimir_core::assessment::{ItemKind, LearningItem};
    let svc = service().await;
    let project = format!("postgres-items-{}", Uuid::new_v4());
    let mut e = experience(&project);
    e.learning_items.push(LearningItem {
        id: None,
        key: Some("estimate-1".into()),
        kind: ItemKind::Estimate,
        source_ref: "task/1".into(),
        actor: "agent".into(),
        statement: "30 minutes".into(),
        conditions: "Pending".into(),
        predictions: vec![],
    });
    let first = svc.record_experience(&e, 0).await.unwrap();
    let assigned = first.item_ids["estimate-1"];
    let retry = service().await.record_experience(&e, 0).await.unwrap();
    assert_eq!(retry.revision, 1);
    assert_eq!(retry.item_ids["estimate-1"], assigned);
    let mut another = e.clone();
    another.id = Uuid::new_v4();
    assert_ne!(
        svc.record_experience(&another, 0).await.unwrap().item_ids["estimate-1"],
        assigned
    );
    let mut correction = first.experience;
    correction.learning_items[0].conditions = "Outcome still unknown".into();
    correction.learning_items[0].key = None; // Legacy UUID-only correction.
    let corrected = svc.record_experience(&correction, 1).await.unwrap();
    assert_eq!(corrected.experience.learning_items[0].id, Some(assigned));
    assert_eq!(corrected.revision, 2);
    svc.delete_project(&project).await.unwrap();
}

#[tokio::test]
async fn postgres_item_ids_migration_preserves_historical_uuid_ownership() {
    let client = item_database_client().await;
    // Temporary relations shadow only this connection's test-database tables.
    // Exercise the additive migration against historical rows without changing
    // the real test ledger or rewriting/deleting any migration history.
    client.batch_execute("CREATE TEMP TABLE mimir_experience_versions(experience_id uuid,payload jsonb); CREATE TEMP TABLE mimir_review_versions(experience_id uuid,payload jsonb); CREATE TEMP TABLE mimir_learning_item_owners(item_id uuid PRIMARY KEY,experience_id uuid NOT NULL,source_ref text NOT NULL,actor text NOT NULL);").await.unwrap();
    let row = client
        .query_one(
            "SELECT gen_random_uuid(),gen_random_uuid(),gen_random_uuid()",
            &[],
        )
        .await
        .unwrap();
    let experience: Uuid = row.get(0);
    let original: Uuid = row.get(1);
    let extracted: Uuid = row.get(2);
    let payload = serde_json::json!({"learning_items":[{"id":original,"source_ref":"original","actor":"agent"}]}).to_string();
    client
        .execute(
            "INSERT INTO mimir_experience_versions VALUES($1,$2::text::jsonb)",
            &[&experience, &payload],
        )
        .await
        .unwrap();
    let payload = serde_json::json!({"extracted_items":[{"id":extracted,"source_ref":"extracted","actor":"agent"}]}).to_string();
    client
        .execute(
            "INSERT INTO mimir_review_versions VALUES($1,$2::text::jsonb)",
            &[&experience, &payload],
        )
        .await
        .unwrap();
    // Existing reservations take precedence over conflicting historical text.
    client
        .execute(
            "INSERT INTO mimir_learning_item_owners VALUES($1,$2,'reserved','owner')",
            &[&original, &experience],
        )
        .await
        .unwrap();
    client
        .batch_execute(include_str!("../migrations/010_postgres_item_ids.sql"))
        .await
        .unwrap();
    let rows = client.query("SELECT item_id,source_ref,actor,item_key FROM mimir_learning_item_owners ORDER BY source_ref", &[]).await.unwrap();
    assert_eq!(rows.len(), 2);
    assert_eq!(rows[0].get::<_, Uuid>(0), extracted);
    assert_eq!(rows[1].get::<_, Uuid>(0), original);
    assert_eq!(rows[1].get::<_, &str>(1), "reserved");
    assert_eq!(rows[1].get::<_, &str>(2), "owner");
    assert!(rows
        .iter()
        .all(|row| row.get::<_, Option<String>>(3).is_none()));
    let generated: Uuid = client.query_one("INSERT INTO mimir_learning_item_owners(experience_id,source_ref,actor,item_key) VALUES($1,'new','agent','estimate-1') RETURNING item_id", &[&experience]).await.unwrap().get(0);
    assert_ne!(generated, original);
    assert_ne!(generated, extracted);
}
