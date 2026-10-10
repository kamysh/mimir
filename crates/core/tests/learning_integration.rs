//! Run only against a disposable database; intentionally uses real AGE and migrations.
use mimir_core::{
    config::{Config, DatabaseConfig, SslMode},
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
        llm: None,
        judge: None,
        email: None,
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

#[tokio::test]
async fn sql_pages_cover_large_filtered_corpus_without_a_total_cutoff() {
    let _page_guard = PAGE_TEST_LOCK.lock().await;
    let svc = service().await;
    let project = format!("paging-{}", Uuid::new_v4());
    let mut expected = std::collections::HashSet::new();
    for n in 0..207 {
        let b = svc
            .add_belief_in_project(
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
    assert!(svc
        .list_beliefs_page(Some(&project), None, 11, 0)
        .await
        .is_err());
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
    let global = svc
        .add_belief("pager global marker", 0.5, 0.0, MemoryType::Fact)
        .await
        .unwrap();
    let a = svc
        .add_belief_in_project("pager local first", 0.5, 0.0, &project, MemoryType::Fact)
        .await
        .unwrap();
    let b = svc
        .add_belief_in_project("pager local second", 0.5, 0.0, &project, MemoryType::Fact)
        .await
        .unwrap();
    let outside = svc
        .add_belief_in_project("pager foreign", 0.5, 0.0, &foreign, MemoryType::Fact)
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
    assert!(svc
        .list_beliefs_page(Some(&project), None, 11, 0)
        .await
        .is_err());
    assert!(svc
        .list_beliefs_page(Some(&project), None, 1, usize::MAX)
        .await
        .is_err());
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
    }
}

/// Fixed Step-11 scenarios exercise the real ledger, candidate ownership, and
/// later retrieval. The deterministic chooser checks whether a retrieved lesson
/// applies; it is not a claim about an LLM's later behavior.
#[tokio::test]
async fn offline_learning_scenario_matrix() {
    let svc = service().await;
    let project = format!("learning-scenarios-{}", Uuid::new_v4());
    let foreign = format!("learning-scenarios-{}", Uuid::new_v4());
    let foreign_belief = svc
        .add_belief_in_project(
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
        .query_learning_context("stale keyboard indicator", &project, 20)
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
        .query_learning_context("disk quota exceeded", &project, 20)
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
            None => assert_eq!((belief.alpha, belief.beta), (1.0, 1.0)),
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
    assert_eq!(svc.get_belief(id).await.unwrap().unwrap().alpha, 1.0);
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
    let belief = svc
        .add_belief_in_project(
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
        svc.explain_belief(belief.id, 0, 10).await.unwrap()["candidate_provenance"].is_null(),
        "standalone belief unexpectedly gained incident provenance"
    );
    svc.delete_project(&project).await.unwrap();
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
async fn atomic_candidates_retry_retraction_and_observed_pattern_use() {
    let svc = service().await;
    let project = format!("learning-{}", Uuid::new_v4());
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
    assert!((svc.get_belief(belief_id).await.unwrap().unwrap().alpha - 4.0).abs() < 1e-9);
    assert_eq!(
        svc.review_experience(&r, 0).await.unwrap().candidate_ids,
        first.candidate_ids
    );
    assert_eq!(
        svc.review_experience(&r, 1).await.unwrap().review_revision,
        1
    );
    let candidate = svc.explain_belief(belief_id, 0, 10).await.unwrap();
    assert_eq!(candidate["candidate_provenance"]["active"], true);
    let before_use = svc
        .query_learning_context("keyboard session lifecycle", &project, 10)
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
        .query_learning_context("keyboard session lifecycle", &project, 10)
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
    assert!((after.alpha - 1.0).abs() < 1e-9);
    assert_eq!(
        svc.explain_belief(belief_id, 0, 10).await.unwrap()["candidate_provenance"]["active"],
        false
    );
    let after = svc
        .query_learning_context("keyboard session lifecycle", &project, 10)
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
async fn source_correction_deactivates_candidate_support_without_deleting_identity() {
    let svc = service().await;
    let project = format!("learning-{}", Uuid::new_v4());
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
    assert!((svc.get_belief(id).await.unwrap().unwrap().alpha - 5.0).abs() < 1e-9);
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
    assert!((svc.get_belief(id).await.unwrap().unwrap().alpha - 1.0).abs() < 1e-9);
    assert_eq!(
        svc.explain_belief(id, 0, 10).await.unwrap()["candidate_provenance"]["active"],
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
    let svc = service().await;
    let project = format!("learning-{}", Uuid::new_v4());
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
    let svc = service().await;
    let project = format!("learning-{}", Uuid::new_v4());
    let target = svc
        .add_belief_in_project("downstream claim", 0.5, 0.0, &project, MemoryType::Fact)
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
    let seed = svc
        .add_belief_in_project("local seed", 0.5, 0.0, &own, MemoryType::Fact)
        .await
        .unwrap();
    let foreign_node = svc
        .add_belief_in_project("foreign bridge", 0.5, 0.0, &foreign, MemoryType::Fact)
        .await
        .unwrap();
    let own_tail = svc
        .add_belief_in_project("own tail", 0.5, 0.0, &own, MemoryType::Fact)
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
    let parent = svc
        .add_belief_in_project(
            "parent grounding source",
            0.5,
            0.0,
            &project,
            MemoryType::Fact,
        )
        .await
        .unwrap();
    let target = svc
        .add_belief_in_project(
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
        database: DatabaseConfig {
            host: std::env::var("MIMIR_HOST").unwrap(),
            port: std::env::var("MIMIR_PORT").unwrap().parse().unwrap(),
            user: std::env::var("MIMIR_USER").unwrap(),
            dbname: std::env::var("MIMIR_DBNAME").unwrap(),
            ssl_mode: SslMode::Disable,
            ssl_root_cert: None,
            ssl_client_cert: None,
            ssl_client_key: None,
        },
        embeddings: None,
        llm: None,
        judge: None,
        email: None,
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
    let a = svc
        .add_belief_in_project("claim A", 0.8, 0.1, &project, MemoryType::Experiential)
        .await
        .unwrap();
    let b = svc
        .add_belief_in_project("claim B", 0.7, 0.1, &project, MemoryType::Experiential)
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
