use super::*;
use crate::{
    learning::{Candidate, ExperienceState, Review},
    operation_catalogue::CommitSite,
    store::{
        OperationBindingRequest, OperationPlan, PlanDecision, ReviewPublicationState, StepDecision,
    },
};
use tokio::sync::oneshot;

async fn plan(service: &MimirService, review: &Review, expected: i64) -> Result<OperationPlan> {
    let client = db::connect(&isolation::fixture().database_config()).await?;
    let key: Uuid = client
        .query_one("SELECT gen_random_uuid()", &[])
        .await?
        .get(0);
    let token = service
        .reserve_operation(&key.to_string())
        .await?
        .operation_token;
    let request = OperationBindingRequest::new(
        "review_experience".into(),
        json!({"review":review,"expected_review_revision":expected}),
        service.embedding_operation_settings(),
    )?;
    service.bind_operation_request(token, &request).await?;
    let keys = review
        .candidates
        .iter()
        .filter_map(|candidate| match candidate {
            Candidate::Belief { key, .. } => Some(key.clone()),
            _ => None,
        })
        .collect();
    let PlanDecision::Ready(plan) = service
        .prepare_operation(token, &request, move |_, _| {
            Box::pin(async move { Ok(vec![(CommitSite::EmbeddingOwnerReservation, keys)]) })
        })
        .await?
    else {
        anyhow::bail!("Original review plan not saved")
    };
    Ok(plan)
}

fn done(result: StepDecision) -> Result<ExperienceState> {
    let StepDecision::Done(answer) = result else {
        anyhow::bail!("Review did not complete: {result:?}")
    };
    Ok(mimir_json::decode_ref(&answer.reply)?)
}

#[tokio::test]
async fn original_review_owners_and_completed_answer_survive_reconnect_and_later_deletion(
) -> Result<()> {
    let (service, project) = service(Some(Ok(vec![vector(0)]))).await?;
    passage(&service, Some(&project), 0, "registered-review").await?;
    let review = review_request(&service, &project).await?;
    let plan = plan(&service, &review, 0).await?;
    let ReviewPublicationState::Preparing { owners, .. } = service
        .store
        .resume_review_operation(&plan, &service.embedding_operation_settings())
        .await?
    else {
        anyhow::bail!("Expected owner phase")
    };
    let original = owners["lesson"].clone();
    no_publication(&service, original.id).await?;
    let (mut other, _) = super::service(Some(Ok(vec![vector(0)]))).await?;
    let ReviewPublicationState::Preparing {
        owners: retried, ..
    } = other
        .store
        .resume_review_operation(&plan, &other.embedding_operation_settings())
        .await?
    else {
        anyhow::bail!("Expected original owner")
    };
    assert_eq!(retried["lesson"].id, original.id);
    assert_eq!(retried["lesson"].created_at, original.created_at);
    let state = done(other.review_experience_operation(&plan).await?)?;
    assert_eq!(state.review_revision, 1);
    assert_eq!(state.reviewed_revision, 1);
    assert_eq!(state.candidate_ids["lesson"], original.id);
    assert_eq!(
        other.get_belief(original.id).await?.unwrap().created_at,
        original.created_at
    );
    assert_eq!(
        other
            .get_belief(original.id)
            .await?
            .unwrap()
            .probability
            .value(),
        0.5
    );
    assert!(other
        .evidence_for_belief(original.id, None)
        .await?
        .is_empty());
    let client = db::connect(&isolation::fixture().database_config()).await?;
    let counts=client.query_one("SELECT (SELECT count(*) FROM mimir_review_versions WHERE experience_id=$1), (SELECT count(*) FROM mimir_operation_step_replies WHERE operation_token=$2), (SELECT count(*) FROM mimir_embedding_owners WHERE operation_token=$2), (SELECT count(*) FROM mimir_belief_sources WHERE belief_id=$3)", &[&review.experience_id,&plan.operation_token(),&original.id]).await?;
    assert_eq!(
        (
            counts.get::<_, i64>(0),
            counts.get::<_, i64>(1),
            counts.get::<_, i64>(2),
            counts.get::<_, i64>(3)
        ),
        (1, 3, 0, 1)
    );
    other.delete_belief(original.id).await?;
    // A later world is retained; historical completion never recreates data
    // or contacts the provider, even after current settings change.
    other.embeddings = None;
    other.embedding_operation_settings = json!({"embeddings":null});
    let replay = done(other.review_experience_operation(&plan).await?)?;
    assert_eq!(
        mimir_json::to_value(&replay)?,
        mimir_json::to_value(&state)?
    );
    no_publication(&other, original.id).await?;
    Ok(())
}

struct Stop(Option<oneshot::Sender<()>>);
impl Drop for Stop {
    fn drop(&mut self) {
        if let Some(sent) = self.0.take() {
            let _ = sent.send(());
        }
    }
}
struct Blocked {
    started: Mutex<Option<oneshot::Sender<()>>>,
    dropped: Mutex<Option<oneshot::Sender<()>>>,
}
impl EmbeddingProvider for Blocked {
    fn embed<'a>(&'a self, _: &'a [String], _: EmbeddingCancellation) -> EmbedFuture<'a> {
        Box::pin(async move {
            let _owned = Stop(self.dropped.lock().unwrap().take());
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
fn blocked(service: &mut MimirService) -> (oneshot::Receiver<()>, oneshot::Receiver<()>) {
    let (started, begin) = oneshot::channel();
    let (dropped, stopped) = oneshot::channel();
    service.embeddings = Some(OwnedEmbeddingBackend::for_test(Box::new(Blocked {
        started: Mutex::new(Some(started)),
        dropped: Mutex::new(Some(dropped)),
    })));
    (begin, stopped)
}

#[tokio::test]
async fn source_or_review_change_stops_both_raw_and_registered_owned_jobs() -> Result<()> {
    for registered in [false, true] {
        for source_change in [false, true] {
            let (mut service, project) = service(Some(Ok(vec![]))).await?;
            passage(&service, Some(&project), 0, "review-source-change").await?;
            let review = review_request(&service, &project).await?;
            let original = review.clone();
            let plan = plan(&service, &review, 0).await?;
            let token = plan.operation_token();
            let (begin, stopped) = blocked(&mut service);
            let job = tokio::spawn(async move {
                if registered {
                    service.review_experience_operation(&plan).await.map(|_| ())
                } else {
                    service.review_experience(&review, 0).await.map(|_| ())
                }
            });
            begin.await?;
            let (writer, _) = super::service(None).await?;
            if source_change {
                let mut source = writer
                    .get_experience(original.experience_id)
                    .await?
                    .unwrap()
                    .experience;
                source.context.push_str(" corrected source");
                writer.record_experience(&source, 1).await?;
            } else {
                let mut next = original.clone();
                next.candidates.clear();
                next.rationale = "a different feedback-only review".into();
                writer.review_experience(&next, 0).await?;
            }
            stopped.await?;
            let error = job.await?.unwrap_err();
            assert!(format!("{error:#}").contains("stale"));
            assert!(writer.list_beliefs(Some(&project)).await?.is_empty());
            if registered {
                assert!(writer
                    .read_operation_step(token, "@operation-result")
                    .await?
                    .is_none());
            }
        }
    }
    Ok(())
}

#[tokio::test]
async fn concurrent_exact_review_stops_redundant_provider_and_preserves_its_original_candidates(
) -> Result<()> {
    let (mut service, project) = service(Some(Ok(vec![]))).await?;
    passage(&service, Some(&project), 0, "exact-review").await?;
    let review = review_request(&service, &project).await?;
    let plan = plan(&service, &review, 0).await?;
    let original = review.clone();
    let original_plan = plan.clone();
    let (begin, stopped) = blocked(&mut service);
    let job = tokio::spawn(async move { service.review_experience_operation(&plan).await });
    begin.await?;
    let (writer, _) = super::service(Some(Ok(vec![vector(1)]))).await?;
    let state = writer.review_experience(&original, 0).await?;
    stopped.await?;
    let saved = done(job.await??)?;
    assert_eq!(mimir_json::to_value(&saved)?, mimir_json::to_value(&state)?);
    let client = db::connect(&isolation::fixture().database_config()).await?;
    assert_eq!(
        client
            .query_one(
                "SELECT count(*) FROM mimir_embedding_owners WHERE operation_token=$1",
                &[&original_plan.operation_token()]
            )
            .await?
            .get::<_, i64>(0),
        0
    );
    assert_eq!(
        client
            .query_one(
                "SELECT count(*) FROM mimir_review_versions WHERE experience_id=$1",
                &[&original.experience_id]
            )
            .await?
            .get::<_, i64>(0),
        1
    );
    let stored: pgvector::Vector = client
        .query_one(
            "SELECT embedding FROM belief_embeddings WHERE belief_id=$1",
            &[&state.candidate_ids["lesson"]],
        )
        .await?
        .get(0);
    assert_eq!(stored.to_vec(), vector(1));
    Ok(())
}

#[tokio::test]
async fn explicit_cancellation_stops_the_job_and_retains_its_owner_answer() -> Result<()> {
    let (mut service, project) = service(Some(Ok(vec![]))).await?;
    passage(&service, Some(&project), 0, "cancel-review").await?;
    let review = review_request(&service, &project).await?;
    let plan = plan(&service, &review, 0).await?;
    let token = plan.operation_token();
    let owner_key = plan.steps()[0].id().to_owned();
    let (begin, stopped) = blocked(&mut service);
    let job = tokio::spawn(async move { service.review_experience_operation(&plan).await });
    begin.await?;
    let (writer, _) = super::service(None).await?;
    let before = writer
        .read_operation_step(token, &owner_key)
        .await?
        .unwrap();
    writer.record_operation_cancellation(token).await?;
    stopped.await?;
    assert!(matches!(job.await??, StepDecision::Cancelled(_)));
    assert_eq!(
        writer
            .read_operation_step(token, &owner_key)
            .await?
            .unwrap(),
        before
    );
    assert!(writer
        .read_operation_step(token, "@operation-result")
        .await?
        .is_none());
    assert!(writer.list_beliefs(Some(&project)).await?.is_empty());
    Ok(())
}

#[tokio::test]
async fn rejected_saved_answer_rolls_back_the_whole_review_and_keeps_preparation_prefix(
) -> Result<()> {
    let (service, project) = service(Some(Ok(vec![vector(0)]))).await?;
    passage(&service, Some(&project), 0, "rollback-review").await?;
    let review = review_request(&service, &project).await?;
    let plan = plan(&service, &review, 0).await?;
    let token = plan.operation_token();
    let client = db::connect(&isolation::fixture().database_config()).await?;
    let suffix = token.simple();
    client.batch_execute(&format!("CREATE FUNCTION public.review_reject_{suffix}() RETURNS trigger LANGUAGE plpgsql AS $$ BEGIN IF NEW.operation_token='{token}'::uuid AND NEW.step='@operation-result' THEN RAISE EXCEPTION 'owned review final answer rejected'; END IF; RETURN NEW; END $$; CREATE TRIGGER review_reject_{suffix} BEFORE INSERT ON mimir_operation_step_replies FOR EACH ROW EXECUTE FUNCTION public.review_reject_{suffix}();")).await?;
    let result = service.review_experience_operation(&plan).await;
    client.batch_execute(&format!("DROP TRIGGER review_reject_{suffix} ON mimir_operation_step_replies; DROP FUNCTION public.review_reject_{suffix}();")).await?;
    assert!(format!("{:#}", result.unwrap_err()).contains("owned review final answer rejected"));
    assert!(service.list_beliefs(Some(&project)).await?.is_empty());
    assert_eq!(
        service
            .get_experience(review.experience_id)
            .await?
            .unwrap()
            .review_revision,
        0
    );
    assert!(service
        .read_operation_step(token, "@operation-result")
        .await?
        .is_none());
    assert!(service
        .read_operation_step(token, plan.steps().last().unwrap().id())
        .await?
        .is_none());
    assert!(service
        .read_operation_step(token, plan.steps()[0].id())
        .await?
        .is_some());
    let counts=client.query_one("SELECT (SELECT count(*) FROM mimir_review_candidates WHERE experience_id=$1),(SELECT count(*) FROM mimir_review_versions WHERE experience_id=$1),(SELECT count(*) FROM mimir_embedding_owners WHERE operation_token=$2)",&[&review.experience_id,&token]).await?;
    assert_eq!(
        (
            counts.get::<_, i64>(0),
            counts.get::<_, i64>(1),
            counts.get::<_, i64>(2)
        ),
        (0, 0, 1)
    );
    Ok(())
}

#[tokio::test]
async fn retiring_a_historical_candidate_stops_preparation_without_changing_revisions() -> Result<()>
{
    let (mut service, project) = service(Some(Ok(vec![]))).await?;
    passage(&service, Some(&project), 0, "retired-review-candidate").await?;
    let mut review = review_request(&service, &project).await?;
    let mut prior = review.clone();
    prior
        .candidates
        .retain(|c| matches!(c, Candidate::Pattern { .. }));
    let original = service.review_experience(&prior, 0).await?;
    review.rationale = "same pattern, with an additional supported belief".into();
    let plan = plan(&service, &review, 1).await?;
    let token = plan.operation_token();
    let (begin, stopped) = blocked(&mut service);
    let job = tokio::spawn(async move { service.review_experience_operation(&plan).await });
    begin.await?;
    let (writer, _) = super::service(None).await?;
    assert!(
        writer
            .delete_pattern(original.candidate_ids["procedure"])
            .await?
    );
    stopped.await?;
    assert!(format!("{:#}", job.await?.unwrap_err()).contains("deleted"));
    let current = writer.get_experience(prior.experience_id).await?.unwrap();
    assert_eq!((current.revision, current.review_revision), (1, 1));
    assert!(writer
        .read_operation_step(token, "@operation-result")
        .await?
        .is_none());
    assert!(writer.list_beliefs(Some(&project)).await?.is_empty());
    Ok(())
}

#[tokio::test]
async fn actual_writer_time_updates_posteriors_without_rewriting_original_creation_time(
) -> Result<()> {
    use crate::learning::{BeliefTarget, CandidateFeedback, Verdict};
    let (service, project) = service(Some(Ok(vec![vector(0)]))).await?;
    passage(&service, Some(&project), 0, "writer-clock-review").await?;
    let mut review = review_request(&service, &project).await?;
    review.candidate_feedback.push(CandidateFeedback {
        target: BeliefTarget::Candidate {
            candidate_key: "lesson".into(),
        },
        verdict: Verdict::Support,
        weight: 1.0,
    });
    let plan = plan(&service, &review, 0).await?;
    let ReviewPublicationState::Preparing { owners, .. } = service
        .store
        .resume_review_operation(&plan, &service.embedding_operation_settings())
        .await?
    else {
        anyhow::bail!("Owner not reserved")
    };
    let created_at = owners["lesson"].created_at;
    let mut client = db::connect(&isolation::fixture().database_config()).await?;
    let lock = client.transaction().await?;
    lock.query("SELECT pg_advisory_xact_lock(671942183)", &[])
        .await?;
    // The provider packet is ready before the writer lock is released. The
    // final clock is sampled after acquiring that lock, not at reservation.
    let token = plan.operation_token();
    let mut prepared = std::collections::HashMap::new();
    let Candidate::Belief { grounding, .. } = review
        .candidates
        .iter()
        .find(|c| c.key() == "lesson")
        .unwrap()
    else {
        unreachable!()
    };
    let support = service
        .store
        .validate_indexed_support(Some(&project), grounding)
        .await?;
    let value = service
        .prepare_owned_belief(owners["lesson"].clone(), None, support)
        .await?;
    prepared.insert("lesson".into(), value);
    let final_step = plan.steps().last().unwrap().clone();
    let boundary: chrono::DateTime<chrono::Utc> = lock
        .query_one("SELECT clock_timestamp()", &[])
        .await?
        .get(0);
    lock.commit().await?;
    let state = done(
        service
            .store
            .publish_review_operation(&final_step, &prepared)
            .await?,
    )?;
    let belief = service
        .get_belief(state.candidate_ids["lesson"])
        .await?
        .unwrap();
    assert_eq!(belief.created_at, created_at);
    assert!(belief.decay_accounted_at >= boundary && belief.decay_accounted_at > created_at);
    assert!(belief.probability.value() > 0.5);
    assert!(matches!(
        service.read_operation_outcome(token, None).await?,
        crate::store::OperationOutcome::Completed { .. }
    ));
    Ok(())
}

#[tokio::test]
async fn a_later_provider_failure_keeps_every_candidate_unpublished_and_the_operation_pending(
) -> Result<()> {
    struct Sequence(Mutex<std::collections::VecDeque<Result<Vec<Vec<f32>>>>>);
    impl EmbeddingProvider for Sequence {
        fn embed<'a>(&'a self, _: &'a [String], _: EmbeddingCancellation) -> EmbedFuture<'a> {
            Box::pin(async move { self.0.lock().unwrap().pop_front().unwrap() })
        }
    }
    let (mut service, project) = service(Some(Ok(vec![]))).await?;
    passage(&service, Some(&project), 0, "partial-review-preparation").await?;
    let mut review = review_request(&service, &project).await?;
    let Candidate::Belief { grounding, .. } = &review.candidates[1] else {
        unreachable!()
    };
    review.candidates.push(Candidate::Belief {
        key: "second".into(),
        content: "a second separately prepared belief".into(),
        memory_type: MemoryType::Experiential,
        grounding: grounding.clone(),
    });
    let plan = plan(&service, &review, 0).await?;
    service.embeddings = Some(OwnedEmbeddingBackend::for_test(Box::new(Sequence(
        Mutex::new(
            [
                Ok(vec![vector(0)]),
                Err(anyhow::anyhow!("actual second preparation failed")),
            ]
            .into(),
        ),
    ))));
    let error = service
        .review_experience_operation(&plan)
        .await
        .unwrap_err();
    assert!(format!("{error:#}").contains("actual second preparation failed"));
    assert!(service.list_beliefs(Some(&project)).await?.is_empty());
    assert_eq!(
        service
            .get_experience(review.experience_id)
            .await?
            .unwrap()
            .review_revision,
        0
    );
    let client = db::connect(&isolation::fixture().database_config()).await?;
    assert_eq!(
        client
            .query_one(
                "SELECT count(*) FROM mimir_operation_step_replies WHERE operation_token=$1",
                &[&plan.operation_token()]
            )
            .await?
            .get::<_, i64>(0),
        2
    );
    assert!(service
        .read_operation_step(plan.operation_token(), "@operation-result")
        .await?
        .is_none());
    Ok(())
}
