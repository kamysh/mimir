//! Original scope and user policy bind before a single atomic sweep.
use crate::{
    interaction::RequestCorrection,
    store::{self, OperationBindingRequest, OperationOutcome, PlanDecision, StepDecision},
    validation::Code,
    MimirService,
};
use anyhow::Result;
use uuid::Uuid;

impl MimirService {
    /// Resume one original sweep. A completed historical answer is returned
    /// before inspecting the current configuration or selecting any new work.
    pub async fn sweep_operation(
        &self,
        token: Uuid,
        threshold: f64,
        project: Option<&str>,
    ) -> Result<OperationOutcome> {
        if !threshold.is_finite() || !(0.0..=1.0).contains(&threshold) {
            return Err(crate::validation::Refusal::invalid(Code::InvalidNumber,
                vec![crate::validation::Segment::Key("prob_threshold".into())],
                "Supply a finite probability between 0 and 1 inclusive; no beliefs were read or deleted.").into());
        }
        let original = self.store.read_operation_binding(token).await?;
        let expected = if let Some(original) = original {
            if original.request.operation() != "sweep_expired_defeated" {
                return Ok(OperationOutcome::ChangedRequest(original));
            }
            let arguments: store::SweepArguments = mimir_json::decode_ref(original.request.arguments())
                .map_err(|_| RequestCorrection::bound_graph_request("operation_token", Code::MalformedInput,
                    "The stored sweep arguments are malformed. Read its original binding and saved outcome before deciding what to do.".into(),
                    "The original sweep scope and finite probability threshold, with no additional request fields."))?;
            if arguments.prob_threshold != threshold || arguments.project.as_deref() != project {
                return Ok(OperationOutcome::ChangedRequest(original));
            }
            original.request
        } else {
            let policy = self.retirement_policy()?;
            let mut arguments = serde_json::json!({"prob_threshold":threshold});
            if let Some(project) = project {
                arguments["project"] = serde_json::json!(project);
            }
            OperationBindingRequest::new(
                "sweep_expired_defeated".into(),
                arguments,
                store::sweep_settings(&policy),
            )?
        };
        match self.store.bind_operation_request(token, &expected).await? {
            store::OperationBindingDecision::Bound(_) => {}
            store::OperationBindingDecision::ChangedRequest(original) => {
                return Ok(OperationOutcome::ChangedRequest(original))
            }
            store::OperationBindingDecision::UnknownToken => {
                return Ok(OperationOutcome::UnknownToken)
            }
            store::OperationBindingDecision::Cancelled(_) => {
                return self
                    .store
                    .read_operation_outcome(token, Some(&expected))
                    .await
            }
        }
        let outcome = self
            .store
            .read_operation_outcome(token, Some(&expected))
            .await?;
        if !matches!(
            outcome,
            OperationOutcome::AwaitingPlan(_)
                | OperationOutcome::Pending { .. }
                | OperationOutcome::AwaitingCompletion(_)
        ) {
            return Ok(outcome);
        }
        let policy = self.retirement_policy()?;
        store::check_sweep_policy(&expected, &policy)?;
        let plan = match self.store.prepare_operation(token, &expected,
            |_, _| Box::pin(async { Ok(vec![]) })).await? {
            PlanDecision::Ready(plan) => plan,
            PlanDecision::NeedsRecovery(reason) => return Err(RequestCorrection::bound_graph_request(
                "operation_token", Code::StaleRevision, reason,
                "The current single-publication sweep plan. Read old completed results; ask the user before replacing unfinished historical work.").into()),
            _ => return self.store.read_operation_outcome(token, Some(&expected)).await,
        };
        let steps = plan.steps();
        let [step] = steps.as_slice() else {
            return Err(RequestCorrection::bound_graph_request("operation_token", Code::MalformedInput,
                "The saved sweep plan does not have its single publication. Nothing was selected or deleted.".into(),
                "The current registered sweep plan, with its original scope and policy.").into());
        };
        if let StepDecision::NeedsRecovery(reason) =
            self.store.sweep_operation(step, &policy).await?
        {
            return Err(RequestCorrection::bound_graph_request("operation_token", Code::StaleRevision, reason,
                "The original sweep plan, selected IDs and saved answers; do not repeat a completed deletion.").into());
        }
        self.store
            .read_operation_outcome(token, Some(&expected))
            .await
    }
}
