//! One assembly point for the declared business writers used by MCP and CLI.
//! Request arguments retain the admitted JSON, including omitted fields.
use crate::{
    interaction::{CorrectionItem, Location, NeedsInput},
    operation_catalogue::{
        CommitSite, GraphOperation as G, LearningOperation as L, Operation, RegisteredWrite,
    },
    store::{
        self, OperationBindingDecision, OperationBindingRequest, OperationOutcome, PlanDecision,
        StepDecision,
    },
    validation::{Code, Fault},
    MimirService,
};
use anyhow::{Context, Result};
use serde_json::{json, Value};
use uuid::Uuid;

/// Created only by the pure validator before an immutable request is bound.
#[derive(Debug)]
pub struct WriteAdmissionIssue(NeedsInput);
impl WriteAdmissionIssue {
    pub fn correction(&self) -> &NeedsInput {
        &self.0
    }
    fn new(operation: Operation, cause: anyhow::Error) -> Self {
        if let Some(correction) = cause.downcast_ref::<crate::interaction::RequestCorrection>() {
            return Self(correction.correction().clone().before_binding());
        }
        if let Some(correction) = cause.downcast_ref::<crate::preparation::PreparationRequired>() {
            return Self(correction.correction().clone().before_binding());
        }
        if let Some(refusal) = cause.downcast_ref::<crate::validation::Refusal>() {
            let mut fault = refusal.fault.clone();
            let root = match operation {
                Operation::Learning(L::RecordExperience) => Some("experience"),
                Operation::Learning(L::ReviewExperience) => Some("review"),
                _ => None,
            };
            if let Some(root) = root {
                if !matches!(fault.path.first(),Some(crate::validation::Segment::Key(key)) if key==root || key=="expected_revision" || key=="expected_review_revision")
                {
                    fault
                        .path
                        .insert(0, crate::validation::Segment::Key(root.into()));
                }
            }
            let issue=CorrectionItem::new(Location::Arguments,fault,
                format!("The indicated {} field satisfying its advertised schema and the condition explained above.",operation.name()),
                "Correct the indicated field using the intended request, then retry with the same reserved operation token. Ask the user if a required value is unknown. Do not invent evidence, change configuration automatically, or reserve another action to bypass a correction.".into()).expect("initial validation retains its field and repair");
            return Self(
                NeedsInput::new(issue, vec![])
                    .expect("one complete domain fault")
                    .before_binding(),
            );
        }
        let item = CorrectionItem::new(Location::Arguments,
            Fault {path:vec![],code:Code::MalformedInput,
                message:format!("The {} request cannot be admitted: {cause:#}. No request was bound and no business data changed.",operation.name())},
            format!("The complete {} arguments satisfying its advertised fields and the condition explained above.",operation.name()),
            "Correct the supplied arguments and retry using the same reserved token. If the intended value is uncertain, explain the problem and ask the user. Do not invent evidence, alter configuration automatically or reserve another action to bypass this correction.".into())
            .expect("initial write admission identifies the operation and repair");
        Self(NeedsInput::new(item, vec![]).expect("one described admission issue"))
    }
}
impl std::fmt::Display for WriteAdmissionIssue {
    fn fmt(&self, out: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        out.write_str(&self.0.issues()[0].fault().message)
    }
}
impl std::error::Error for WriteAdmissionIssue {}

fn validate_initial(operation: Operation, request: &OperationBindingRequest) -> Result<()> {
    match operation {
        Operation::Graph(G::InsertBelief) => store::admit_belief_request(request),
        Operation::Graph(G::LoadDocument) => store::document_arguments(request).map(|_| ()),
        Operation::Graph(
            G::InsertPattern | G::RecordSupport | G::RecordCause | G::RecordContradiction,
        ) => store::admit_direct_request(request),
        Operation::Learning(L::RecordExperience) => store::admit_source_operation(request),
        Operation::Learning(L::ReviewExperience) => store::admit_review_request(request),
        // Their public field/UUID/number admission is shared with MCP. Their
        // state-dependent conditions are checked in the real transaction.
        Operation::Graph(
            G::DeleteBelief
            | G::DeleteProject
            | G::DeletePattern
            | G::RecordDefeat
            | G::DecayAll
            | G::SweepExpiredDefeated
            | G::AddEvidence
            | G::PropagateFrom
            | G::ClearDocument,
        ) => Ok(()),
        Operation::Graph(
            G::GetBelief
            | G::ListBeliefs
            | G::ListPatterns
            | G::GetContradictions
            | G::QueryRelevant
            | G::GetEvidence
            | G::QueryIntervention
            | G::QueryDocument,
        )
        | Operation::Learning(
            L::LearningCapabilities
            | L::GetLessonAssessment
            | L::LessonAssessmentHistory
            | L::ExplainBelief
            | L::GetLearningReview
            | L::PendingExperiences
            | L::GetExperience
            | L::ExperienceHistory
            | L::QueryLearningContext,
        )
        | Operation::Control(_) => {
            anyhow::bail!("This operation is not a declared business writer")
        }
    }
}

impl MimirService {
    fn initial_operation_settings(&self, operation: Operation, arguments: &Value) -> Result<Value> {
        match operation {
            Operation::Graph(G::InsertBelief | G::LoadDocument)
            | Operation::Learning(L::ReviewExperience) => Ok(self.embedding_operation_settings()),
            Operation::Graph(G::SweepExpiredDefeated) => {
                Ok(store::sweep_settings(&self.retirement_policy()?))
            }
            Operation::Graph(G::ClearDocument) => {
                let path = arguments
                    .get("path")
                    .and_then(Value::as_str)
                    .context("Supply the original clear_document path string")?;
                Ok(mimir_json::clone_value(
                    self.clear_document_request(path)?.settings(),
                ))
            }
            Operation::Graph(_) | Operation::Learning(_) => Ok(json!({})),
            Operation::Control(_) => {
                anyhow::bail!("Operation controls do not create a business binding")
            }
        }
    }

    /// Bind the original admitted request once. Completed readback precedes
    /// present configuration, filesystem preparation and provider calls.
    pub async fn execute_registered_write(
        &self,
        writer: RegisteredWrite,
        token: Uuid,
        arguments: mimir_json::Document,
    ) -> Result<OperationOutcome> {
        self.own_operation(
            token,
            self.execute_registered_write_inner(writer, token, arguments),
        )
        .await
    }

    async fn execute_registered_write_inner(
        &self,
        writer: RegisteredWrite,
        token: Uuid,
        arguments: mimir_json::Document,
    ) -> Result<OperationOutcome> {
        let operation = writer.operation();
        let existing = self.read_operation_binding(token).await?;
        if existing.is_none() {
            let reservation = self.read_operation_outcome(token, None).await?;
            if !matches!(reservation, OperationOutcome::Reserved) {
                return Ok(reservation);
            }
        }
        let settings = match &existing {
            Some(original) => mimir_json::clone_value(original.request.settings()),
            None => self.initial_operation_settings(operation, &arguments)?,
        };
        let expected = OperationBindingRequest::new(
            operation.name().into(),
            arguments.into_value(),
            settings,
        )?;
        if existing.is_none() {
            validate_initial(operation, &expected)
                .map_err(|cause| WriteAdmissionIssue::new(operation, cause))?;
        }
        match self.bind_operation_request(token, &expected).await? {
            OperationBindingDecision::Bound(_) => {}
            OperationBindingDecision::ChangedRequest(original) => {
                return Ok(OperationOutcome::ChangedRequest(original))
            }
            OperationBindingDecision::UnknownToken | OperationBindingDecision::Cancelled(_) => {
                return self.read_operation_outcome(token, Some(&expected)).await
            }
        }
        let previous = self.read_operation_outcome(token, Some(&expected)).await?;
        if !matches!(
            previous,
            OperationOutcome::AwaitingPlan(_)
                | OperationOutcome::Pending { .. }
                | OperationOutcome::AwaitingCompletion(_)
        ) {
            return Ok(previous);
        }
        match operation {
            Operation::Graph(G::LoadDocument) => return self.load_document_operation(token).await,
            Operation::Graph(G::SweepExpiredDefeated) => {
                // The request is already bound without inserting defaults into
                // its JSON. The existing domain default is interpreted here.
                let threshold = expected
                    .arguments()
                    .get("prob_threshold")
                    .and_then(Value::as_f64)
                    .unwrap_or(0.3);
                let project = expected.arguments().get("project").and_then(Value::as_str);
                return self.sweep_operation(token, threshold, project).await;
            }
            _ => {}
        }
        let selection = if operation == Operation::Learning(L::ReviewExperience) {
            // Capture keys from the admitted declarations without normalizing
            // optional IDs or decoding unrelated numeric fields ahead of the
            // review's own structured validation boundary.
            let mut keys = Vec::new();
            if let Some(candidates) = expected
                .arguments()
                .get("review")
                .and_then(|review| review.get("candidates"))
                .and_then(Value::as_array)
            {
                for candidate in candidates {
                    if candidate.get("kind").and_then(Value::as_str) == Some("belief") {
                        keys.push(
                            candidate
                                .get("key")
                                .and_then(Value::as_str)
                                .context("Supply the original nonblank belief-candidate key")?
                                .to_owned(),
                        );
                    }
                }
            }
            vec![(CommitSite::EmbeddingOwnerReservation, keys)]
        } else {
            vec![]
        };
        let plan = match self
            .prepare_operation(token, &expected, move |_, _| {
                Box::pin(async move { Ok(selection) })
            })
            .await?
        {
            PlanDecision::Ready(plan) => plan,
            PlanDecision::NeedsRecovery(reason) => {
                return Ok(OperationOutcome::NeedsRecovery {
                    binding: self
                        .read_operation_binding(token)
                        .await?
                        .context("Read the original immutable binding")?,
                    reason,
                })
            }
            PlanDecision::UnknownBinding
            | PlanDecision::ChangedRequest(_)
            | PlanDecision::Cancelled(_) => {
                return self.read_operation_outcome(token, Some(&expected)).await
            }
        };
        match operation {
            Operation::Graph(G::InsertBelief) => {
                self.publish_belief_operation(&plan).await?;
            }
            Operation::Graph(G::RecordDefeat) => {
                self.record_defeat_operation(&plan).await?;
            }
            Operation::Learning(L::ReviewExperience) => {
                self.review_experience_operation(&plan).await?;
            }
            one => {
                let steps = plan.steps();
                let [step] = steps.as_slice() else {
                    anyhow::bail!("{} requires its original single committed step; read the saved plan and outcome before continuing",one.name());
                };
                let decision = match one {
                    Operation::Graph(G::DeleteBelief) => self.delete_belief_operation(step).await?,
                    Operation::Graph(G::DeleteProject) => {
                        self.delete_project_operation(step).await?
                    }
                    Operation::Graph(G::DeletePattern) => {
                        self.delete_pattern_operation(step).await?
                    }
                    Operation::Graph(G::InsertPattern) => {
                        self.create_pattern_operation(step).await?
                    }
                    Operation::Graph(
                        G::RecordSupport | G::RecordCause | G::RecordContradiction,
                    ) => self.direct_relationship_operation(step).await?,
                    Operation::Graph(G::DecayAll) => self.decay_operation(step).await?,
                    Operation::Graph(G::AddEvidence) => {
                        self.change_evidence_operation(step).await?
                    }
                    Operation::Graph(G::PropagateFrom) => self.propagate_operation(step).await?,
                    Operation::Graph(G::ClearDocument) => {
                        self.clear_document_operation(step).await?
                    }
                    Operation::Learning(L::RecordExperience) => {
                        self.record_experience_operation(step).await?
                    }
                    Operation::Graph(
                        G::InsertBelief
                        | G::RecordDefeat
                        | G::LoadDocument
                        | G::SweepExpiredDefeated,
                    )
                    | Operation::Learning(L::ReviewExperience) => anyhow::bail!(
                        "Use the complete registered operation, not a selected inner step"
                    ),
                    Operation::Graph(
                        G::GetBelief
                        | G::ListBeliefs
                        | G::ListPatterns
                        | G::GetContradictions
                        | G::QueryRelevant
                        | G::GetEvidence
                        | G::QueryIntervention
                        | G::QueryDocument,
                    )
                    | Operation::Learning(
                        L::LearningCapabilities
                        | L::GetLessonAssessment
                        | L::LessonAssessmentHistory
                        | L::ExplainBelief
                        | L::GetLearningReview
                        | L::PendingExperiences
                        | L::GetExperience
                        | L::ExperienceHistory
                        | L::QueryLearningContext,
                    )
                    | Operation::Control(_) => {
                        anyhow::bail!("This operation is not a declared business writer")
                    }
                };
                if let StepDecision::NeedsRecovery(reason) = decision {
                    return Ok(OperationOutcome::NeedsRecovery {
                        binding: self
                            .read_operation_binding(token)
                            .await?
                            .context("Read the original immutable binding")?,
                        reason,
                    });
                }
            }
        }
        self.read_operation_outcome(token, Some(&expected)).await
    }
}
