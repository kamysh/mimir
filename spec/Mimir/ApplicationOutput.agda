{-# OPTIONS --safe #-}
-- Exhaustive result classification and JSON projection. Failed/uncertain
-- operations remain errors even if an earlier component committed. The error
-- retains its complete typed cause for the host's diagnostic formatter.
module Mimir.ApplicationOutput where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.String using (String; toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)
open import Mimir.Text using (Text)
import Mimir.StructuredValue as V
import Mimir.PublicEncoding as Encoding
import Mimir.ApplicationProtocol as Application
import Mimir.GraphMutationProtocol as Mutation
import Mimir.GroundingPublication as Ground
import Mimir.GraphReadProtocol as Read
import Mimir.GraphRecords as Records
import Mimir.InferenceProtocol as Inference
import Mimir.DocumentQuery as DocumentQuery
import Mimir.LearningQueryProtocol as Query
import Mimir.LearningOperations as Operations
import Mimir.LearningHistory as History
import Mimir.LearningHistoryWire as RawHistory
import Mimir.ExperienceRead as Experiences
import Mimir.ReviewObservation as Observation
import Mimir.ExperienceSchema as Experience
import Mimir.BeliefExplanation as Explain
import Mimir.ReviewEdges as Edges
import Mimir.IndependentProvenance as Origin
import Mimir.CandidateProvenance as Provenance
import Mimir.PatternOutcomes as Pattern
import Mimir.RetrievalProtocol as Retrieval
import Mimir.LearningContext as Context
import Mimir.LearningContextProtocol as ContextProtocol
import Mimir.AssessmentRead as Assessment
import Mimir.AssessmentSelection as Selection
import Mimir.AssessmentEvaluation as Evaluation
import Mimir.AssessmentScores as Scores
import Mimir.LearningCapabilities as Capabilities
import Mimir.BeliefEmbedding as Embedding
import Mimir.McpErrors as Errors
import Mimir.Validation as Validation
import Mimir.GraphDeletion as Deletion
import Mimir.ExperienceRecord as Recording
import Mimir.ReviewRecord as Reviewing
import Mimir.ReviewNumericalPublication as ReviewNumerical
import Mimir.PosteriorComputation as Posterior
import Mimir.ApplicationStore as Store
import Mimir.PublicOperationCatalogue as Catalogue
import Mimir.RecoverableStoreStep as Step
import Mimir.OperationControls as Controls
import Mimir.PublicRetrievalRecovery as Search
import Mimir.Recovery as Recovery
import Mimir.FaultWire as FaultWire
import Mimir.InferenceStorageBinding as NumericalRead
import Mimir.GroundingRecovery as GroundingRecovery
import Mimir.BeliefDeletionRecovery as BeliefDeletion
import Mimir.IndependentBeliefRecovery as IndependentIntent
import Mimir.StandardLibrary as Library
import Mimir.DecayRecovery as DecayRecovery
import Mimir.DefeatRecovery as DefeatRecovery
import Mimir.StorageSemantics as Stored
import Mimir.PublicRequest as Public
import Mimir.ReviewSchema as Relations
import Data.Float.Base as Float

module Project (environment : Application.Environment) (format : Encoding.Formatting) where
  module A = Application.Run environment
  open Encoding
  open Encode format

  data Projection : Set where
    success : V.Value → Projection
    failure : A.Result → Projection
    decision : Errors.AgentCorrection.Claim → Projection
    partialDecision : Mutation.CommittedEdge → Errors.AgentCorrection.Claim → Projection

  flag : String → Bool → V.Value
  flag fieldKey value = object ((fieldKey , V.boolean value) ∷ [])
  count : String → ℕ → V.Value
  count fieldKey value = object ((fieldKey , V.unsigned value) ∷ [])

  -- Rendering uses the standard Float and configured UUID dependencies. The
  -- business decision retains every observed value; no diagnostic cutoff.
  numericalCounts : Posterior.State → Text
  numericalCounts [] = []
  numericalCounts ((identity , counts) ∷ rest) =
    toList "belief " ++ Formatting.uuidText format identity ++
    toList ": alpha=" ++ toList (Float.show (Posterior.Beta.alpha counts)) ++
    toList ", beta=" ++ toList (Float.show (Posterior.Beta.negative counts)) ++
    toList "; " ++ numericalCounts rest

  numericalHistory : List Posterior.State → Text
  numericalHistory [] = []
  numericalHistory (first ∷ rest) = toList "[" ++ numericalCounts first ++
    toList "] " ++ numericalHistory rest

  numericalCorrection : Posterior.State → List Posterior.State → Errors.AgentCorrection.Claim
  numericalCorrection repeated visited = Errors.AgentCorrection.claim
    (Errors.AgentCorrection.item Errors.AgentCorrection.arguments
      (Validation.problem [] Validation.unsupportedCombination
        (toList "Cyclic propagation repeats incomplete stored-count states. This calculation produced no complete result. Repeated values: " ++
         numericalCounts repeated ++ toList "Observed history: " ++ numericalHistory visited))
      (toList "Every final alpha and beta must equal the value recomputed from its fixed prior and all incoming evidence in that same final state.")
      (toList "Open a dialog with the user showing the repeated values. Ask whether to cancel or agree on an explicit numerical accuracy policy before retrying. Do not choose an iterate, change weights, invent a tolerance, or retry automatically.")) []

  partialValue : Mutation.CommittedEdge → Errors.AgentCorrection.Claim → V.Value
  partialValue edge report = object
    (("status" , V.string (toList "needs_input")) ∷
     ("issues" , Errors.AgentCorrection.issues report) ∷
     ("next_action" , V.string (toList "ask_user")) ∷
     ("business_changes" , object (("committed_edge" , object
       (("from_id" , uuid (Mutation.CommittedEdge.from edge)) ∷
        ("to_id" , uuid (Mutation.CommittedEdge.to edge)) ∷
        ("relation" , V.string (toList "defeats")) ∷
        ("weight" , V.floating (Mutation.CommittedEdge.weight edge)) ∷ [])) ∷ [])) ∷
     ("posterior_publication" , V.string (toList "not_performed")) ∷
     ("message" , V.string (toList "The defeat edge was committed before propagation requested a user decision. The edge remains stored; no posterior update was published. Open the user dialog using the repeated values. Do not report this operation as complete or claim that nothing changed.")) ∷ [])

  patternResult : Pattern.Result → V.Value
  patternResult p = object (("pattern" , patternValue (Pattern.Result.patternValue p)) ∷
    ("successes" , V.unsigned (Pattern.Counts.successes counts)) ∷ ("failures" , V.unsigned (Pattern.Counts.failures counts)) ∷
    ("unknown" , V.unsigned (Pattern.Counts.unknowns counts)) ∷
    ("observed_success_probability" , real (Pattern.Result.observedSuccessProbability p)) ∷ originField (Pattern.Result.candidateProvenance p))
    where
    counts = Pattern.Result.observations p
    originField : Maybe Provenance.Provenance → List (String × V.Value)
    originField nothing = []
    originField (just origin) = ("candidate_provenance" , provenance origin) ∷ []

  currentReview : History.CurrentReview → V.Value
  currentReview r = object (("experience_id" , uuid (Experience.Experience.identity (Observation.Snapshot.experience s))) ∷
    ("revision" , V.signed (Observation.Snapshot.revision s)) ∷ ("review_revision" , V.signed (Observation.Snapshot.reviewRevision s)) ∷
    ("reviewed_revision" , V.signed (Observation.Snapshot.reviewedRevision s)) ∷
    ("review" , optional review (History.CurrentReview.applied r)) ∷ [])
    where s = History.CurrentReview.state r

  contextAssessments : List (Context.Key × Evaluation.Result) → Maybe (List V.Value)
  contextAssessments [] = just []
  contextAssessments ((fieldKey , evaluated) ∷ rest) with evaluation evaluated | contextAssessments rest
  ... | just s | just later = just (object (("belief_id" , uuid (Context.Key.belief fieldKey)) ∷
    ("scope" , V.string (Context.Key.scope fieldKey)) ∷ ("rubric" , V.string (Context.Key.rubric fieldKey)) ∷ ("scores" , s) ∷ []) ∷ later)
  ... | _ | _ = nothing

  module C = A.C

  argumentCorrection : Validation.Fault → Errors.AgentCorrection.Claim
  argumentCorrection detail = Errors.AgentCorrection.claim
    (Errors.AgentCorrection.item Errors.AgentCorrection.arguments detail
      (toList "The unchanged intended request and the advertised field types and required values.")
      (toList "Correct the indicated field before binding. For already bound work, read operation_outcome and retain the original token and arguments; ask the user before cancelling or reserving corrected work.")) []

  module Numerical = NumericalRead.NumericalOutcome (Application.Environment.databaseSum environment)
  module GroundDiagnostic = GroundingRecovery.Business (Application.Environment.databaseSum environment)
    (Application.Environment.calculator environment) using (Diagnostic; requestFault; preparation; rejectedReport; repeated)
  module DeletionDiagnostic = BeliefDeletion.Business (Application.Environment.databaseSum environment)
    (Application.Environment.calculator environment) using (Diagnostic; requestFault; preparation; rejectedReport; repeated)
  module IndependentDiagnostic = IndependentIntent.Business (Application.Environment.format environment) (Application.Environment.databaseSum environment)
    (Application.Environment.calculator environment) using (Diagnostic; requestFault; preparation)
  module DecayDiagnostic = DecayRecovery.Business (Application.Environment.databaseSum environment)
    using (Diagnostic; requestFault; invalidStoredInputs)

  observedProblem : Text → Projection
  observedProblem description = decision (argumentCorrection
    (Validation.problem [] Validation.unsupportedCombination description))

  preparationProblem : Numerical.PreparationIssue → Projection
  preparationProblem (Numerical.missingSeed identity) = decision (argumentCorrection
    (Validation.problem (Validation.key "id" ∷ []) Validation.missingReference
      (toList "The requested numerical seed belief is not stored: " ++ Formatting.uuidText format identity ++
       toList ". Inspect the stored beliefs and select the intended existing identity; ask the user if it is unknown.")))
  preparationProblem (Numerical.invalidIntervention value) = decision (argumentCorrection
    (Validation.problem (Validation.key "value" ∷ []) Validation.invalidNumber
      (toList "The intervention probability is invalid: " ++ toList (Float.show value) ++
       toList ". Supply a finite probability from 0 through 1; do not clamp or guess a replacement.")))
  preparationProblem Numerical.invalidStoredInputs = observedProblem
    (toList "The stored counts or relationships cannot prepare a valid posterior calculation. No complete numerical result was published. Inspect the stored inputs and diagnostics and discuss the repair with the user; do not drop evidence or invent counts.")

  reportProblem : Posterior.CalculationReport → Projection
  reportProblem (Posterior.candidate counts) = observedProblem
    (toList "The calculation's reported counts do not satisfy the complete posterior equations and stored-input requirements: " ++
     numericalCounts counts ++ toList "Keep the original operation and inspect these values; do not publish this candidate or invent an accuracy threshold.")
  reportProblem (Posterior.sweeps history) = observedProblem
    (toList "The calculation's recorded sweeps do not establish a complete valid posterior result: " ++
     numericalHistory history ++ toList "Keep the original operation and inspect this history; do not select an incomplete iterate or invent an accuracy threshold.")

  groundingProblem : GroundDiagnostic.Diagnostic → Projection
  groundingProblem (GroundDiagnostic.requestFault fault) = decision (argumentCorrection fault)
  groundingProblem (GroundDiagnostic.preparation issue) = preparationProblem issue
  groundingProblem (GroundDiagnostic.rejectedReport report) = reportProblem report
  groundingProblem (GroundDiagnostic.repeated counts history) = decision (numericalCorrection counts history)

  deletionProblem : DeletionDiagnostic.Diagnostic → Projection
  deletionProblem (DeletionDiagnostic.requestFault fault) = decision (argumentCorrection fault)
  deletionProblem (DeletionDiagnostic.preparation issue) = preparationProblem issue
  deletionProblem (DeletionDiagnostic.rejectedReport report) = reportProblem report
  deletionProblem (DeletionDiagnostic.repeated counts history) = decision (numericalCorrection counts history)

  independentProblem : IndependentDiagnostic.Diagnostic → Projection
  independentProblem (IndependentDiagnostic.requestFault fault) = decision (argumentCorrection fault)
  independentProblem (IndependentDiagnostic.preparation report) = decision report

  decayProblem : DecayDiagnostic.Diagnostic → Projection
  decayProblem (DecayDiagnostic.requestFault fault) = decision (argumentCorrection fault)
  decayProblem DecayDiagnostic.invalidStoredInputs = observedProblem
    (toList "The stored counts or decay accounting are invalid for this publication. Keep the original token and inspect the stored baselines and diagnostics before discussing a repair; do not invent counts or replace the original decay settings.")

  recordProblem : Recording.Failure → Projection
  recordProblem (Recording.invalid fault) = decision (argumentCorrection fault)
  recordProblem Recording.invalidExpected = decision (argumentCorrection (Validation.fault
    (Validation.key "expected_revision" ∷ []) Validation.invalidNumber
    "The expected source revision is invalid. Read get_experience and retain the original incident ID; supply the actual revision rather than guessing."))
  recordProblem Recording.staleRevision = decision (argumentCorrection (Validation.fault
    (Validation.key "expected_revision" ∷ []) Validation.staleRevision
    "The source revision changed. Read get_experience and experience_history with the same incident ID, compare the stored source with the intended correction, and ask the user if its meaning is uncertain. Do not overwrite newer work blindly."))
  recordProblem Recording.missingPattern = decision (argumentCorrection (Validation.fault
    (Validation.key "pattern_id" ∷ []) Validation.missingReference
    "The referenced pattern is not stored. Inspect list_patterns and use the intended stored pattern, or ask the user if it is unknown; do not invent an ID."))
  recordProblem Recording.foreignPattern = decision (argumentCorrection (Validation.fault
    (Validation.key "pattern_id" ∷ []) Validation.wrongIdentity
    "The referenced pattern belongs to a different project. Read the original source and pattern project before correcting the request; do not move records to bypass ownership."))
  recordProblem Recording.incoherentSnapshot = observedProblem
    (toList "The stored source and its revision history do not describe a coherent snapshot. Keep the original token and incident ID and inspect get_experience, experience_history and private diagnostics before repairing those records.")
  recordProblem Recording.numericFailure = observedProblem
    (toList "The changed source could not produce a valid complete numerical publication. Keep its original request and inspect the stored counts and relationships before discussing a repair with the user.")
  recordProblem (Recording.numericalDecision counts history) = decision (numericalCorrection counts history)

  reviewProblem : Reviewing.Failure → Projection
  reviewProblem (Reviewing.invalid fault) = decision (argumentCorrection fault)
  reviewProblem Reviewing.invalidExpected = decision (argumentCorrection (Validation.fault
    (Validation.key "expected_review_revision" ∷ []) Validation.invalidNumber
    "The expected review revision is invalid. Read the current review for the same experience and use its actual revision; do not invent a number."))
  reviewProblem Reviewing.missingExperience = decision (argumentCorrection (Validation.fault
    (Validation.key "experience_id" ∷ []) Validation.missingReference
    "This experience is not stored. Read the intended experience and its source records before reviewing; ask the user if the incident is unknown."))
  reviewProblem Reviewing.incoherentSnapshot = observedProblem
    (toList "The stored experience and review history do not describe a coherent snapshot. Keep the original token and inspect their current revisions and private diagnostics before repairing those records.")
  reviewProblem (Reviewing.numeric ReviewNumerical.foreignTarget) = observedProblem
    (toList "The review's numerical targets include a belief outside its project. Inspect the original review and target projects; do not broaden project scope to bypass this check.")
  reviewProblem (Reviewing.numeric ReviewNumerical.invalidInput) = observedProblem
    (toList "The review's stored numerical inputs are invalid. Inspect those counts and relationships before repairing the original operation.")
  reviewProblem (Reviewing.numeric ReviewNumerical.invalidWrite) = observedProblem
    (toList "The review's proposed numerical write is invalid. No complete posterior result was published; inspect the calculation and stored inputs before retrying.")
  reviewProblem (Reviewing.numeric (ReviewNumerical.numericalDecision counts history)) = decision (numericalCorrection counts history)

  operationProblem : Operations.Failure → Projection
  operationProblem (Operations.preparationFailure report) = decision report
  operationProblem (Operations.externalFailure description) = observedProblem
    (toList "The external operation could not complete: " ++ description ++
     toList " Read the original outcome before retrying; ask the user if a prerequisite or request must change.")
  operationProblem (Operations.allocationFailure fault) = decision (argumentCorrection fault)
  operationProblem failure with Operations.requestCorrection failure
  ... | just report = decision report
  operationProblem (Operations.recordFailure failure) | nothing = recordProblem failure
  operationProblem (Operations.reviewFailure failure) | nothing = reviewProblem failure

  sourceProblem : Validation.Fault ⊎ (Recording.Failure ⊎ (Operations.Failure ⊎ GroundDiagnostic.Diagnostic)) → Projection
  sourceProblem (inj₁ fault) = decision (argumentCorrection fault)
  sourceProblem (inj₂ (inj₁ failure)) = recordProblem failure
  sourceProblem (inj₂ (inj₂ (inj₁ failure))) = operationProblem failure
  sourceProblem (inj₂ (inj₂ (inj₂ failure))) = groundingProblem failure

  reviewPublicationProblem : Validation.Fault ⊎ (Operations.Failure ⊎ GroundDiagnostic.Diagnostic) → Projection
  reviewPublicationProblem (inj₁ fault) = decision (argumentCorrection fault)
  reviewPublicationProblem (inj₂ (inj₁ failure)) = operationProblem failure
  reviewPublicationProblem (inj₂ (inj₂ failure)) = groundingProblem failure

  originalRequest : Store.BindingRow → V.Value
  originalRequest binding = object
    (("operation_token" , uuid (Store.BindingRow.token binding)) ∷
     ("bound_at" , timestamp (Store.BindingRow.boundAt binding)) ∷
     ("request" , object (("operation" , V.string (Store.BindingRow.operation binding)) ∷
       ("arguments" , Store.BindingRow.arguments binding) ∷
       ("settings" , Store.BindingRow.settings binding) ∷ [])) ∷ [])

  savedReply : Store.SavedReplyRow → V.Value
  savedReply row = object (("operation_token" , uuid (Store.SavedReplyRow.token row)) ∷
    ("step" , V.string (Store.SavedReplyRow.step row)) ∷
    ("reply" , Store.SavedReplyRow.reply row) ∷ [])

  nextStep : Controls.Plan.Step → V.Value
  nextStep step = object (("site" , V.string (Controls.Plan.Step.site step)) ∷
    ("key" , optional V.string (Controls.Plan.Step.key step)) ∷
    ("id" , V.string (Controls.Plan.Step.id step)) ∷ [])

  pendingReadback : ℕ → Store.BindingRow → Projection
  pendingReadback token binding = success (object (("operation_token" , uuid token) ∷
    ("status" , V.string (toList "pending")) ∷ ("original_request" , originalRequest binding) ∷
    ("suggested_fix" , V.string (toList "Repeat the original write with the same token and arguments. Discuss an unresolved prerequisite with the user; do not infer completion from a saved step.")) ∷ []))

  savedRecordsProblem : Store.BindingRow → Validation.Fault → Projection
  savedRecordsProblem binding detail = decision (Errors.AgentCorrection.claim
    (Errors.AgentCorrection.item Errors.AgentCorrection.arguments detail
      (toList "The original immutable request, its complete saved plan and ordered answers: " ++
       Library.Contract.lossyUTF8 library (Library.Contract.compactJSON library (originalRequest binding)))
      (toList "Keep the original token, request, plan and saved answers. Explain the inconsistency to the user and reconcile those records before more work. Do not invent a completed result, replace the plan or repeat committed changes.")) [])
    where library = Application.Environment.library environment

  journalProblem : Store.BindingRow → C.Control.Read.Problem → Projection
  journalProblem binding (C.Control.Read.malformedPlan fault) = savedRecordsProblem binding fault
  journalProblem binding C.Control.Read.differentOperation = savedRecordsProblem binding
    (Validation.fault (Validation.key "operation_token" ∷ []) Validation.wrongIdentity
      "The saved plan belongs to a different operation than the original bound request.")
  journalProblem binding C.Control.Read.invalidRegisteredPlan = savedRecordsProblem binding
    (Validation.fault (Validation.key "plan" ∷ []) Validation.wrongIdentity
      "The unfinished saved plan does not match the registered operation boundaries.")
  journalProblem binding C.Control.Read.undeclaredOrNonprefixAnswers = savedRecordsProblem binding
    (Validation.fault (Validation.key "saved_replies" ∷ []) Validation.malformedInput
      "The saved answers contain an undeclared step, a gap, an extra answer or a duplicate; they are not one complete ordered prefix of the original plan.")
  journalProblem binding C.Control.Read.prematureCompletion = savedRecordsProblem binding
    (Validation.fault (Validation.key "saved_replies" ∷ []) Validation.malformedInput
      "A final operation answer was stored before every step of the original plan was complete.")

  readback : A.Result → ℕ → C.Control.Read.Result → Projection
  readback original token C.Control.Read.unknownToken = decision (argumentCorrection
    (Validation.fault (Validation.key "operation_token" ∷ []) Validation.missingReference
      "This token has no reservation in the selected database. Repeat reserve_operation with the original request_key if its reply was lost, and check the selected database. Do not invent a replacement token."))
  readback original token C.Control.Read.reserved = success (object
    (("operation_token" , uuid token) ∷ ("status" , V.string (toList "reserved")) ∷
     ("suggested_fix" , V.string (toList "Call the intended write with this token and its complete arguments; retain those exact arguments on retries.")) ∷ []))
  readback original token (C.Control.Read.awaitingPlan binding) = pendingReadback token binding
  readback original token (C.Control.Read.awaitingCompletion binding) = pendingReadback token binding
  readback original token (C.Control.Read.pending binding step replies) = success (object
    (("operation_token" , uuid token) ∷ ("status" , V.string (toList "pending")) ∷
     ("original_request" , originalRequest binding) ∷ ("next_step" , nextStep step) ∷
     ("saved_replies" , V.array (map savedReply replies)) ∷
     ("suggested_fix" , V.string (toList "Repeat the original write with unchanged token and arguments to resume its saved next step. Ask the user about unresolved prerequisites; do not skip steps or cancel automatically.")) ∷ []))
  readback original token (C.Control.Read.completed binding value) = success (object
    (("operation_token" , uuid token) ∷ ("status" , V.string (toList "completed")) ∷
     ("original_request" , originalRequest binding) ∷ ("result" , value) ∷ []))
  readback original token (C.Control.Read.needsRecovery binding) = savedRecordsProblem binding
    (Validation.fault (Validation.key "saved_replies" ∷ []) Validation.malformedInput
      "The saved operation records require reconciliation before this work can resume.")
  readback original token (C.Control.Read.inconsistent binding problem) = journalProblem binding problem
  readback original token (C.Control.Read.cancelled cancellation binding replies) = success (object
    (("operation_token" , uuid token) ∷ ("status" , V.string (toList "cancelled")) ∷
     ("cancellation" , object (("operation_token" , uuid (Store.CancellationRow.token cancellation)) ∷
       ("cancelled_at" , timestamp (Store.CancellationRow.cancelledAt cancellation)) ∷ [])) ∷
     ("original_request" , optional originalRequest binding) ∷ ("saved_replies" , V.array (map savedReply replies)) ∷
     ("worker_cleanup" , V.string (toList "not_confirmed_by_this_receipt")) ∷
     ("message" , V.string (toList "Cancellation is durable and further publication is blocked. Committed changes and saved answers remain. This database receipt does not establish that every worker has stopped.")) ∷ []))

  finalReadback : A.Result → ℕ → Store.World → Projection
  finalReadback original token final = readback original token (C.Control.Read.answer token final)

  stepProjection : ∀ {Diagnostic : Set} → A.Result → (Diagnostic → Projection) →
    ℕ → Store.World → Step.Result Diagnostic → Projection
  stepProjection original diagnostic token final (Step.done value) = finalReadback original token final
  stepProjection original diagnostic token final (Step.needsInput detail) = diagnostic detail
  stepProjection original diagnostic token final Step.needsRecovery = finalReadback original token final
  stepProjection original diagnostic token final (Step.cancelled _) = finalReadback original token final

  faultStep : A.Result → ℕ → Store.World → Step.Result Validation.Fault → Projection
  faultStep original = stepProjection original (λ fault → decision (argumentCorrection fault))

  storedDefeat : ℕ → ℕ → List Edges.Edge → Maybe Mutation.CommittedEdge
  storedDefeat from to [] = nothing
  storedDefeat from to (edge ∷ rest) with from ≟ Edges.Edge.from edge | to ≟ Edges.Edge.to edge | Edges.Edge.relation edge
  ... | yes _ | yes _ | Relations.defeats = just (Mutation.committedEdge from to (Edges.Edge.weight edge))
  ... | _ | _ | _ = storedDefeat from to rest

  defeatProblem : A.Result → Public.Request → ℕ → Store.World → GroundDiagnostic.Diagnostic → Projection
  defeatProblem original expected token final detail with Store.lookupSaved final token (DefeatRecovery.firstKey token)
  ... | nothing = groundingProblem detail
  ... | just _ with expected
  ... | Public.mutation (Mutation.edge from to Relations.defeats weight) with storedDefeat from to (Stored.edges final) | groundingProblem detail
  ... | just edge | decision report = partialDecision edge report
  ... | _ | _ = failure original
  defeatProblem original expected token final detail | just _ | _ = failure original

  defeatStep : A.Result → Public.Request → ℕ → Store.World → Step.Result GroundDiagnostic.Diagnostic → Projection
  defeatStep original expected token final (Step.needsInput detail) = defeatProblem original expected token final detail
  defeatStep original expected token final reply = stepProjection original groundingProblem token final reply

  retrievalResponse : Search.Response → V.Value
  retrievalResponse (Search.plain result) = object
    (("beliefs" , V.array (map belief (Retrieval.Report.beliefs result))) ∷
     ("retrieval" , Retrieval.coverageValue (Retrieval.Report.retrieval result)) ∷ [])
  retrievalResponse (Search.grounded coverage beliefs) = object
    (("beliefs" , V.array (map grounded beliefs)) ∷
     ("retrieval" , Retrieval.coverageValue coverage) ∷ [])

  contextOutput : A.Result → ContextProtocol.Output → Projection
  contextOutput original result with contextAssessments (Context.Assessments.values (ContextProtocol.Output.assessments result))
  ... | nothing = observedProblem
    (toList "The selected learning context contains an invalid stored assessment. Inspect its source contributions and history before repairing the affected scores; do not return incomplete assessments as a successful context.")
  ... | just assessments = success (object (("beliefs" , V.array (map belief (ContextProtocol.Output.beliefs result))) ∷
    ("patterns" , V.array (map patternResult (ContextProtocol.Output.patterns result))) ∷ ("assessments" , V.array assessments) ∷
    ("assessments_truncated" , V.boolean (Context.Assessments.truncated (ContextProtocol.Output.assessments result))) ∷
    ("retrieval" , Retrieval.coverageValue (ContextProtocol.Output.retrieval result)) ∷ []))

  payload : A.Result → (kind : C.Kind) → C.Input kind → C.Result kind → Store.World → Projection
  payload original (C.basic request) input value final = success value
  payload original (C.experiences request) input value final = success value
  payload original (C.assessments request) input (C.Assessments.scoreResult (Assessment.invalidTarget detail)) final = decision (argumentCorrection detail)
  payload original (C.assessments request) input (C.Assessments.historyResult Assessment.missingProject) final = decision (argumentCorrection
    (Validation.fault (Validation.key "project" ∷ []) Validation.missingField
      "Assessment history requires the intended project. Supply that project from the task context or ask the user; do not guess an unrelated project."))
  payload original (C.assessments request) input (C.Assessments.historyResult Assessment.invalidStoredHistory) final = observedProblem
    (toList "The stored assessment history cannot be joined into a valid response. Keep the selected project and belief and inspect their source/review revisions and diagnostics before repairing the history.")
  payload original (C.assessments request) input (C.Assessments.explanationResult Explain.beliefMissing) final = decision (argumentCorrection
    (Validation.fault (Validation.key "id" ∷ []) Validation.missingReference
      "The requested belief is not stored. Inspect list_beliefs or query_relevant_beliefs for the intended project and select the existing identity; ask the user if it is unknown."))
  payload original (C.assessments request) input (C.Assessments.explanationResult Explain.invalidStoredProvenance) final = observedProblem
    (toList "The stored belief provenance cannot be decoded as valid provenance. Inspect that belief's source and private diagnostic before repairing it; do not invent a replacement provenance record.")
  payload original (C.assessments request) input reply final with C.Assessments.successfulWire reply
  ... | just value = success value
  ... | nothing = observedProblem
    (toList "The selected assessment contains an invalid stored numerical value or score total. Inspect its source contributions and history and discuss the repair with the user; do not clamp or omit contributions to produce a score.")
  payload original (C.intervention request) input (C.Intervention.N.calculated writes) final = success
    (V.array (map (λ { (identity , probability) → object (("id" , uuid identity) ∷ ("projected_probability" , real probability) ∷ []) }) writes))
  payload original (C.intervention request) input (C.Intervention.N.needsDecision repeated visited) final = decision (numericalCorrection repeated visited)
  payload original (C.intervention request) input (C.Intervention.N.unavailable issue) final = preparationProblem issue
  payload original (C.intervention request) input (C.Intervention.N.invalidCalculation counts) final = observedProblem
    (toList "The intervention calculation reached invalid stored-count values: " ++ numericalCounts counts ++
     toList " No complete result is available. Inspect the original seed, relationships and counts before correcting the request or stored inputs.")
  payload original (C.intervention request) input (C.Intervention.N.rejectedReport report) final = reportProblem report
  payload original (C.retrieval request) input (C.Retrieval.completed configuration actual snapshot receipt response) final = success (retrievalResponse response)
  payload original (C.context request) input (C.LearningContext.needsInput actual report) final = decision report
  payload original (C.context request) input (C.LearningContext.contextResult source (C.LearningContext.Assembly.response result)) final = contextOutput original result
  payload original (C.context request) input (C.LearningContext.contextResult source C.LearningContext.Assembly.invalidAssessment) final = observedProblem
    (toList "The selected learning context contains an invalid stored assessment. Inspect its source contributions and history before repairing it; do not silently omit the invalid assessment.")
  payload original (C.documentQuery request) input value final with C.DocumentQuery.value value
  ... | DocumentQuery.found hits = success (V.array (map documentHit hits))
  ... | DocumentQuery.preparationRequired issue = decision (Errors.AgentCorrection.claim
    (Errors.AgentCorrection.embeddingQueryItem (DocumentQuery.preparationCode issue) (DocumentQuery.preparationDescription issue)) [])
  ... | DocumentQuery.failed reason = observedProblem
    (toList "The document query could not complete: " ++ reason ++
     toList " Inspect its diagnostic and restore the missing database or document prerequisite before retrying the original query.")
  payload original (C.projectRemoval project) token value final = finalReadback original token final
  payload original (C.correction fault) input reply final = decision (argumentCorrection reply)
  payload original (C.patternWrite expected) token (C.PatternGuard.needsInput detail) final = decision (argumentCorrection detail)
  payload original (C.patternWrite expected) token (C.PatternGuard.executed reply) final = faultStep original token final reply
  payload original (C.independentWrite expected) token (C.IndependentGuard.needsInput detail) final = decision (argumentCorrection detail)
  payload original (C.independentWrite expected) token (C.IndependentGuard.executed reply) final =
    stepProjection original independentProblem token final (C.IndependentPublic.Result.value reply)
  payload original (C.patternRemoval expected) token (C.PatternRemovalGuard.needsInput detail) final = decision (argumentCorrection detail)
  payload original (C.patternRemoval expected) token (C.PatternRemovalGuard.executed reply) final = faultStep original token final reply
  payload original (C.beliefRemoval expected) token (C.BeliefRemovalGuard.needsInput detail) final = decision (argumentCorrection detail)
  payload original (C.beliefRemoval expected) token (C.BeliefRemovalGuard.executed reply) final = stepProjection original deletionProblem token final reply
  payload original (C.relationship relation expected) token (C.RelationshipGuard.needsInput detail) final = decision (argumentCorrection detail)
  payload original (C.relationship relation expected) token (C.RelationshipGuard.executed reply) final = faultStep original token final reply
  payload original (C.grounding relation expected) token (C.GroundingGuard.needsInput detail) final = decision (argumentCorrection detail)
  payload original (C.grounding relation expected) token (C.GroundingGuard.executed reply) final = stepProjection original groundingProblem token final reply
  payload original (C.propagation expected) token (C.PropagationGuard.needsInput detail) final = decision (argumentCorrection detail)
  payload original (C.propagation expected) token (C.PropagationGuard.executed reply) final = stepProjection original groundingProblem token final reply
  payload original (C.decay expected) token (C.DecayGuard.needsInput detail) final = decision (argumentCorrection detail)
  payload original (C.decay expected) token (C.DecayGuard.executed reply) final = stepProjection original decayProblem token final reply
  payload original (C.documentRemoval expected) token (C.ClearGuard.needsInput detail) final = decision (argumentCorrection detail)
  payload original (C.documentRemoval expected) token (C.ClearGuard.executed reply) final = stepProjection original groundingProblem token final reply
  payload original (C.defeat expected) token reply final = defeatStep original expected token final reply
  payload original (C.sweep expected) token reply final = stepProjection original deletionProblem token final reply
  payload original (C.sourceWrite expected) token reply final = stepProjection original sourceProblem token final reply
  payload original (C.reviewWrite expected) token reply final = stepProjection original reviewPublicationProblem token final reply
  payload original (C.documentLoading expected) token (C.DocumentEntry.inspected outcome) final = readback original token outcome
  payload original (C.documentLoading expected) token result@(C.DocumentEntry.executed _) final =
    stepProjection original groundingProblem token final (C.DocumentEntry.normalized result)
  payload original (C.control Controls.reserve requestKey) input (C.Control.Reserve.reserved row) final = success (object
    (("status" , V.string (toList "reserved")) ∷ ("operation_token" , uuid (Store.ReservationRow.token row)) ∷
     ("reserved_at" , timestamp (Store.ReservationRow.reservedAt row)) ∷
     ("request_key" , V.string (Controls.RequestKey.text requestKey)) ∷
     ("message" , V.string (toList "No business work has run. Keep this key and token for the intended write, including after a lost reply.")) ∷ []))
  payload original (C.control Controls.reserve requestKey) input (C.Control.Reserve.needsRecovery token) final = decision (argumentCorrection
    (Validation.problem (Validation.key "request_key" ∷ []) Validation.malformedInput
      (toList "The saved request key points to a missing reservation for token " ++ Formatting.uuidText format token ++
       toList ". Keep the original request_key and selected database; ask the user to reconcile the saved reservation instead of inventing a replacement action.")))
  payload original (C.control Controls.readOutcome token) input reply final = readback original token reply
  payload original (C.control Controls.cancel token) input reply final = finalReadback original token final

  writePayload : A.Result → C.Creating.Request → A.Writes.Response → Store.World → Projection
  writePayload original requested (A.Writes.needsInput detail) final = decision (argumentCorrection detail)
  writePayload original requested (A.Writes.returned outcome) final
    with C.Creating.decode requested
  ... | inj₁ detail = decision (argumentCorrection detail)
  ... | inj₂ call = readback original
    (C.Creating.Call.token call) outcome
  writePayload original requested (A.Writes.executed scope reply) final =
    payload original (A.Writes.bodyKind scope) (A.Writes.bodyInput scope) reply final

  routePayload : A.Result → (call : A.Call) → A.RouteValue (A.route call) → Store.World → Projection
  routePayload original call reply final with A.route call
  ... | A.plainRoute selected = payload original (C.Choice.kind selected) (C.Choice.input selected) reply final
  ... | A.registeredRoute requested = writePayload original requested reply final

  -- A non-successful completed script retains its actual typed diagnostic.
  -- Stopping before a returned reply never manufactures a successful value.
  retryProjection : (original : A.Result) → Projection
  retryProjection original@(A.terminalResult call initial terminal) with
    A.Checked.Active.remaining call (A.Checked.Terminal.active call terminal)
  ... | A.O.E.done reply = routePayload original call reply
    (A.Checked.History.current call (A.Checked.Active.evidence call (A.Checked.Terminal.active call terminal)))
  ... | A.O.E.ask effect continuation = failure original

  project : A.Result → Projection
  project original@(A.terminalResult call initial terminal) with A.Checked.Terminal.disposition call terminal
  ... | A.Checked.done reply exposed successful = routePayload original call reply
    (A.Checked.History.current call (A.Checked.Active.evidence call (A.Checked.Terminal.active call terminal)))
  ... | A.Checked.correction certified = retryProjection original
  ... | A.Checked.retry = retryProjection original
  ... | A.Checked.fatal violation = failure original

module Encode (environment : Application.Environment) (format : Encoding.Formatting) where
  module A = Application.Run environment
  module P = Project environment format

  decisionValue : A.Result → Errors.AgentCorrection.Claim → V.Value
  decisionValue (A.terminalResult call initial terminal) report with A.Checked.Terminal.disposition call terminal
  ... | A.Checked.correction certified = Errors.AgentCorrection.emitCorrection
    (Errors.AgentCorrection.certified report (Errors.AgentCorrection.Certified.unchanged certified))
  ... | _ = object (("status" , V.string (toList "needs_recovery")) ∷
    ("issues" , Errors.AgentCorrection.issues report) ∷
    ("next_action" , V.string (toList "read_operation_outcome_or_ask_user")) ∷
    ("message" , V.string (toList "The original operation returned this diagnostic, but this receipt does not establish that business data is unchanged. Read its original outcome and preserve committed steps before discussing the correction with the user.")) ∷ [])

  result : A.Result → V.Value
  result original with P.project original
  ... | P.success value = value
  ... | P.decision report = decisionValue original report
  ... | P.partialDecision edge report = P.partialValue edge report
  ... | P.failure cause = object (("status" , V.string (toList "needs_recovery")) ∷
    ("message" , V.string (toList "The requested operation has no certified successful result. Keep its original token, request and saved answers; read operation_outcome and the complete diagnostic before retrying or asking the user to resolve the prerequisite.")) ∷ [])
