{-# OPTIONS --safe #-}
-- Exhaustive result classification and JSON projection. Failed/uncertain
-- operations remain errors even if an earlier component committed. The error
-- retains its complete typed cause for the host's diagnostic formatter.
module Mimir.ApplicationOutput where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.String using (String; toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
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
import Mimir.ReviewNumericalPublication as Numerical
import Mimir.PosteriorComputation as Posterior
import Mimir.ApplicationStore as Store
import Mimir.PublicOperationCatalogue as Catalogue
import Mimir.RecoverableStoreStep as Step
import Mimir.OperationControls as Controls
import Mimir.PublicRetrievalRecovery as Search
import Mimir.Recovery as Recovery
import Mimir.FaultWire as FaultWire
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

  originalRequest : Store.BindingRow → V.Value
  originalRequest binding = object
    (("operation_token" , uuid (Store.BindingRow.token binding)) ∷
     ("bound_at" , timestamp (Store.BindingRow.boundAt binding)) ∷
     ("request" , object (("operation" , V.string (Store.BindingRow.operation binding)) ∷
       ("arguments" , Store.BindingRow.arguments binding) ∷
       ("settings" , Store.BindingRow.settings binding) ∷ [])) ∷ [])

  savedReply : Store.SavedReplyRow → V.Value
  savedReply row = object (("step_id" , V.string (Store.SavedReplyRow.step row)) ∷
    ("reply" , Store.SavedReplyRow.reply row) ∷ [])

  nextStep : Controls.Plan.Step → V.Value
  nextStep step = object (("site" , V.string (Controls.Plan.Step.site step)) ∷
    ("key" , optional V.string (Controls.Plan.Step.key step)) ∷
    ("id" , V.string (Controls.Plan.Step.id step)) ∷ [])

  readback : A.Result → ℕ → C.Control.Read.Result → Projection
  readback original token C.Control.Read.unknownToken = decision (argumentCorrection
    (Validation.fault (Validation.key "operation_token" ∷ []) Validation.missingReference
      "This token has no reservation in the selected database. Repeat reserve_operation with the original request_key if its reply was lost, and check the selected database. Do not invent a replacement token."))
  readback original token C.Control.Read.reserved = success (object
    (("operation_token" , uuid token) ∷ ("status" , V.string (toList "reserved")) ∷
     ("suggested_fix" , V.string (toList "Call the intended write with this token and its complete arguments; retain those exact arguments on retries.")) ∷ []))
  readback original token (C.Control.Read.awaitingPlan binding) = pending binding
    where pending : Store.BindingRow → Projection
          pending binding = success (object (("operation_token" , uuid token) ∷
            ("status" , V.string (toList "pending")) ∷ ("original_request" , originalRequest binding) ∷
            ("suggested_fix" , V.string (toList "Repeat the original write with the same token and arguments. Discuss an unresolved prerequisite with the user; do not infer completion from a saved step.")) ∷ []))
  readback original token (C.Control.Read.awaitingCompletion binding) = readback original token (C.Control.Read.awaitingPlan binding)
  readback original token (C.Control.Read.pending binding step replies) = success (object
    (("operation_token" , uuid token) ∷ ("status" , V.string (toList "pending")) ∷
     ("original_request" , originalRequest binding) ∷ ("next_step" , nextStep step) ∷
     ("saved_replies" , V.array (map savedReply replies)) ∷
     ("suggested_fix" , V.string (toList "Repeat the original write with unchanged token and arguments to resume its saved next step. Ask the user about unresolved prerequisites; do not skip steps or cancel automatically.")) ∷ []))
  readback original token (C.Control.Read.completed binding value) = success (object
    (("operation_token" , uuid token) ∷ ("status" , V.string (toList "completed")) ∷
     ("original_request" , originalRequest binding) ∷ ("result" , value) ∷ []))
  readback original token (C.Control.Read.needsRecovery binding) = failure original
  readback original token (C.Control.Read.inconsistent binding problem) = failure original
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
  stepProjection original diagnostic token final Step.needsRecovery = failure original
  stepProjection original diagnostic token final (Step.cancelled _) = finalReadback original token final

  faultStep : A.Result → ℕ → Store.World → Step.Result Validation.Fault → Projection
  faultStep original = stepProjection original (λ fault → decision (argumentCorrection fault))

  retrievalResponse : Search.Response → V.Value
  retrievalResponse (Search.plain result) = object
    (("beliefs" , V.array (map belief (Retrieval.Report.beliefs result))) ∷
     ("retrieval" , Retrieval.coverageValue (Retrieval.Report.retrieval result)) ∷ [])
  retrievalResponse (Search.grounded coverage beliefs) = object
    (("beliefs" , V.array (map grounded beliefs)) ∷
     ("retrieval" , Retrieval.coverageValue coverage) ∷ [])

  contextOutput : A.Result → ContextProtocol.Output → Projection
  contextOutput original result with contextAssessments (Context.Assessments.values (ContextProtocol.Output.assessments result))
  ... | nothing = failure original
  ... | just assessments = success (object (("beliefs" , V.array (map belief (ContextProtocol.Output.beliefs result))) ∷
    ("patterns" , V.array (map patternResult (ContextProtocol.Output.patterns result))) ∷ ("assessments" , V.array assessments) ∷
    ("assessments_truncated" , V.boolean (Context.Assessments.truncated (ContextProtocol.Output.assessments result))) ∷
    ("retrieval" , Retrieval.coverageValue (ContextProtocol.Output.retrieval result)) ∷ []))

  payload : A.Result → (kind : C.Kind) → C.Input kind → C.Result kind → Store.World → Projection
  payload original (C.basic request) input value final = success value
  payload original (C.experiences request) input value final = success value
  payload original (C.assessments request) input reply final with C.Assessments.successfulWire reply
  ... | just value = success value
  ... | nothing = failure original
  payload original (C.intervention request) input (C.Intervention.N.calculated writes) final = success
    (V.array (map (λ { (identity , probability) → object (("id" , uuid identity) ∷ ("projected_probability" , real probability) ∷ []) }) writes))
  payload original (C.intervention request) input (C.Intervention.N.needsDecision repeated visited) final = decision (numericalCorrection repeated visited)
  payload original (C.intervention request) input reply final = failure original
  payload original (C.retrieval request) input (C.Retrieval.completed configuration actual snapshot receipt response) final = success (retrievalResponse response)
  payload original (C.context request) input (C.LearningContext.needsInput actual report) final = decision report
  payload original (C.context request) input (C.LearningContext.contextResult source (C.LearningContext.Assembly.response result)) final = contextOutput original result
  payload original (C.context request) input (C.LearningContext.contextResult source C.LearningContext.Assembly.invalidAssessment) final = failure original
  payload original (C.documentQuery request) input value final with C.DocumentQuery.value value
  ... | DocumentQuery.found hits = success (V.array (map documentHit hits))
  ... | DocumentQuery.preparationRequired issue = decision (Errors.AgentCorrection.claim
    (Errors.AgentCorrection.embeddingQueryItem (DocumentQuery.preparationCode issue) (DocumentQuery.preparationDescription issue)) [])
  ... | DocumentQuery.failed reason = failure original
  payload original (C.projectRemoval project) token value final = finalReadback original token final
  payload original (C.correction fault) input reply final = decision (argumentCorrection reply)
  payload original (C.patternWrite expected) token (C.PatternGuard.needsInput detail) final = decision (argumentCorrection detail)
  payload original (C.patternWrite expected) token (C.PatternGuard.executed reply) final = faultStep original token final reply
  payload original (C.independentWrite expected) token (C.IndependentGuard.needsInput detail) final = decision (argumentCorrection detail)
  payload original (C.independentWrite expected) token (C.IndependentGuard.executed reply) final =
    stepProjection original (λ _ → failure original) token final (C.IndependentPublic.Result.value reply)
  payload original (C.patternRemoval expected) token (C.PatternRemovalGuard.needsInput detail) final = decision (argumentCorrection detail)
  payload original (C.patternRemoval expected) token (C.PatternRemovalGuard.executed reply) final = faultStep original token final reply
  payload original (C.beliefRemoval expected) token (C.BeliefRemovalGuard.needsInput detail) final = decision (argumentCorrection detail)
  payload original (C.beliefRemoval expected) token (C.BeliefRemovalGuard.executed reply) final = stepProjection original (λ _ → failure original) token final reply
  payload original (C.relationship relation expected) token (C.RelationshipGuard.needsInput detail) final = decision (argumentCorrection detail)
  payload original (C.relationship relation expected) token (C.RelationshipGuard.executed reply) final = faultStep original token final reply
  payload original (C.grounding relation expected) token (C.GroundingGuard.needsInput detail) final = decision (argumentCorrection detail)
  payload original (C.grounding relation expected) token (C.GroundingGuard.executed reply) final = stepProjection original (λ _ → failure original) token final reply
  payload original (C.propagation expected) token (C.PropagationGuard.needsInput detail) final = decision (argumentCorrection detail)
  payload original (C.propagation expected) token (C.PropagationGuard.executed reply) final = stepProjection original (λ _ → failure original) token final reply
  payload original (C.decay expected) token (C.DecayGuard.needsInput detail) final = decision (argumentCorrection detail)
  payload original (C.decay expected) token (C.DecayGuard.executed reply) final = stepProjection original (λ _ → failure original) token final reply
  payload original (C.documentRemoval expected) token (C.ClearGuard.needsInput detail) final = decision (argumentCorrection detail)
  payload original (C.documentRemoval expected) token (C.ClearGuard.executed reply) final = stepProjection original (λ _ → failure original) token final reply
  payload original (C.defeat expected) token reply final = stepProjection original (λ _ → failure original) token final reply
  payload original (C.sweep expected) token reply final = stepProjection original (λ _ → failure original) token final reply
  payload original (C.sourceWrite expected) token reply final = stepProjection original (λ _ → failure original) token final reply
  payload original (C.reviewWrite expected) token reply final = stepProjection original (λ _ → failure original) token final reply
  payload original (C.documentLoading expected) token (C.DocumentEntry.inspected outcome) final = readback original token outcome
  payload original (C.documentLoading expected) token (C.DocumentEntry.executed result) final =
    stepProjection original (λ _ → failure original) token final (C.DocumentEntry.Body.Result.value result)
  payload original (C.control Controls.reserve requestKey) input (C.Control.Reserve.reserved row) final = success (object
    (("status" , V.string (toList "reserved")) ∷ ("operation_token" , uuid (Store.ReservationRow.token row)) ∷
     ("reserved_at" , timestamp (Store.ReservationRow.reservedAt row)) ∷
     ("request_key" , V.string (Controls.RequestKey.text requestKey)) ∷
     ("message" , V.string (toList "No business work has run. Keep this key and token for the intended write, including after a lost reply.")) ∷ []))
  payload original (C.control Controls.reserve requestKey) input (C.Control.Reserve.needsRecovery token) final = failure original
  payload original (C.control Controls.readOutcome token) input reply final = readback original token reply
  payload original (C.control Controls.cancel token) input reply final = finalReadback original token final

  -- A non-successful completed script retains its actual typed diagnostic.
  -- Stopping before a returned reply never manufactures a successful value.
  retryProjection : (original : A.Result) → Projection
  retryProjection original@(A.terminalResult call initial terminal) with
    A.Checked.Active.remaining call (A.Checked.Terminal.active call terminal)
  ... | A.O.E.done reply = payload original (A.kind call) (A.input call) reply
    (A.Checked.History.current call (A.Checked.Active.evidence call (A.Checked.Terminal.active call terminal)))
  ... | A.O.E.ask effect continuation = failure original

  project : A.Result → Projection
  project original@(A.terminalResult call initial terminal) with A.Checked.Terminal.disposition call terminal
  ... | A.Checked.done reply exposed successful = payload original (A.kind call) (A.input call) reply
    (A.Checked.History.current call (A.Checked.Active.evidence call (A.Checked.Terminal.active call terminal)))
  ... | A.Checked.correction certified = decision (Errors.AgentCorrection.Certified.report certified)
  ... | A.Checked.retry = retryProjection original
  ... | A.Checked.fatal violation = failure original

module Encode (environment : Application.Environment) (format : Encoding.Formatting) where
  module A = Application.Run environment
  module P = Project environment format
  result : A.Result → V.Value
  result original with P.project original
  ... | P.success value = value
  ... | P.decision report = object (("status" , V.string (toList "needs_input")) ∷
    ("issues" , Errors.AgentCorrection.issues report) ∷
    ("next_action" , V.string (toList "correct_request_or_ask_user")) ∷ [])
  ... | P.partialDecision edge report = P.partialValue edge report
  ... | P.failure cause = object (("status" , V.string (toList "needs_recovery")) ∷
    ("message" , V.string (toList "The requested operation has no certified successful result. Keep its original token, request and saved answers; read operation_outcome and the complete diagnostic before retrying or asking the user to resolve the prerequisite.")) ∷ [])
