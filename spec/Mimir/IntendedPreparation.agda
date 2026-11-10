{-# OPTIONS --safe #-}
-- Pure evaluation of the metadata surrounding a public write. Business
-- evaluation is separate: its world and answer come from the operation's
-- independent intent, never from executing an effect script.
module Mimir.IntendedPreparation where

open import Data.Bool using (true; false)
open import Data.Integer using (ℤ)
import Data.List
import Data.Float.Base as Float
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; pred)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Data.String using (String)
import Data.String
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.ApplicationStore as Store
import Mimir.BeliefDeletionRecovery as BeliefDeletion
import Mimir.GroundingRecovery as Grounding
import Mimir.DocumentQuery as DocumentQuery
import Mimir.InferenceStorageBinding as Numerical
import Mimir.OperationControls as Controls
import Mimir.PublicOperationBinding as Binding
import Mimir.PublicRequest as Public
import Mimir.PublicInput as PublicInput
import Mimir.PublicRetrievalRecovery as PublicRetrieval
import Mimir.RecordDecoding as Record
import Mimir.Recovery as Recovery
import Mimir.RetrievalRanking as Ranking
import Mimir.LearningCandidates as Candidates
import Mimir.ProjectDeletion as Project
import Mimir.StandardLibrary as Library
import Mimir.PublicEncoding as Encoding
import Mimir.StorageReadBinding as StorageReads
import Mimir.LearningQueryBinding as LearningReads
import Mimir.LearningContextProtocol as LearningContext
import Mimir.McpErrors as Errors
import Mimir.StructuredValue as Wire
import Mimir.ToolCatalog as Tools
import Mimir.Validation as Validation

-- Missing test observations are not application outcomes. In particular, a
-- missing capture must not manufacture a product request for user input.
data ObservationError : Set where
  observationError : Validation.Fault → ObservationError

module Evaluate (library : Library.Contract) (postgres : Controls.PostgreSQL) where
  module C = Binding.Creating library postgres
  module Read = Controls.Readback library postgres
  module Reserve = Controls.Reservation postgres
  module Cancel = Recovery.Cancellation

  -- These are external facts from the same attempted execution, not an
  -- expected world, a desired reply, an admission context or a recovery proof.
  -- The transport adapter is responsible for matching their operation token,
  -- boundary and attempt to the retained observation artifacts.
  record Observations (call : C.Call) : Set where
    field
      currentSettings : C.Settings
      bindingTime : Maybe ℤ
      planEncoding : Maybe (C.PlanEncoding call)

  Outcome = Store.World × C.Result
  Evaluation = ObservationError Data.Sum.⊎ Outcome

  module With (observed : (call : C.Call) → Observations call) where
    missing : String → String → ObservationError
    missing kind explanation = observationError (Validation.fault
      (Validation.key "observations" Data.List.∷ Validation.key kind Data.List.∷ Data.List.[])
      Validation.missingField explanation)

    finishPlan : C.Call → Store.World × C.PlanResult → Evaluation
    finishPlan call (after , C.planned binding model raw) =
      inj₂ (after , C.ready (C.preparedWrite call binding model raw))
    finishPlan call (after , C.planRefused fault) = inj₂ (after , C.needsInput fault)
    finishPlan call (after , C.planCancelled receipt) =
      inj₂ (after , C.returned (Read.answer (C.Call.token call) after))
    finishPlan call (after , C.planUnknown) =
      inj₂ (after , C.returned (Read.answer (C.Call.token call) after))

    -- A stored plan is enough on retry. A new codec observation is required
    -- only when this invocation actually has to publish a new plan.
    publishPlan : C.Call → Wire.Value → Store.World → Evaluation
    publishPlan call settings before with C.binding (C.Call.token call) before
    ... | nothing = finishPlan call (before , C.planUnknown)
    ... | just original with C.matches call settings original
    ... | false = finishPlan call (before , C.planRefused Binding.changedRequest)
    ... | true with Store.lookupCancellation before (C.Call.token call)
    ... | just receipt = finishPlan call (before , C.planCancelled receipt)
    ... | nothing with C.plan (C.Call.token call) before
    ... | just raw = finishPlan call (before , C.existingPlan original raw)
    ... | nothing with Read.savedRows (C.Call.token call) before
    ... | _ Data.List.∷ _ = finishPlan call (before , C.planRefused C.badPlan)
    ... | Data.List.[] with Observations.planEncoding (observed call)
    ... | nothing = inj₁ (missing "plan_encoding"
      "The oracle needs the actual validated standard plan encoding for this new plan. Capture that encoding for the same operation and attempt; do not invent it or report a product correction. Existing saved plans need no fresh encoding receipt.")
    ... | just codecReceipt = finishPlan call (C.saveNewPlan call original codecReceipt before)

    currentPolicy : C.Call → Wire.Value → C.Settings → Store.World → Evaluation
    currentPolicy call original (C.unavailable fault) before = inj₂ (before , C.needsInput fault)
    currentPolicy call original (C.configured current) before with
      Controls.PostgreSQL.jsonbEqual postgres original current
    ... | false = inj₂ (before , C.needsInput C.changedPolicy)
    ... | true = publishPlan call original before

    preparePlan : C.Call → Wire.Value → Store.World → Evaluation
    preparePlan call settings before with C.needsPolicy (C.Call.tool call)
    ... | false = publishPlan call settings before
    ... | true = currentPolicy call settings
      (Observations.currentSettings (observed call)) before

    resume : C.Call → Wire.Value → Store.World → Read.Result → Evaluation
    resume call settings before (Read.awaitingPlan _) = preparePlan call settings before
    resume call settings before (Read.awaitingCompletion _) = preparePlan call settings before
    resume call settings before (Read.pending _ _ _) = preparePlan call settings before
    resume call settings before outcome = inj₂ (before , C.returned outcome)

    finishBinding : C.Call → Wire.Value → Store.World × C.BindingResult → Evaluation
    finishBinding call settings (after , C.bound original) =
      resume call settings after (Read.answer (C.Call.token call) after)
    finishBinding call settings (after , C.changed original) = inj₂ (after , C.needsInput Binding.changedRequest)
    finishBinding call settings (after , C.unknown) = inj₂ (after , C.returned (Read.answer (C.Call.token call) after))
    finishBinding call settings (after , C.cancelled receipt) = inj₂ (after , C.returned (Read.answer (C.Call.token call) after))

    -- Existing binding time is already part of the original world. A fresh
    -- PostgreSQL time must be captured only for a genuinely new binding.
    bind : C.Call → Wire.Value → Store.World → Evaluation
    bind call settings before with C.binding (C.Call.token call) before
    ... | just original = finishBinding call settings
      (C.bind call settings (Store.BindingRow.boundAt original) before)
    ... | nothing with Controls.reservation (C.Call.token call) before
    ... | nothing = finishBinding call settings (before , C.unknown)
    ... | just reservation with Store.lookupCancellation before (C.Call.token call)
    ... | just receipt = finishBinding call settings (before , C.cancelled receipt)
    ... | nothing with Observations.bindingTime (observed call)
    ... | nothing = inj₁ (missing "postgres_writer_clock"
      "The oracle needs the PostgreSQL time actually used for this new binding. Capture it for the same operation and attempt; do not invent a timestamp or turn a missing test observation into a product correction.")
    ... | just time = finishBinding call settings (C.bind call settings time before)

    freshSettings : C.Call → C.Settings → Store.World → Evaluation
    freshSettings call (C.unavailable fault) before = inj₂ (before , C.needsInput fault)
    freshSettings call (C.configured settings) before with
      Public.freshLearningAdmission (C.Call.request call)
    ... | inj₁ fault = inj₂ (before , C.needsInput fault)
    ... | inj₂ tt = bind call settings before

    unbound : C.Call → Store.World → Read.Result → Evaluation
    unbound call before Read.reserved =
      freshSettings call (Observations.currentSettings (observed call)) before
    unbound call before outcome = inj₂ (before , C.returned outcome)

    admitted : C.Call → Store.World → Evaluation
    admitted call before with C.binding (C.Call.token call) before
    ... | just original = bind call (Store.BindingRow.settings original) before
    ... | nothing = unbound call before (Read.answer (C.Call.token call) before)

    evaluate : C.Request → Store.World → Evaluation
    evaluate requested before with C.decode requested
    ... | inj₁ fault = inj₂ (before , C.needsInput fault)
    ... | inj₂ call = admitted call before

    malformedInputUnchanged : ∀ requested before fault →
      C.decode requested ≡ inj₁ fault →
      evaluate requested before ≡ inj₂ (before , C.needsInput fault)
    malformedInputUnchanged requested before fault rejected rewrite rejected = refl

  -- Typed semantic output for the public adapter. A returned null body stays
  -- distinct from admission which never entered the business operation.
  data PublicOutcome : Set where
    requestCorrection : Validation.Fault → PublicOutcome
    operationReadback : Read.Result → PublicOutcome
    reservationReadback : Controls.RequestKey → Reserve.Result → PublicOutcome
    cancellationReadback : ℕ → Cancel.Result → PublicOutcome
    documentQueryReadback : DocumentQuery.Result → PublicOutcome
    retrievalReadback : PublicRetrieval.Response → PublicOutcome
    learningContextReadback : LearningContext.Output → PublicOutcome
    invalidContextAssessment : PublicOutcome
    invalidDecayInputs : PublicOutcome
    beliefDeletionProblem : (databaseSum : Data.List.List Float.Float → Float.Float) →
      BeliefDeletion.Diagnostics.Diagnostic databaseSum → PublicOutcome
    checkedPosteriorProblem : (databaseSum : Data.List.List Float.Float → Float.Float) →
      Grounding.Diagnostics.Diagnostic databaseSum → PublicOutcome
    agentDecision : Errors.AgentCorrection.Claim → PublicOutcome
    numericalReadback : (databaseSum : Data.List.List Float.Float → Float.Float) →
      Numerical.NumericalOutcome.Result databaseSum → PublicOutcome
    assessmentReadback : (format : Encoding.Formatting) →
      LearningReads.AssessmentReads.Answer format → PublicOutcome
    directValue : Wire.Value → PublicOutcome

  record Expected (Body : Set) : Set where
    constructor expected
    field
      world : Store.World
      body : Maybe Body
      publicOutcome : PublicOutcome

  module ReservationIntent where
    module Decode = Public.Decode library
    ReservationEvaluation = ObservationError Data.Sum.⊎ Expected Reserve.Result

    missingReceipt : ObservationError
    missingReceipt = observationError (Validation.fault
      (Validation.key "observations" Data.List.∷ Validation.key "reservation" Data.List.∷ Data.List.[])
      Validation.missingField
      "A fresh request_key needs its actual PostgreSQL reservation identity and time for this attempt. Capture the original returning receipt; do not invent a token or turn missing test input into a product correction. Reusing a saved key needs no new receipt.")

    reusedIdentity : ObservationError
    reusedIdentity = observationError (Validation.fault
      (Validation.key "observations" Data.List.∷ Validation.key "reservation" Data.List.∷ Validation.key "operation_token" Data.List.∷ Data.List.[])
      Validation.wrongIdentity
      "The proposed fresh reservation token already exists in the starting world. Match the actual PostgreSQL returning receipt to this request_key and attempt; do not borrow another action's token.")

    returned : Controls.RequestKey → Store.World → Reserve.Result → Expected Reserve.Result
    returned key after reply = expected after (just reply) (reservationReadback key reply)

    reserve : Controls.RequestKey → Store.World → Maybe Store.ReservationRow → ReservationEvaluation
    reserve key before receipt with Reserve.inspect key before
    ... | Reserve.original saved = inj₂ (returned key before (Reserve.reserved saved))
    ... | Reserve.broken token = inj₂ (returned key before (Reserve.needsRecovery token))
    ... | Reserve.vacant with receipt
    ... | nothing = inj₁ missingReceipt
    ... | just received with Controls.reservation (Store.ReservationRow.token received) before
    ... | just _ = inj₁ reusedIdentity
    ... | nothing = inj₂ (returned key (Reserve.publish key received before) (Reserve.reserved received))

    afterKey : Validation.Fault Data.Sum.⊎ Controls.RequestKey → Store.World → Maybe Store.ReservationRow → ReservationEvaluation
    afterKey (inj₁ fault) before receipt = inj₂ (expected before nothing (requestCorrection fault))
    afterKey (inj₂ key) before receipt = reserve key before receipt

    evaluate : Wire.Value → Store.World → Maybe Store.ReservationRow → ReservationEvaluation
    evaluate raw before receipt with Decode.readInvocation Tools.reserveOperation raw
    ... | inj₁ fault = inj₂ (expected before nothing (requestCorrection fault))
    ... | inj₂ admitted = afterKey
      (Record._>>=_ (PublicInput.required "request_key" Wire.asString
        (Wire.Object.normalize (Decode.Invocation.suppliedFields admitted))) Controls.admitRequestKey)
      before receipt

    replayNeedsNoFreshReceipt : ∀ key before saved →
      Reserve.inspect key before ≡ Reserve.original saved →
      reserve key before nothing ≡ inj₂ (returned key before (Reserve.reserved saved))
    replayNeedsNoFreshReceipt key before saved original rewrite original = refl

    missingFreshReceiptIsOracleInputError : ∀ key before →
      Reserve.inspect key before ≡ Reserve.vacant →
      reserve key before nothing ≡ inj₁ missingReceipt
    missingFreshReceiptIsOracleInputError key before absentKey rewrite absentKey = refl

    malformedRequestDoesNotEnterBody : ∀ raw before receipt fault →
      Decode.readInvocation Tools.reserveOperation raw ≡ inj₁ fault →
      evaluate raw before receipt ≡ inj₂ (expected before nothing (requestCorrection fault))
    malformedRequestDoesNotEnterBody raw before receipt fault rejected rewrite rejected = refl

  module CancellationIntent where
    module Decode = Public.Decode library
    CancellationEvaluation = ObservationError Data.Sum.⊎ Expected Cancel.Result

    missingClock : ObservationError
    missingClock = observationError (Validation.fault
      (Validation.key "observations" Data.List.∷ Validation.key "cancellation_clock" Data.List.∷ Data.List.[])
      Validation.missingField
      "A fresh cancellation needs the PostgreSQL clock actually used for its cancellation row. Capture that receipt for this token and attempt; do not invent a timestamp or turn missing test input into a product correction. Existing cancellation and completed results need no fresh clock.")

    returned : ℕ → Store.World → Cancel.Result → Expected Cancel.Result
    returned token after reply = expected after (just reply) (cancellationReadback token reply)

    -- This is the independently stated database intent, not an execution of
    -- the receipt script and not a claim that any physical worker has stopped.
    atTime : ℕ → ℤ → Store.World → Expected Cancel.Result
    atTime token time before = returned token (Cancel.intended original before)
      (Cancel.expectedReply original before)
      where original = Cancel.input token time

    cancel : ℕ → Store.World → Maybe ℤ → CancellationEvaluation
    cancel token before receipt with Cancel.reserved token
      (Store.OperationTables.reservations (Store.World.operations before))
    ... | false = inj₂ (returned token before Cancel.unknownToken)
    ... | true with Store.lookupSaved before token Cancel.resultKey
    ... | just saved = inj₂ (returned token before (Cancel.savedResult saved))
    ... | nothing with Store.lookupCancellation before token
    ... | just original = inj₂ (atTime token (Store.CancellationRow.cancelledAt original) before)
    ... | nothing with receipt
    ... | nothing = inj₁ missingClock
    ... | just time = inj₂ (atTime token time before)

    afterToken : Validation.Fault Data.Sum.⊎ ℕ → Store.World → Maybe ℤ → CancellationEvaluation
    afterToken (inj₁ fault) before receipt = inj₂ (expected before nothing (requestCorrection fault))
    afterToken (inj₂ token) before receipt = cancel token before receipt

    evaluate : Wire.Value → Store.World → Maybe ℤ → CancellationEvaluation
    evaluate raw before receipt with Decode.readInvocation Tools.cancelOperation raw
    ... | inj₁ fault = inj₂ (expected before nothing (requestCorrection fault))
    ... | inj₂ admitted = afterToken
      (PublicInput.required "operation_token" (PublicInput.readUUID library)
        (Wire.Object.normalize (Decode.Invocation.suppliedFields admitted))) before receipt

    savedResultNeedsNoFreshClock : ∀ token before saved →
      Cancel.reserved token (Store.OperationTables.reservations (Store.World.operations before)) ≡ true →
      Store.lookupSaved before token Cancel.resultKey ≡ just saved →
      cancel token before nothing ≡ inj₂ (returned token before (Cancel.savedResult saved))
    savedResultNeedsNoFreshClock token before saved allocated completed rewrite allocated | completed = refl

    malformedRequestDoesNotEnterBody : ∀ raw before receipt fault →
      Decode.readInvocation Tools.cancelOperation raw ≡ inj₁ fault →
      evaluate raw before receipt ≡ inj₂ (expected before nothing (requestCorrection fault))
    malformedRequestDoesNotEnterBody raw before receipt fault rejected rewrite rejected = refl

  module OperationReadback where
    module Decode = Public.Decode library

    -- The complete saved state supplies the answer. This includes malformed
    -- journals and cancellation; neither is replaced with an assumed success.
    read : ℕ → Store.World → Expected Read.Result
    read token before = expected before (just answer) (operationReadback answer)
      where answer = Read.answer token before

    afterToken : Validation.Fault Data.Sum.⊎ ℕ → Store.World → Expected Read.Result
    afterToken (inj₁ fault) before = expected before nothing (requestCorrection fault)
    afterToken (inj₂ token) before = read token before

    evaluate : Wire.Value → Store.World → Expected Read.Result
    evaluate raw before with Decode.readInvocation Tools.operationOutcome raw
    ... | inj₁ fault = expected before nothing (requestCorrection fault)
    ... | inj₂ admitted = afterToken
      (PublicInput.required "operation_token" (PublicInput.readUUID library)
        (Wire.Object.normalize (Decode.Invocation.suppliedFields admitted))) before

    afterTokenKeepsWorld : ∀ received before → Expected.world (afterToken received before) ≡ before
    afterTokenKeepsWorld (inj₁ fault) before = refl
    afterTokenKeepsWorld (inj₂ token) before = refl

    neverChangesWorld : ∀ raw before → Expected.world (evaluate raw before) ≡ before
    neverChangesWorld raw before with Decode.readInvocation Tools.operationOutcome raw
    ... | inj₁ fault = refl
    ... | inj₂ admitted = afterTokenKeepsWorld
      (PublicInput.required "operation_token" (PublicInput.readUUID library)
        (Wire.Object.normalize (Decode.Invocation.suppliedFields admitted))) before

    malformedRequestDoesNotEnterBody : ∀ raw before fault →
      Decode.readInvocation Tools.operationOutcome raw ≡ inj₁ fault →
      evaluate raw before ≡ expected before nothing (requestCorrection fault)
    malformedRequestDoesNotEnterBody raw before fault rejected rewrite rejected = refl

  module AssessmentIntent (format : Encoding.Formatting) where
    module Assessments = LearningReads.AssessmentReads format
    module Decode = Public.Decode library

    data Family : Set where scores history explanation : Family

    tool : Family → Tools.Tool
    tool scores = Tools.getLessonAssessment
    tool history = Tools.lessonAssessmentHistory
    tool explanation = Tools.explainBelief

    -- All parsing uses the same field readers as public admission. Ordered
    -- pages, missing targets and invalid stored values remain typed results.
    request : Family → Wire.Object.View → Validation.Fault Data.Sum.⊎ Assessments.Request
    request scores fields = Record.mapResult Assessments.scores (Decode.assessmentQuery fields)
    request history fields = Record._>>=_ (Decode.assessmentQuery fields) λ query →
      Record._>>=_ (PublicInput.defaulted "offset" 0 Decode.integer fields) λ offset →
      Record.mapResult (Assessments.history query offset) (Decode.selection "limit" fields)
    request explanation fields = Record._>>=_ (PublicInput.required "id" (PublicInput.readUUID library) fields) λ identity →
      Record._>>=_ (PublicInput.defaulted "offset" 0 Decode.integer fields) λ offset →
      Record.mapResult (Assessments.explanation identity offset) (Decode.selection "limit" fields)

    read : Assessments.Request → Store.World → Expected Assessments.Answer
    read selected before = expected before (just answer) (assessmentReadback format answer)
      where answer = Assessments.answer selected before

    afterRequest : Validation.Fault Data.Sum.⊎ Assessments.Request → Store.World → Expected Assessments.Answer
    afterRequest (inj₁ fault) before = expected before nothing (requestCorrection fault)
    afterRequest (inj₂ selected) before = read selected before

    evaluate : Family → Wire.Value → Store.World → Expected Assessments.Answer
    evaluate family raw before with Decode.readInvocation (tool family) raw
    ... | inj₁ fault = expected before nothing (requestCorrection fault)
    ... | inj₂ admitted = afterRequest
      (request family (Wire.Object.normalize (Decode.Invocation.suppliedFields admitted))) before

    afterRequestKeepsWorld : ∀ received before → Expected.world (afterRequest received before) ≡ before
    afterRequestKeepsWorld (inj₁ fault) before = refl
    afterRequestKeepsWorld (inj₂ selected) before = refl

    neverChangesWorld : ∀ family raw before → Expected.world (evaluate family raw before) ≡ before
    neverChangesWorld family raw before with Decode.readInvocation (tool family) raw
    ... | inj₁ fault = refl
    ... | inj₂ admitted = afterRequestKeepsWorld
      (request family (Wire.Object.normalize (Decode.Invocation.suppliedFields admitted))) before

    malformedRequestDoesNotEnterBody : ∀ family raw before fault →
      Decode.readInvocation (tool family) raw ≡ inj₁ fault →
      evaluate family raw before ≡ expected before nothing (requestCorrection fault)
    malformedRequestDoesNotEnterBody family raw before fault rejected rewrite rejected = refl

  module BasicIntent (format : Encoding.Formatting) where
    module Basic = StorageReads.BasicReads format
    module Decode = Public.Decode library

    data Family : Set where belief beliefs patterns contradictions evidence capabilities : Family

    tool : Family → Tools.Tool
    tool belief = Tools.getBelief
    tool beliefs = Tools.listBeliefs
    tool patterns = Tools.listPatterns
    tool contradictions = Tools.getContradictions
    tool evidence = Tools.getEvidence
    tool capabilities = Tools.learningCapabilities

    -- Omitted selection means all matches; an explicit page uses the same
    -- positive count and offset validation as public admission. BasicReads
    -- stores count-minus-one, which has no zero-means-all interpretation.
    listRequest : Wire.Object.View → Maybe Candidates.Memory → Validation.Fault Data.Sum.⊎ Basic.Request
    listRequest fields memory with fields (Data.String.toList "limit")
    ... | nothing with fields (Data.String.toList "offset")
    ... | nothing = inj₂ (Basic.listBeliefs (Decode.project fields) memory)
    ... | just _ = PublicInput.bad "offset requires limit"
    listRequest fields memory | just raw =
      Record._>>=_ (PublicInput.required "limit" Decode.selectedCount fields) λ selected →
      Record.mapResult (Basic.beliefPage (Decode.project fields) memory
        (pred (Ranking.PositiveCount.count selected)))
        (PublicInput.defaulted "offset" 0 Decode.integer fields)

    request : Family → Wire.Object.View → Validation.Fault Data.Sum.⊎ Basic.Request
    request belief fields = Record.mapResult Basic.getBelief
      (PublicInput.required "id" (PublicInput.readUUID library) fields)
    request beliefs fields = Record._>>=_
      (Public.memoryField (Data.String.toList "memory_type") fields) (listRequest fields)
    request patterns fields = inj₂ (Basic.listPatterns (Decode.project fields))
    request contradictions fields = inj₂ (Basic.contradictions (Decode.project fields))
    request evidence fields = Record.mapResult Basic.evidence
      (PublicInput.required "belief_id" (PublicInput.readUUID library) fields)
    request capabilities fields = inj₂ Basic.capabilities

    read : Basic.Request → Store.World → Expected Wire.Value
    read selected before = expected before (just answer) (directValue answer)
      where answer = Basic.answer selected before

    afterRequest : Validation.Fault Data.Sum.⊎ Basic.Request → Store.World → Expected Wire.Value
    afterRequest (inj₁ fault) before = expected before nothing (requestCorrection fault)
    afterRequest (inj₂ selected) before = read selected before

    evaluate : Family → Wire.Value → Store.World → Expected Wire.Value
    evaluate family raw before with Decode.readInvocation (tool family) raw
    ... | inj₁ fault = expected before nothing (requestCorrection fault)
    ... | inj₂ admitted = afterRequest
      (request family (Wire.Object.normalize (Decode.Invocation.suppliedFields admitted))) before

    afterRequestKeepsWorld : ∀ received before → Expected.world (afterRequest received before) ≡ before
    afterRequestKeepsWorld (inj₁ fault) before = refl
    afterRequestKeepsWorld (inj₂ selected) before = refl

    neverChangesWorld : ∀ family raw before → Expected.world (evaluate family raw before) ≡ before
    neverChangesWorld family raw before with Decode.readInvocation (tool family) raw
    ... | inj₁ fault = refl
    ... | inj₂ admitted = afterRequestKeepsWorld
      (request family (Wire.Object.normalize (Decode.Invocation.suppliedFields admitted))) before

    malformedRequestDoesNotEnterBody : ∀ family raw before fault →
      Decode.readInvocation (tool family) raw ≡ inj₁ fault →
      evaluate family raw before ≡ expected before nothing (requestCorrection fault)
    malformedRequestDoesNotEnterBody family raw before fault rejected rewrite rejected = refl

  module ExperienceIntent (format : Encoding.Formatting) where
    module Experiences = LearningReads.ExperienceReads format
    module Decode = Public.Decode library

    data Family : Set where experience currentReview history pending : Family

    tool : Family → Tools.Tool
    tool experience = Tools.getExperience
    tool currentReview = Tools.getLearningReview
    tool history = Tools.experienceHistory
    tool pending = Tools.pendingExperiences

    request : Family → Wire.Object.View → Validation.Fault Data.Sum.⊎ Experiences.Request
    request experience fields = Record.mapResult Experiences.experience
      (PublicInput.required "id" (PublicInput.readUUID library) fields)
    request currentReview fields = Record.mapResult Experiences.currentReview
      (PublicInput.required "id" (PublicInput.readUUID library) fields)
    request history fields = Record.mapResult Experiences.history
      (PublicInput.required "id" (PublicInput.readUUID library) fields)
    request pending fields = Record._>>=_ (PublicInput.present "project" Wire.asString fields) λ project →
      Record._>>=_ (Decode.selection "limit" fields) λ selection →
      Record.mapResult (Experiences.pending project selection)
        (PublicInput.defaulted "exclude_ids" Data.List.[]
          (Record.readArray (PublicInput.readUUID library)) fields)

    -- The complete raw history and stored current review come from this
    -- World; the caller supplies no desired rows or reformatted history.
    read : Experiences.Request → Store.World → Expected Wire.Value
    read selected before = expected before (just answer) (directValue answer)
      where answer = Experiences.answer selected before

    afterRequest : Validation.Fault Data.Sum.⊎ Experiences.Request → Store.World → Expected Wire.Value
    afterRequest (inj₁ fault) before = expected before nothing (requestCorrection fault)
    afterRequest (inj₂ selected) before = read selected before

    evaluate : Family → Wire.Value → Store.World → Expected Wire.Value
    evaluate family raw before with Decode.readInvocation (tool family) raw
    ... | inj₁ fault = expected before nothing (requestCorrection fault)
    ... | inj₂ admitted = afterRequest
      (request family (Wire.Object.normalize (Decode.Invocation.suppliedFields admitted))) before

    afterRequestKeepsWorld : ∀ received before → Expected.world (afterRequest received before) ≡ before
    afterRequestKeepsWorld (inj₁ fault) before = refl
    afterRequestKeepsWorld (inj₂ selected) before = refl

    neverChangesWorld : ∀ family raw before → Expected.world (evaluate family raw before) ≡ before
    neverChangesWorld family raw before with Decode.readInvocation (tool family) raw
    ... | inj₁ fault = refl
    ... | inj₂ admitted = afterRequestKeepsWorld
      (request family (Wire.Object.normalize (Decode.Invocation.suppliedFields admitted))) before

    malformedRequestDoesNotEnterBody : ∀ family raw before fault →
      Decode.readInvocation (tool family) raw ≡ inj₁ fault →
      evaluate family raw before ≡ expected before nothing (requestCorrection fault)
    malformedRequestDoesNotEnterBody family raw before fault rejected rewrite rejected = refl

  module ReadOnly (format : Encoding.Formatting) where
    module Basic = StorageReads.BasicReads format using (Request; answer)
    module Experiences = LearningReads.ExperienceReads format using (Request; answer)

    basic : Basic.Request → Store.World → Expected Wire.Value
    basic request before = expected before (just answer) (directValue answer)
      where answer = Basic.answer request before

    experience : Experiences.Request → Store.World → Expected Wire.Value
    experience request before = expected before (just answer) (directValue answer)
      where answer = Experiences.answer request before

  module ProjectDeletion (observed : (call : C.Call) → Observations call) where
    module Metadata = With observed
    module Decode = Public.Decode library

    project : ∀ {raw} → Decode.Invocation Tools.deleteProject raw → Text
    project call = proj₁ (C.readProject (Decode.Invocation.arguments call)
      (Decode.Invocation.request call) (Decode.Invocation.decoded call))

    -- The operation input comes from the original submitted request. The
    -- metadata result cannot replace its token, project or desired outcome.
    prepared : Project.Registered.Input → Outcome → Expected Wire.Value
    prepared request (before , C.needsInput fault) =
      expected before nothing (requestCorrection fault)
    prepared request (before , C.returned outcome) =
      expected before nothing (operationReadback outcome)
    prepared request (before , C.ready context) =
      expected final (just answer)
        (operationReadback (Read.answer (Project.Registered.Input.token request) final))
      where
      final = Project.Registered.intended request before
      answer = Project.Registered.expectedReply request before

    evaluate : Wire.Value → Store.World → ObservationError Data.Sum.⊎ Expected Wire.Value
    evaluate raw before with Decode.readInvocation Tools.deleteProject raw
    ... | inj₁ fault = inj₂ (expected before nothing (requestCorrection fault))
    ... | inj₂ call with Metadata.admitted (C.admittedWrite Tools.deleteProject raw refl call) before
    ... | inj₁ missing = inj₁ missing
    ... | inj₂ outcome = inj₂ (prepared
      (Project.Registered.input (Decode.Invocation.operationToken call) (project call)) outcome)
