{-# OPTIONS --safe #-}
-- One selected revision. Database readback confirms a review.
module Mimir.JudgeRevision where

open import Data.Bool using (Bool; true; false; not)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Mimir.UUIDGroups using (UUID)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String; toList)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
open import Mimir.Bits using (Byte)
import Mimir.Effects as Effects
import Mimir.JudgeRevisionPolicy as Policy
import Mimir.JudgeScopedTools as Scoped
import Mimir.ReviewObservation as Observation
import Mimir.BatchReport as Batch
import Mimir.JudgeStateRecords as Records
import Mimir.JudgeBatchReadback as Readback
import Mimir.SourceFailure as Source
import Mimir.StructuredValue as V
import Mimir.PublicEncoding as Encoding
import Mimir.StandardLibrary as Conversion
import Mimir.Validation as Validation
import Mimir.ExperienceSchema as Experience

module R = Records.Over UUID

-- JSON rendering and error display provide correction details.
record Display : Set where
  field json : V.Value → Text; bytes : V.Value → List Byte
        fault : Validation.Fault → Text
        evidenceGuidance : Experience.Experience → Text

record Error : Set where
  constructor error
  field detail : Text; source : Maybe Source.Failure

data Action : Set where
  modelDone : Action
  tool : Text → V.Value → Action
  malformedTool : Text → Source.Failure → Action

data Answer : Set where
  action : Action → Answer
  backendError : Error → Answer

record Rejection : Set where
  constructor rejection
  field name detail : Text; source : Maybe Source.Failure

feedback : String → Text → String → V.Value
feedback kind message guidance = Encoding.object
  (("error" , V.string (toList kind)) ∷ ("message" , V.string message) ∷
   ("guidance" , V.string (toList guidance)) ∷ [])

candidateFeedback : V.Value
candidateFeedback = Encoding.object
  (("error" , V.string (toList "candidate_key_conflict")) ∷
   ("guidance" , V.string (toList "A candidate key from an earlier review has a different declaration. Inspect experience_history. Reuse a key only with its exact original kind and declaration; use a new key for a revised claim.")) ∷ [])

module Run (conversion : Conversion.Contract) (format : Encoding.Formatting)
  (display : Display) (selected : Observation.Snapshot) where

  module Scope = Scoped.For conversion format selected
  pin = Observation.pinSnapshot selected
  identity = Observation.Pin.identity pin

  record Work : Set where
    constructor work
    field report : R.Report; policy : Policy.State; last : Maybe V.Value; lastRejection : Maybe Rejection
          submissionRequested : Bool

  record Outcome : Set where
    constructor outcome
    field report : R.Report; failed : Bool

  data Effect : Set where
    nextModel : Maybe V.Value → Effect
    hostTool : Scoped.Effect → Effect
    stopTool : Effect
    observe : Effect
    clock : Effect

  Reply : Effect → Set
  Reply (nextModel last) = Answer
  Reply (hostTool request) = Scoped.Reply request
  Reply stopTool = ⊤
  Reply observe = Error ⊎ Maybe Observation.Snapshot
  Reply clock = Maybe ℕ
  module P = Effects.Protocol Effect Reply
  open P

  data State : Set where
    loop : Work → State
    executing : Script State → State
    finished : Outcome → State

  fromScoped : ∀ {A} → Scoped.P.Script A → Script A
  fromScoped (Scoped.P.done value) = done value
  fromScoped (Scoped.P.ask request next) = ask (hostTool request) (λ reply → fromScoped (next reply))

  firstDiagnostic : Work → Text → Text → Maybe Source.Failure → Script Work
  firstDiagnostic w name detail source with R.Report.diagnostic (Work.report w)
  ... | just _ = done (record w { report = R.captureSource source (Work.report w) })
  ... | nothing = ask clock (λ observed → done (record w
    { report = record (R.captureSource source (Work.report w))
      { diagnostic = just (R.newDiagnostic observed identity name detail) } }))

  deferred : Work → Script State
  deferred w with Policy.finish pin (Work.policy w)
    (map (λ d → Observation.deferred (R.Deferred.identity d) (R.Deferred.revision d))
      (R.Report.deferredReviews (Work.report w)))
  ... | Policy.retained retained = done (finished (outcome
      (record (Work.report w) { deferredReviews = map
        (λ d → R.deferred (Observation.Deferred.identity d) (Observation.Deferred.revision d)) retained })
      (Policy.State.failed (Work.policy w))))

  afterRejection : Work → Script State
  afterRejection w with Policy.shouldDefer (Work.policy w)
  ... | false = deferred w
  ... | true = firstDiagnostic w (toList "review_experience") detail nothing >>= deferred
    where
    detail : Text
    detail with Policy.State.lastConflict (Work.policy w)
    ... | just message = message
    ... | nothing = toList "review correction was not confirmed"

  rejectionReason : R.Report → R.Report
  rejectionReason r with R.Report.blockReason r
  ... | just _ = r
  ... | nothing = record r { blockReason = just (toList "tool_rejected") }

  end : Work → Script State
  end w with Policy.State.settled (Work.policy w) | Work.lastRejection w
  ... | true | _ = afterRejection w
  ... | false | nothing = afterRejection w
  ... | false | just rejected = firstDiagnostic w (Rejection.name rejected)
      (Rejection.detail rejected) (Rejection.source rejected) >>= λ updated →
      afterRejection (record updated { report = rejectionReason (Work.report updated) })

  conditional : Work → Policy.Event → String → Maybe Text → Maybe Source.Failure → Work
  conditional w event reason detail source with Policy.State.conflicts (Work.policy w)
  ... | suc _ = record w { policy = Policy.Step.state (Policy.step (Work.policy w) event) }
  ... | zero = record w
    { policy = Policy.Step.state (Policy.step (Work.policy w) event)
    ; report = record (R.captureSource source (Work.report w))
        { blockReason = just (toList reason) ; failureDetail = detail } }

  sourceError : String → V.Value → Validation.Fault → Error
  sourceError stage value failure = error (Source.display source) (just source)
    where source = Source.Current.input conversion (toList stage) (Display.bytes display value) (Display.fault display failure)

  scopedError : Scoped.Failure → Error
  scopedError (Scoped.rejected detail) = error detail nothing
  scopedError (Scoped.needsUserDecision detail) = error detail nothing
  scopedError (Scoped.invalidResponse detail) = error detail nothing
  scopedError (Scoped.transport detail) = error detail nothing
  scopedError (Scoped.sourceFailure source) = error (Source.display source) (just source)
  scopedError (Scoped.application detail) = error detail nothing
  scopedError (Scoped.candidateConflict detail) = error detail nothing
  scopedError (Scoped.malformedReview value failure) = sourceError "invalid review arguments" value failure
  scopedError (Scoped.malformedState value failure) = sourceError "invalid experience state" value failure
  scopedError (Scoped.invalidReviewSchema failure) = error (Display.fault display failure ++ toList ". " ++
    Display.evidenceGuidance display (Observation.Snapshot.experience selected)) nothing

  rejectionMessage : Scoped.Failure → Maybe Text
  rejectionMessage (Scoped.rejected detail) = just detail
  -- An application error does not prove that the arguments were invalid.
  rejectionMessage (Scoped.application _) = nothing
  rejectionMessage (Scoped.malformedReview value failure) = just (Display.fault display failure)
  rejectionMessage (Scoped.invalidReviewSchema failure) = just (Error.detail (scopedError (Scoped.invalidReviewSchema failure)))
  rejectionMessage _ = nothing

  unresolvedReview : Work → Script State
  unresolvedReview w = end (record w
    { policy = Policy.Step.state (Policy.step (Work.policy w) Policy.toolInfrastructureError)
    ; report = record (Work.report w) { blockReason = just (toList "tool_error") } })

  readbackUnavailable : Work → Error → Script State
  readbackUnavailable w failure =
    firstDiagnostic w (toList "review readback") (Error.detail failure) (Error.source failure) >>= unresolvedReview

  afterObservation : Work → Reply observe → Script State
  afterObservation w (inj₁ failure) = readbackUnavailable w failure
  afterObservation w (inj₂ snapshot) with Observation.observe pin snapshot
  ... | Observation.malformed failure = readbackUnavailable w (error (Display.fault display failure) nothing)
  ... | receipt with Policy.step (Work.policy w) (Policy.reviewed (Batch.label receipt))
  ...   | Policy.mkStep next Policy.continueRevision = done (loop (record w { policy = next }))
  ...   | Policy.mkStep next _ = end (record w { policy = next })

  -- An empty model reply can arrive before it submits anything, or after
  -- another caller has saved a review. Read the selected experience first.
  -- Once the missing submission has been explained, the same empty reply
  -- with no saved review requires repair outside this attempt.
  submissionDetail : Work → Text
  submissionDetail w with Work.lastRejection w
  ... | nothing = toList "There is no saved review for the selected experience revision."
  ... | just rejected = toList "The last submission was rejected. " ++ Rejection.detail rejected

  missingSubmission : Work → Script State
  missingSubmission w with Work.submissionRequested w
  ... | false = done (loop (record w
    { submissionRequested = true
    ; last = just (feedback "review_not_saved"
        (submissionDetail w)
        "Submit review_experience for the selected experience and revisions. Correct any rejected fields before submitting.") }))
  ... | true = firstDiagnostic w (toList "review_experience")
    (toList "The judge stopped without saving a review after being asked to submit it.") nothing >>= λ recorded →
    end (record recorded
      { report = record (Work.report recorded)
        { blockReason = just (toList "review_requires_repair") } })

  afterDone : Work → Reply observe → Script State
  afterDone w (inj₁ failure) = readbackUnavailable w failure
  afterDone w (inj₂ snapshot) with Observation.observe pin snapshot
  ... | Observation.unavailable =
    readbackUnavailable w (error (toList "The selected experience is unavailable for review confirmation.") nothing)
  ... | Observation.malformed failure =
    readbackUnavailable w (error (Display.fault display failure) nothing)
  ... | Observation.found _ _ (Observation.pending _ _ _) = missingSubmission w
  ... | Observation.found _ _ (Observation.confirmed _) =
    end (record w { policy = record (Work.policy w) { settled = true } })
  ... | Observation.found _ _ (Observation.corrected _ _) =
    end (record w { policy = record (Work.policy w) { settled = true } })

  pendingDoneContinuesWithSubmissionRequest :
    ∀ w snapshot stored valid identityMatches sameRevision unconfirmed →
    Observation.observe pin snapshot ≡
      Observation.found stored valid (Observation.pending identityMatches sameRevision unconfirmed) →
    Work.submissionRequested w ≡ false →
    Σ Work (λ next → afterDone w (inj₂ snapshot) ≡ done (loop next) ×
      Work.submissionRequested next ≡ true)
  pendingDoneContinuesWithSubmissionRequest w snapshot stored valid match same unconfirmed observed requested
    rewrite observed | requested = _ , refl , refl


  infrastructure : Work → Text → Error → Script State
  infrastructure w name failure = ask stopTool (λ _ →
    ask clock (λ observed → end (record w
      { policy = Policy.Step.state (Policy.step (Work.policy w) Policy.toolInfrastructureError)
      ; report = record (R.captureSource (Error.source failure) (Work.report w))
        { blockReason = just (toList "tool_error")
        ; diagnostic = just (R.newDiagnostic observed identity name (Error.detail failure)) } })))

  inputRejected : Work → Text → Scoped.Failure → Text → Script State
  inputRejected w name failure message = done (loop (record w
      { policy = Policy.Step.state (Policy.step (Work.policy w) (Policy.inputRejected message))
      ; last = just (feedback "invalid_tool_arguments" message
          "Correct the indicated arguments and resubmit. If the intended value is unclear, ask the user.")
      ; lastRejection = just (rejection name (Error.detail diagnostic) (Error.source diagnostic)) }))
    where diagnostic = scopedError failure

  data Continues : State → Set where
    continue : ∀ work → Continues (loop work)

  correctionContinues : ∀ w name failure message events result →
    Runs (inputRejected w name failure message) events result → Continues result
  correctionContinues w name failure message events result (returned _) = continue _

  ordinaryFailure : Work → Text → Scoped.Failure → Script State
  ordinaryFailure w name (Scoped.needsUserDecision detail) =
    firstDiagnostic w name detail nothing >>= λ recorded → end (record recorded
      { report = record (Work.report recorded)
        { blockReason = just (toList "needs_input") ; failureDetail = just detail } })
  ordinaryFailure w name failure with rejectionMessage failure
  ... | just message = inputRejected w name failure message
  ... | nothing = infrastructure w name (scopedError failure)

  conflict : Work → Text → Text → Script State
  conflict w name detail with Policy.step (Work.policy w) (Policy.candidateConflict detail)
  ... | Policy.mkStep next Policy.retryCandidate =
    done (loop (record w { policy = next ; last = just candidateFeedback }))
  ... | Policy.mkStep next _ = end (record w { policy = next })

  afterTool : Work → Text → Scoped.Failure ⊎ V.Value → Script State
  afterTool w name (inj₁ (Scoped.candidateConflict detail)) with does (name ≟Text toList "review_experience")
  ... | true = conflict w name detail
  ... | false = ordinaryFailure w name (Scoped.candidateConflict detail)
  afterTool w name (inj₁ failure) = ordinaryFailure w name failure
  afterTool w name (inj₂ value) = next
    where
    updated = record w { last = just value }
    next : Script State
    next with does (name ≟Text toList "review_experience")
    ... | true = ask observe (afterObservation updated)
    ... | false = done (loop updated)

  transportFailureStopsFirst : ∀ w name detail →
    Σ (⊤ → Script State) (λ continuation →
      afterTool w name (inj₁ (Scoped.transport detail)) ≡ ask stopTool continuation)
  transportFailureStopsFirst w name detail = _ , refl

  graphScopeRefusalContinues : ∀ w name kind args belief events result →
    Scoped.textIs Scope.project (Scoped.get "project" belief) ≡ false →
    Runs (fromScoped (Scope.exactGraph kind args belief) >>= afterTool w name) events result →
    Continues result
  graphScopeRefusalContinues w name kind args belief events result outside execution
    rewrite Scope.graphScopeRefusal kind args belief outside =
    correctionContinues w name (Scoped.rejected Scope.graphScopeMessage)
      Scope.graphScopeMessage events result execution

  attempt : Work → Text → V.Value → Script State
  attempt w name arguments = fromScoped (Scope.run name arguments) >>= afterTool w name

  malformedAttempt : Work → Text → Source.Failure → Script State
  malformedAttempt w name source = done (loop (record w
    { last = just (feedback "invalid_tool_arguments" (Source.Failure.detail source)
        "Correct the tool arguments using the supplied schema and resend the call.")
    ; lastRejection = just (rejection name (Source.display source) (just source)) }))

  afterModel : Work → Answer → Script State
  afterModel w (backendError failure) =
    end (conditional w Policy.modelError "backend_error" (just (Error.detail failure)) (Error.source failure))
  afterModel w (action modelDone) = ask observe (afterDone w)
  afterModel w (action (tool name arguments)) = attempt w name arguments
  afterModel w (action (malformedTool name source)) = malformedAttempt w name source

  data Step : Set where
    internal : State → Step
    external : (effect : Effect) → (Reply effect → State) → Step
    stopped : Outcome → Step

  next : State → Step
  next (loop w) = external (nextModel (Work.last w)) (λ reply → executing (afterModel w reply))
  next (executing (done state)) = internal state
  next (executing (ask effect continuation)) = external effect (λ reply → executing (continuation reply))
  next (finished result) = stopped result

  data Transition : State → Maybe P.Event → State → Set where
    internalStep : ∀ {before after} → next before ≡ internal after → Transition before nothing after
    externalStep : ∀ {before effect continuation} → next before ≡ external effect continuation →
      (reply : Reply effect) → Transition before (just (effect , reply)) (continuation reply)

  data Trace : State → List (Maybe P.Event) → State → Set where
    empty : ∀ {state} → Trace state [] state
    step : ∀ {before middle after event events} → Transition before event middle →
      Trace middle events after → Trace before (event ∷ events) after

  start : R.Report → State
  start report = loop (work report Policy.initial nothing nothing false)
