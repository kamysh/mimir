{-# OPTIONS --safe #-}
-- One selected revision. Database readback confirms a review.
module Mimir.JudgeRevision where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Bool.ListAction using (any)
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
  backendUnavailable : Error → Answer
  providerWaiting : Error → Policy.Signal → Answer

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
    field report : R.Report; sentCorrections : List (Text × Text); last : Maybe V.Value; lastRejection : Maybe Rejection
          submissionRequested : Bool

  record Outcome : Set where
    constructor outcome
    field report : R.Report; obstacle : Maybe Policy.Obstacle

  data Effect : Set where
    nextModel : Maybe V.Value → Effect
    prepareCorrection : Maybe Rejection → Effect
    hostTool : Scoped.Effect → Effect
    stopTool releaseBackend : Effect
    observe : Effect
    clock : Effect

  Reply : Effect → Set
  Reply (nextModel last) = Answer
  Reply (prepareCorrection rejected) = Maybe V.Value
  Reply (hostTool request) = Scoped.Reply request
  Reply stopTool = ⊤
  Reply releaseBackend = ⊤
  Reply observe = Error ⊎ Maybe Observation.Snapshot
  Reply clock = Maybe ℕ
  module P = Effects.Protocol Effect Reply
  open P

  data State : Set where
    loop : Work → State
    correcting : Work → V.Value → State
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

  closeAttempt : Script State → Script State
  closeAttempt next = ask stopTool (λ _ → ask releaseBackend (λ _ → next))

  afterCleanup : Work → Policy.Obstacle → String → Error → Script State
  afterCleanup w obstacle reason failure = done (finished (outcome
    (record (R.captureSource (Error.source failure) (Work.report w))
      { blockReason = just (toList reason) ; failureDetail = just (Error.detail failure) })
    (just obstacle)))

  interrupted : Work → Policy.Obstacle → String → Error → Script State
  interrupted w obstacle reason failure = closeAttempt (afterCleanup w obstacle reason failure)

  endsAfterCleanup : ∀ w obstacle reason problem events result →
    Runs (interrupted w obstacle reason problem) events result →
    events ≡ ((stopTool , tt) ∷ (releaseBackend , tt) ∷ [])
  endsAfterCleanup w obstacle reason problem ._ result
    (replied _ _ tt (replied _ _ tt (returned _))) = refl

  settled : Work → Script State
  settled w = done (finished (outcome (Work.report w) nothing))

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

  readbackUnavailable : Work → Error → Script State
  readbackUnavailable w failure =
    firstDiagnostic w (toList "review readback") (Error.detail failure) (Error.source failure) >>= λ recorded →
    interrupted recorded (Policy.toolStopped (Error.detail failure)) "tool_error" failure

  afterObservation : Work → Reply observe → Script State
  afterObservation w (inj₁ failure) = readbackUnavailable w failure
  afterObservation w (inj₂ snapshot) with Observation.observe pin snapshot
  ... | Observation.unavailable = readbackUnavailable w (error (toList "Review readback unavailable") nothing)
  ... | Observation.malformed failure = readbackUnavailable w (error (Display.fault display failure) nothing)
  ... | Observation.found _ _ (Observation.pending _ _ _) = done (loop w)
  ... | Observation.found _ _ (Observation.confirmed _) = settled w
  ... | Observation.found _ _ (Observation.corrected _ _) = settled w

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
  ... | true = ask (prepareCorrection (Work.lastRejection w)) λ where
    (just draft) → done (correcting w draft)
    nothing → firstDiagnostic w (toList "review_experience")
      (submissionDetail w) nothing >>= λ recorded →
      interrupted recorded (Policy.noSubmission (submissionDetail w)) "review_requires_repair"
        (error (submissionDetail w) nothing)

  afterDone : Work → Reply observe → Script State
  afterDone w (inj₁ failure) = readbackUnavailable w failure
  afterDone w (inj₂ snapshot) with Observation.observe pin snapshot
  ... | Observation.unavailable =
    readbackUnavailable w (error (toList "The selected experience is unavailable for review confirmation.") nothing)
  ... | Observation.malformed failure =
    readbackUnavailable w (error (Display.fault display failure) nothing)
  ... | Observation.found _ _ (Observation.pending _ _ _) = missingSubmission w
  ... | Observation.found _ _ (Observation.confirmed _) =
    settled w
  ... | Observation.found _ _ (Observation.corrected _ _) =
    settled w

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
  infrastructure w name failure = closeAttempt (
    firstDiagnostic w name (Error.detail failure) (Error.source failure) >>= λ recorded →
    afterCleanup recorded (Policy.toolStopped (Error.detail failure)) "tool_error" failure)

  alreadyExplained : Work → Text → Text → Bool
  alreadyExplained w name detail = any (λ { (previousName , previousDetail) →
    does (name ≟Text previousName) ∧ does (detail ≟Text previousDetail) }) (Work.sentCorrections w)

  correct : Work → Text → Error → V.Value → Script State
  correct w name problem guidance with alreadyExplained w name (Error.detail problem)
  ... | true = interrupted w (Policy.noSubmission (Error.detail problem)) "tool_rejected" problem
  ... | false = done (loop (record w
      { sentCorrections = (name , Error.detail problem) ∷ Work.sentCorrections w
      ; last = just guidance
      ; lastRejection = just (rejection name (Error.detail problem) (Error.source problem))
      ; submissionRequested = false }))

  inputRejected : Work → Text → Scoped.Failure → Text → Script State
  inputRejected w name failure message = correct w name (scopedError failure)
    (feedback "invalid_tool_arguments" message
      "Correct the indicated arguments and resubmit. If the intended value is unclear, ask the user.")

  data Continues : State → Set where
    continue : ∀ work → Continues (loop work)
    restartFromSource : ∀ report detail → Continues (finished (outcome report (just (Policy.noSubmission detail))))

  correctionContinues : ∀ w name failure message events result →
    Runs (inputRejected w name failure message) events result → Continues result
  correctionContinues w name failure message events result execution
    with alreadyExplained w name (Error.detail (scopedError failure))
  ... | false with execution
  ...   | returned _ = continue _
  correctionContinues w name failure message events result execution | true with execution
  ... | replied _ _ tt (replied _ _ tt (returned _)) = restartFromSource _ _

  ordinaryFailure : Work → Text → Scoped.Failure → Script State
  ordinaryFailure w name (Scoped.needsUserDecision detail) =
    firstDiagnostic w name detail nothing >>= λ recorded →
      interrupted recorded (Policy.userDecision detail) "needs_input" (error detail nothing)
  ordinaryFailure w name failure with rejectionMessage failure
  ... | just message = inputRejected w name failure message
  ... | nothing = infrastructure w name (scopedError failure)

  conflict : Work → Text → Text → Script State
  conflict w name detail = correct w name (error detail nothing) candidateFeedback

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

  -- Host-produced corrections enter the same validation and feedback path.
  -- Their receipts cannot directly settle a revision or open a repair case.
  correctedSubmission : Work → V.Value → Script State
  correctedSubmission w arguments = attempt w (toList "review_experience") arguments

  correctedRejectionContinues : ∀ w failure message events result →
    Runs (inputRejected w (toList "review_experience") failure message) events result →
    Continues result
  correctedRejectionContinues w = correctionContinues w (toList "review_experience")

  newRejectionReplacesExplanation : ∀ w name problem guidance →
    alreadyExplained w name (Error.detail problem) ≡ false →
    Σ Work (λ updated →
      correct w name problem guidance ≡ done (loop updated) ×
      Work.lastRejection updated ≡
        just (rejection name (Error.detail problem) (Error.source problem)) ×
      Work.submissionRequested updated ≡ false)
  newRejectionReplacesExplanation w name problem guidance fresh rewrite fresh =
    _ , refl , refl , refl

  correctedResponseRequiresReadback : ∀ w value →
    afterTool w (toList "review_experience") (inj₂ value) ≡
      ask observe (afterObservation (record w { last = just value }))
  correctedResponseRequiresReadback w value = refl

  malformedAttempt : Work → Text → Source.Failure → Script State
  malformedAttempt w name source = correct w name (error (Source.display source) (just source))
    (feedback "invalid_tool_arguments" (Source.Failure.detail source)
      "Correct the tool arguments using the supplied schema and resend the call.")

  afterModel : Work → Answer → Script State
  afterModel w (backendError failure) =
    interrupted w (Policy.modelStopped (Error.detail failure) nothing) "backend_error" failure
  afterModel w (backendUnavailable failure) =
    interrupted w (Policy.backendUnavailable (Error.detail failure)) "backend_configuration" failure
  afterModel w (providerWaiting failure signal) =
    interrupted w (Policy.modelStopped (Error.detail failure) (just signal)) "provider_unavailable" failure
  afterModel w (action modelDone) = ask observe (afterDone w)
  afterModel w (action (tool name arguments)) = attempt w name arguments
  afterModel w (action (malformedTool name source)) = malformedAttempt w name source

  data Step : Set where
    internal : State → Step
    external : (effect : Effect) → (Reply effect → State) → Step
    stopped : Outcome → Step

  next : State → Step
  next (loop w) = external (nextModel (Work.last w)) (λ reply → executing (afterModel w reply))
  next (correcting w arguments) = internal (executing (correctedSubmission w arguments))
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
  start report = loop (work report [] nothing nothing false)
