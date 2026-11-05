{-# OPTIONS --safe #-}
-- One selected revision in the native runner. The account is shared with the
-- surrounding batch. Model replies, database reads and durable diagnostic
-- writes are separate effects; none can stand in for another's receipt.
module Mimir.JudgeRevision where

open import Data.Bool using (Bool; true; false; not)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String; toList)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
open import Mimir.Bits using (Byte)
import Mimir.Effects as Effects
import Mimir.JudgeAccounting as Budget
import Mimir.ProviderQueue as Queue
import Mimir.JudgeRevisionPolicy as Policy
import Mimir.JudgeScopedTools as Scoped
import Mimir.ReviewObservation as Observation
import Mimir.BatchReport as Batch
import Mimir.JudgeStateRecords as Records
import Mimir.JudgeBatchReadback as Readback
import Mimir.SourceFailure as Source
import Mimir.DiagnosticText as Bounded
import Mimir.StructuredValue as V
import Mimir.PublicEncoding as Encoding
import Mimir.StandardLibrary as Conversion
import Mimir.Validation as Validation
import Mimir.JudgePrompt as Prompt

module R = Records.Over ℕ

-- JSON rendering and error display are standard-library boundaries. The raw
-- value is retained until source capture; only the diagnostic detail is sent
-- back to the model, never the excerpt or MCP application error text.
record Display : Set where
  field json : V.Value → Text; bytes : V.Value → List Byte
        fault : Validation.Fault → Text

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
  (display : Display) (initial : Budget.Counts)
  (selected : Observation.Snapshot) where

  module Scope = Scoped.For conversion format selected
  pin = Observation.pinSnapshot selected
  identity = Observation.Pin.identity pin

  record Work : Set where
    constructor work
    field account : Queue.Account initial; report : R.Report
          policy : Policy.State; last : Maybe V.Value; lastRejection : Maybe Rejection

  record Outcome : Set where
    constructor outcome
    field account : Queue.Account initial; report : R.Report; failed fatal : Bool

  data Effect : Set where
    willCallModel : Effect
    nextModel : Maybe V.Value → Effect
    hostTool : Scoped.Effect → Effect
    observe : Effect
    clock : Effect
    appendTrace : ℕ → R.Event → Effect

  Reply : Effect → Set
  Reply willCallModel = Bool
  Reply (nextModel last) = Answer
  Reply (hostTool request) = Scoped.Reply request
  Reply observe = Error ⊎ Maybe Observation.Snapshot
  Reply clock = Maybe ℕ
  Reply (appendTrace id event) = Text ⊎ ⊤
  module P = Effects.Protocol Effect Reply
  open P

  data State : Set where
    loop : Work → State
    executing : Script State → State
    finished : Outcome → State

  fatal : Work → Text → Error → State
  fatal w reason failure = finished (outcome (Work.account w)
    (record (R.captureSource (Error.source failure) (Work.report w))
      { status = toList "blocked" ; blockReason = just reason
      ; failureDetail = just (Bounded.bounded 512 (Error.detail failure)) }) true true)

  trace : Work → String → Maybe Text → Maybe Text → Script State → Script State
  trace w kind name detail next with R.Report.diagnosticsId (Work.report w)
  ... | nothing = next
  ... | just id = ask clock (λ observed →
    ask (appendTrace id (R.newEvent observed identity (toList kind)
      (Budget.Counts.models (Queue.Account.totals (Work.account w)))
      (Budget.Counts.tools (Queue.Account.totals (Work.account w))) name detail)) λ where
        (inj₁ failure) → done (fatal w (toList "diagnostics_write_error") (error failure nothing))
        (inj₂ tt) → next)

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
  ... | Policy.retained retained = done (finished (outcome (Work.account w)
      (record (Work.report w) { deferredReviews = map
        (λ d → R.deferred (Observation.Deferred.identity d) (Observation.Deferred.revision d)) retained })
      (Policy.State.failed (Work.policy w)) false))

  afterRejection : Work → Script State
  afterRejection w with Policy.shouldDefer (Work.policy w)
  ... | false = deferred w
  ... | true = firstDiagnostic w (toList "review_experience") detail nothing >>= deferred
    where
    detail : Text
    detail with Policy.State.lastConflict (Work.policy w)
    ... | just message = message
    ... | nothing = toList "review correction was not confirmed"

  end : Work → Script State
  end w with Policy.State.settled (Work.policy w) | Work.lastRejection w
  ... | true | _ = afterRejection w
  ... | false | nothing = afterRejection w
  ... | false | just rejected = firstDiagnostic w (Rejection.name rejected)
      (Rejection.detail rejected) (Rejection.source rejected) >>= λ updated →
      afterRejection (record updated { report = reason (Work.report updated) })
    where
    reason : R.Report → R.Report
    reason r with R.Report.blockReason r
    ... | just _ = r
    ... | nothing = record r { blockReason = just (toList "tool_rejected") }

  conditional : Work → Policy.Event → String → Maybe Text → Maybe Source.Failure → Work
  conditional w event reason detail source with Policy.State.conflicts (Work.policy w)
  ... | suc _ = record w { policy = Policy.Step.state (Policy.step (Work.policy w) event) }
  ... | zero = record w
    { policy = Policy.Step.state (Policy.step (Work.policy w) event)
    ; report = record (R.captureSource source (Work.report w))
      { blockReason = just (toList reason) ; failureDetail = Data.Maybe.map (Bounded.bounded 512) detail } }

  sourceError : String → V.Value → Validation.Fault → Error
  sourceError stage value failure = error (Source.display source) (just source)
    where source = Source.Current.input conversion (toList stage) (Display.bytes display value) (Display.fault display failure)

  scopedError : Scoped.Failure → Error
  scopedError (Scoped.rejected detail) = error detail nothing
  scopedError (Scoped.invalidResponse detail) = error detail nothing
  scopedError (Scoped.transport detail) = error detail nothing
  scopedError (Scoped.sourceFailure source) = error (Source.display source) (just source)
  scopedError (Scoped.application detail) = error detail nothing
  scopedError (Scoped.candidateConflict detail) = error detail nothing
  scopedError (Scoped.malformedReview value failure) = sourceError "invalid review arguments" value failure
  scopedError (Scoped.malformedState value failure) = sourceError "invalid experience state" value failure
  scopedError (Scoped.invalidReviewSchema failure) = error (Display.fault display failure ++ toList ". " ++
    Prompt.evidenceGuidance (Display.json display) (Observation.Snapshot.experience selected)) nothing

  rejectionMessage : Scoped.Failure → Maybe Text
  rejectionMessage (Scoped.rejected detail) = just detail
  rejectionMessage (Scoped.application _) = just (toList "Mimir rejected this tool call. Check the tool schema and arguments.")
  rejectionMessage (Scoped.malformedReview value failure) = just (Display.fault display failure)
  rejectionMessage (Scoped.invalidReviewSchema failure) = just (Error.detail (scopedError (Scoped.invalidReviewSchema failure)))
  rejectionMessage _ = nothing

  afterObservation : Work → Reply observe → Script State
  afterObservation w (inj₁ failure) = done (fatal w (toList "mcp_or_configuration_error") failure)
  afterObservation w (inj₂ snapshot) with Observation.observe pin snapshot
  ... | Observation.malformed failure = done (fatal w (toList "mcp_or_configuration_error")
      (error (Display.fault display failure) nothing))
  ... | receipt with Policy.step (Work.policy w) (Policy.reviewed (Batch.label receipt))
  ...   | Policy.mkStep next Policy.continueRevision = done (loop (record w { policy = next }))
  ...   | Policy.mkStep next _ = end (record w { policy = next })

  infrastructure : Work → Text → Error → Script State
  infrastructure w name failure = trace w "tool_error" (just name) (just (Error.detail failure))
    (ask clock (λ observed → end (record w
      { policy = Policy.Step.state (Policy.step (Work.policy w) Policy.toolInfrastructureError)
      ; report = record (R.captureSource (Error.source failure) (Work.report w))
        { blockReason = just (toList "tool_error")
        ; diagnostic = just (R.newDiagnostic observed identity name (Error.detail failure)) } })))

  inputRejected : Work → Text → Scoped.Failure → Text → Script State
  inputRejected w name failure message = trace w "tool_rejection" (just name) (just (Error.detail diagnostic))
    (done (loop (record w
      { policy = Policy.Step.state (Policy.step (Work.policy w) (Policy.inputRejected message))
      ; last = just (feedback "invalid_tool_arguments" message
          "Correct the tool arguments and resubmit the request. The rejected call changed nothing.")
      ; lastRejection = just (rejection name (Bounded.bounded 512 (Error.detail diagnostic)) (Error.source diagnostic)) })))
    where diagnostic = scopedError failure

  ordinaryFailure : Work → Text → Scoped.Failure → Script State
  ordinaryFailure w name failure with rejectionMessage failure
  ... | just message = inputRejected w name failure message
  ... | nothing = infrastructure w name (scopedError failure)

  conflict : Work → Text → Text → Script State
  conflict w name detail with Policy.step (Work.policy w) (Policy.candidateConflict detail)
  ... | Policy.mkStep next Policy.retryCandidate = trace w "candidate_conflict" (just name) (just detail)
      (done (loop (record w { policy = next ; last = just candidateFeedback })))
  ... | Policy.mkStep next _ = trace w "candidate_conflict" (just name) (just detail)
      (end (record w { policy = next }))

  afterTool : Work → Text → Scoped.Failure ⊎ V.Value → Script State
  afterTool w name (inj₁ (Scoped.candidateConflict detail)) with does (name ≟Text toList "review_experience")
  ... | true = conflict w name detail
  ... | false = ordinaryFailure w name (Scoped.candidateConflict detail)
  afterTool w name (inj₁ failure) = ordinaryFailure w name failure
  afterTool w name (inj₂ value) = trace w "tool_result" (just name) (just (Display.json display value)) next
    where
    updated = record w { last = just value }
    next : Script State
    next with does (name ≟Text toList "review_experience")
    ... | true = ask observe (afterObservation updated)
    ... | false = done (loop updated)

  attempt : Work → Text → V.Value → Script State
  attempt w name arguments = fromScoped (Scope.run name arguments) >>=
    afterTool (record w { account = Queue.charge (Work.account w) Budget.tool }) name

  malformedAttempt : Work → Text → Source.Failure → Script State
  malformedAttempt w name source = done (loop (record w
    { account = Queue.charge (Work.account w) Budget.tool
    ; last = just (feedback "invalid_tool_arguments" (Source.Failure.detail source)
        "Correct the tool arguments using the supplied schema and resend the call.")
    ; lastRejection = just (rejection name (Source.display source) (just source)) }))

  afterModel : Work → Answer → Script State
  afterModel w (backendError failure) = trace w "model_error" nothing (just (Error.detail failure))
    (end (conditional w Policy.modelError "backend_error" (just (Error.detail failure)) (Error.source failure)))
  afterModel w (action modelDone) = trace w "model_done" nothing nothing
    (end (record w { policy = Policy.Step.state (Policy.step (Work.policy w) Policy.modelDone) }))
  afterModel w (action (tool name arguments)) = trace w "tool_request" (just name)
    (just (Display.json display arguments)) (attempt w name arguments)
  afterModel w (action (malformedTool name source)) = trace w "tool_parse_rejection" (just name)
    (just (Source.Failure.excerpt source)) (malformedAttempt w name source)

  provider : Work → Script State
  provider w = ask (nextModel (Work.last w)) (afterModel w)

  admitModel : Work → Bool → Script State
  admitModel w false = provider w
  admitModel w true = trace updated "model_request" nothing
    (Data.Maybe.map (Display.json display) (Work.last w)) (provider updated)
    where updated = record w { account = Queue.charge (Work.account w) Budget.provider }

  data Step : Set where
    internal : State → Step
    external : (effect : Effect) → (Reply effect → State) → Step
    stopped : Outcome → Step

  next : State → Step
  next (loop w) = external willCallModel (λ reply → executing (admitModel w reply))
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

  start : Queue.Account initial → R.Report → State
  start currentAccount report = loop (work currentAccount report Policy.initial nothing nothing)

  -- Applies to every outcome, including fatal diagnostic or transport errors.
  -- Account construction itself contains the original, shared charge trace.
  providerRequestsCounted : ∀ result →
    Budget.Counts.models (Queue.Account.totals (Outcome.account result)) ≡
    Budget.count Budget.modelCost (Queue.Account.charges (Outcome.account result)) + Budget.Counts.models initial
  providerRequestsCounted result = Queue.requestsCounted (Outcome.account result)

  toolAttemptsCounted : ∀ result →
    Budget.Counts.tools (Queue.Account.totals (Outcome.account result)) ≡
    Budget.count Budget.toolCost (Queue.Account.charges (Outcome.account result)) + Budget.Counts.tools initial
  toolAttemptsCounted result = Queue.attemptsCounted (Outcome.account result)
