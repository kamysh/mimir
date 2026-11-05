{-# OPTIONS --safe #-}
-- Refinement receipts for the runner's model effects. will_call_model is the
-- adapter's actual queue predicate; successful/failed replies carry adapter
-- traces. Cancellation retains mutations already performed and drops any
-- subprocess group still owned according to spawn/reap receipts.
module Mimir.JudgeBackendComposition where

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤_)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.StandardLibrary as Conversion
import Mimir.PublicEncoding as Encoding
import Mimir.JudgeConfiguration as Config
import Mimir.JudgeRevision as Revision
import Mimir.JudgeHarnessAdapter as Harness
import Mimir.JudgeAPIAdapter as API
import Mimir.JudgeProcess as Process
import Mimir.JudgeServiceBinding as Service
import Mimir.JudgeScopedTools as Scoped
import Mimir.ToolCatalog as Catalog
import Mimir.ApplicationProtocol as Application
import Mimir.JudgeAccounting as Budget
import Mimir.ReviewObservation as Observation
import Mimir.ExperienceSchema as Experience
import Mimir.StructuredValue as V
import Mimir.Text as Text
open import Data.String using (toList)
import Mimir.JudgeStateOperations as State
import Mimir.UnixPath as Path
import Mimir.UUIDV4 as UUID
import Mimir.JudgeMcpLifecycle as Client

data BackendState : Set where
  harness : Harness.Adapter → BackendState
  api : Config.Provider → API.Adapter → BackendState
  unavailable : BackendState

answer : Revision.Error ⊎ Revision.Action → Revision.Answer
answer (inj₁ failureValue) = Revision.backendError failureValue
answer (inj₂ value) = Revision.action value

module Bound (conversion : Conversion.Contract) (format : Encoding.Formatting)
  (libraries : Harness.Libraries) (environment : Application.Environment) (errors : Service.Display) (config : Config.Llm) (program : Text.Text)
  (initial : Budget.Counts) (selected : Observation.Snapshot) (tools : List V.Value)
  (sizeMaximum : ℕ) (endian : UUID.Endian) (path : Path.Path) where
  private module Storage = State.Bound conversion sizeMaximum endian path
  module T = Revision.Run conversion format (Harness.Libraries.display libraries) initial selected
  private
    module H = Harness.Run conversion format libraries config program selected tools
    module A provider = API.Run conversion format libraries config provider selected tools
    module S = Service.Bind conversion format (Harness.Libraries.display libraries) errors environment
  identity = Experience.Experience.identity (Observation.Snapshot.experience selected)

  record HarnessInterruption (before : Harness.Adapter) (last : Maybe V.Value) : Set where
    constructor interruptedHarness
    field
      events : List H.P.Event
      process : Process.Spawn
      continuation : H.ProcessReceipt process → H.P.Script H.Result
      prefix : H.P.Prefix (H.start before last) events (H.P.ask (H.runProcess process) continuation)
      childEvents : List (Maybe Process.P.Event)
      childState : Process.State
      childPrefix : Process.Trace (Process.start process) childEvents childState
      cleanupEvents : List Process.P.Event
      cleaned : Process.P.Runs (Process.cancelOwned (Process.ownerAfter nothing childEvents)) cleanupEvents
        (Process.finished (inj₁ (Process.nativeFailure (toList "cancelled"))))

    -- Dropping the pending adapter future also drops RunDir. Removal is
    -- best effort, but invoking it is mandatory even when process cleanup fails.
    field
      directoryEvents : List H.P.Event
      directoryDropped : H.P.Runs
        (H.P.ask (H.removeRun (Process.Spawn.directory process)) (λ _ → H.P.done tt)) directoryEvents tt

  data Ordinary : T.Effect → Set where
    clock : Ordinary T.clock

  observation : Scoped.Failure ⊎ V.Value → Revision.Error ⊎ Maybe Observation.Snapshot
  observation (inj₁ failure) = inj₁ (T.scopedError failure)
  observation (inj₂ V.null) = inj₂ nothing
  observation (inj₂ value) with T.Scope.snapshot value
  ... | inj₁ failure = inj₁ (T.scopedError failure)
  ... | inj₂ selected = inj₂ (just selected)

  data Receipt : BackendState → (effect : T.Effect) → T.Reply effect → BackendState → Set where
    harnessCost : ∀ state → Receipt (harness state) T.willCallModel (Harness.willCallModel state identity) (harness state)
    apiCost : ∀ provider state → Receipt (api provider state) T.willCallModel (API.willCallModel state identity) (api provider state)
    unavailableCost : Receipt unavailable T.willCallModel true unavailable
    harnessResult : ∀ before last events result → H.P.Runs (H.start before last) events result →
      Receipt (harness before) (T.nextModel last) (answer (H.Result.answer result)) (harness (H.Result.state result))
    apiResult : ∀ provider before last events result →
      A.Trace provider (A.start provider before last) events (A.finished result) →
      Receipt (api provider before) (T.nextModel last) (answer (A.Outcome.answer result)) (api provider (A.Outcome.state result))
    harnessCancelled : ∀ before last (prefix : HarnessInterruption before last) →
      Receipt (harness before) (T.nextModel last)
        (Revision.backendError (Revision.error (toList "cancelled") nothing))
        (harness (H.observedState before (HarnessInterruption.events prefix)))
    unavailableResult : ∀ last → Receipt unavailable (T.nextModel last)
      (Revision.backendError (Revision.error (toList "configured backend adapter is not installed") nothing)) unavailable
    serviceCall : ∀ before id tool args reply → S.Receipt id tool args reply →
      Receipt before (T.hostTool (Scoped.call tool args)) reply before
    serviceObservation : ∀ before id reply →
      S.Receipt id Catalog.getExperience (T.Scope.byID T.Scope.canonicalID) reply →
      Receipt before T.observe (observation reply) before
    traceRecorded : ∀ before id event reply → Storage.Recorded id event reply →
      Receipt before (T.appendTrace id event) reply before
    ordinary : ∀ before effect reply → Ordinary effect → Receipt before effect reply before

  data Trace : BackendState → T.State → List (Maybe T.P.Event) → BackendState → T.State → Set where
    empty : ∀ {backend state} → Trace backend state [] backend state
    internal : ∀ {backend before middle after final events} →
      T.next before ≡ T.internal middle → Trace backend middle events after final →
      Trace backend before (nothing ∷ events) after final
    external : ∀ {backend before effect continuation reply middle after final events} →
      T.next before ≡ T.external effect continuation → Receipt backend effect reply middle →
      Trace middle (continuation reply) events after final →
      Trace backend before (just (effect , reply) ∷ events) after final

  issued : ∀ {before effect reply after} → Receipt before effect reply after → List Client.Issued
  issued (serviceCall before id tool args reply receipt) = S.issued receipt ∷ []
  issued (serviceObservation before id reply receipt) = S.issued receipt ∷ []
  issued (harnessCost _) = []
  issued (apiCost _ _) = []
  issued unavailableCost = []
  issued (harnessResult _ _ _ _ _) = []
  issued (apiResult _ _ _ _ _ _) = []
  issued (harnessCancelled _ _ _) = []
  issued (unavailableResult _) = []
  issued (traceRecorded _ _ _ _ _) = []
  issued (ordinary _ _ _ _) = []

  traceIssued : ∀ {backend before events after final} → Trace backend before events after final → List Client.Issued
  traceIssued empty = []
  traceIssued (internal next execution) = traceIssued execution
  traceIssued (external next receipt execution) = issued receipt ++ traceIssued execution

  runnerTrace : ∀ {backend before events after final} → Trace backend before events after final → T.Trace before events final
  runnerTrace empty = T.empty
  runnerTrace (internal next execution) = T.step (T.internalStep next) (runnerTrace execution)
  runnerTrace (external next receipt execution) = T.step (T.externalStep next _) (runnerTrace execution)
