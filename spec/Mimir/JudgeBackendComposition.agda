{-# OPTIONS --safe #-}
-- Judge effects are related to the calling service and to the lifetime of its
-- tool client. A model provider's internal protocol is an external dependency.
module Mimir.JudgeBackendComposition where

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
import Mimir.JudgeServiceBinding as Service
import Mimir.JudgeScopedTools as Scoped
import Mimir.ToolCatalog as Catalog
import Mimir.ApplicationProtocol as Application
import Mimir.ReviewObservation as Observation
import Mimir.StructuredValue as V
import Mimir.Text as Text
open import Data.String using (toList)
import Mimir.JudgeMcpLifecycle as Client

data BackendState : Set where
  harness : BackendState
  api : Config.Provider → BackendState
  unavailable : BackendState

module Bound (conversion : Conversion.Contract) (format : Encoding.Formatting)
  (display : Revision.Display) (environment : Application.Environment) (errors : Service.Display)
  (selected : Observation.Snapshot) where
  module T = Revision.Run conversion format display selected
  private
    module S = Service.Bind conversion format display errors environment

  data Ordinary : T.Effect → Set where
    clock : Ordinary T.clock
    reportTraceProblem : ∀ failure → Ordinary (T.reportTraceProblem failure)

  observation : Scoped.Failure ⊎ V.Value → Revision.Error ⊎ Maybe Observation.Snapshot
  observation (inj₁ failure) = inj₁ (T.scopedError failure)
  observation (inj₂ V.null) = inj₂ nothing
  observation (inj₂ value) with T.Scope.snapshot value
  ... | inj₁ failure = inj₁ (T.scopedError failure)
  ... | inj₂ selected = inj₂ (just selected)

  data Receipt : BackendState → (effect : T.Effect) → T.Reply effect → BackendState → Set where
    harnessResult : ∀ last result → Receipt harness (T.nextModel last) result harness
    apiResult : ∀ provider last result → Receipt (api provider) (T.nextModel last) result (api provider)
    unavailableResult : ∀ last → Receipt unavailable (T.nextModel last)
      (Revision.backendError (Revision.error (toList "configured backend adapter is not installed") nothing)) unavailable
    serviceCall : ∀ before id tool args reply → S.Receipt id tool args reply →
      Receipt before (T.hostTool (Scoped.call tool args)) reply before
    serviceObservation : ∀ before id reply →
      S.Receipt id Catalog.getExperience (T.Scope.byID T.Scope.canonicalID) reply →
      Receipt before T.observe (observation reply) before
    toolStopped : ∀ before client events →
      (proof : Client.Runs (Client.dropClient client) events (inj₂ tt)) →
      Receipt before T.stopTool tt before
    traceRecorded : ∀ before id kind name detail reply →
      Receipt before (T.appendTrace id kind name detail) reply before
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
  issued (toolStopped before ownedClient events proof) = Client.stoppedClient ownedClient events proof ∷ []
  issued (harnessResult _ _) = []
  issued (apiResult _ _ _) = []
  issued (unavailableResult _) = []
  issued (traceRecorded _ _ _ _ _ _) = []
  issued (ordinary _ _ _ _) = []

  traceIssued : ∀ {backend before events after final} → Trace backend before events after final → List Client.Issued
  traceIssued empty = []
  traceIssued (internal next execution) = traceIssued execution
  traceIssued (external next receipt execution) = issued receipt ++ traceIssued execution

  runnerTrace : ∀ {backend before events after final} → Trace backend before events after final → T.Trace before events final
  runnerTrace empty = T.empty
  runnerTrace (internal next execution) = T.step (T.internalStep next) (runnerTrace execution)
  runnerTrace (external next receipt execution) = T.step (T.externalStep next _) (runnerTrace execution)
