{-# OPTIONS --safe #-}
-- Selection and final readback share the actual public MCP service. Retained
-- deferrals come from the persisted status report; raw parse failures retain
-- their original bounded source evidence for final diagnostics.
module Mimir.JudgeBatchServiceBinding where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
import Mimir.UUIDGroups as UUIDValue
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Data.String using (String; toList)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Mimir.Text using (Text)
import Mimir.StandardLibrary as Conversion
import Mimir.PublicEncoding as Encoding
import Mimir.ApplicationProtocol as Application
import Mimir.JudgeRevision as Revision
import Mimir.JudgeServiceBinding as Service
import Mimir.JudgeScopedTools as Scope
import Mimir.JudgeSelection as Selection
import Mimir.JudgeBatchReadback as Readback
import Mimir.JudgeStateOperations as State
import Mimir.LearningStateWire as Wire
import Mimir.ReviewObservation as Observation
import Mimir.RecordDecoding as Decode
import Mimir.StructuredValue as V
import Mimir.ToolCatalog as Catalog
import Mimir.SourceFailure as Source
import Mimir.Validation as Validation
import Mimir.JudgeMcpLifecycle as Client

module Bound (conversion : Conversion.Contract) (format : Encoding.Formatting)
  (display : Revision.Display) (errors : Service.Display) (environment : Application.Environment)
  (sizeMaximum : ℕ) where
  private
    module S = Service.Bind conversion format display errors environment
    module W = Wire.Decode conversion sizeMaximum

  sourceError : String → V.Value → Validation.Fault → Revision.Error
  sourceError stage value failure = Revision.error (Source.display captured) (just captured)
    where captured = Source.Current.input conversion (toList stage) (Revision.Display.bytes display value)
            (Revision.Display.fault display failure)

  error : Scope.Failure → Revision.Error
  error (Scope.rejected detail) = Revision.error detail nothing
  error (Scope.needsUserDecision detail) = Revision.error detail nothing
  error (Scope.invalidResponse detail) = Revision.error detail nothing
  error (Scope.transport detail) = Revision.error detail nothing
  error (Scope.application detail) = Revision.error detail nothing
  error (Scope.candidateConflict detail) = Revision.error detail nothing
  error (Scope.sourceFailure captured) = Revision.error (Source.display captured) (just captured)
  error (Scope.malformedReview value failure) = sourceError "invalid review arguments" value failure
  error (Scope.malformedState value failure) = sourceError "invalid experience state" value failure
  error (Scope.invalidReviewSchema failure) = Revision.error (Revision.Display.fault display failure) nothing

  current : Scope.Failure ⊎ V.Value → Revision.Error ⊎ Maybe Observation.Snapshot
  current (inj₁ failure) = inj₁ (error failure)
  current (inj₂ V.null) = inj₂ nothing
  current (inj₂ value) with W.snapshot value
  ... | inj₁ failure = inj₁ (sourceError "invalid experience state" value failure)
  ... | inj₂ observedSnapshot = inj₂ (just observedSnapshot)

  pending : Scope.Failure ⊎ V.Value → Revision.Error ⊎ List Observation.Snapshot
  pending (inj₁ failure) = inj₁ (error failure)
  pending (inj₂ value) with Decode.readArray W.snapshot value
  ... | inj₁ failure = inj₁ (sourceError "invalid pending batch" value failure)
  ... | inj₂ snapshots = inj₂ snapshots

  previous : Text ⊎ Maybe State.R.Report → Revision.Error ⊎ List Observation.Deferred
  previous (inj₁ detail) = inj₁ (Revision.error detail nothing)
  previous (inj₂ nothing) = inj₂ []
  previous (inj₂ (just report)) = inj₂ (map (λ item → Observation.deferred
    (State.R.Deferred.identity item) (State.R.Deferred.revision item)) (State.R.Report.deferredReviews report))

  byID : UUIDValue.UUID → V.Value
  byID id = Encoding.object (("id" , V.string (Encoding.Formatting.uuidText format id)) ∷ [])
  pendingArgs : Maybe Text → Maybe ℕ → List UUIDValue.UUID → V.Value
  pendingArgs project limit excluded = Encoding.object
    (("exclude_ids" , V.array (map
      (λ id → V.string (Encoding.Formatting.uuidText format id)) excluded)) ∷ (selection limit Data.List.++ extra project))
    where
    selection : Maybe ℕ → List (String Data.Product.× V.Value)
    selection nothing = []
    selection (just count) = ("limit" , V.unsigned count) ∷ []
    extra : Maybe Text → List (String Data.Product.× V.Value)
    extra nothing = []
    extra (just value) = ("project" , V.string value) ∷ []

  data SelectionReceipt : (effect : Selection.Effect) → Selection.Reply effect → Set where
    retained : ∀ reply → SelectionReceipt Selection.previousDeferred (previous reply)
    observed : ∀ id requestID reply → S.Receipt requestID Catalog.getExperience (byID id) reply →
      SelectionReceipt (Selection.current id) (current reply)
    selected : ∀ project limit excluded requestID reply →
      S.Receipt requestID Catalog.pendingExperiences (pendingArgs project limit excluded) reply →
      SelectionReceipt (Selection.pending project limit excluded) (pending reply)

  readback : Revision.Error ⊎ Maybe Observation.Snapshot → Readback.Failure ⊎ Maybe Observation.Snapshot
  readback (inj₁ failure) = inj₁ (Readback.failure (Revision.Error.detail failure) (Revision.Error.source failure))
  readback (inj₂ observedSnapshot) = inj₂ observedSnapshot

  data ReadbackReceipt : (effect : Readback.Effect) → Readback.Reply effect → Set where
    clock : ∀ now → ReadbackReceipt Readback.clock now
    observed : ∀ pin requestID reply →
      S.Receipt requestID Catalog.getExperience (byID (Observation.Pin.identity pin)) reply →
      ReadbackReceipt (Readback.getExperience pin) (readback (current reply))

  selectionCalls : ∀ {effect reply} → SelectionReceipt effect reply → List Client.Issued
  selectionCalls (retained _) = []
  selectionCalls (observed _ _ _ receipt) = S.issued receipt ∷ []
  selectionCalls (selected _ _ _ _ _ receipt) = S.issued receipt ∷ []

  readbackCalls : ∀ {effect reply} → ReadbackReceipt effect reply → List Client.Issued
  readbackCalls (clock _) = []
  readbackCalls (observed _ _ _ receipt) = S.issued receipt ∷ []
