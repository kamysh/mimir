{-# OPTIONS --safe #-}
-- The original graph determines the numerical inputs. An actual solver
-- report is checked, never assumed correct or supplied as an expected answer.
module Mimir.IntendedIntervention where

open import Data.Float.Base using (Float)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.ApplicationStore as Store
import Mimir.InferenceStorageBinding as Inference
import Mimir.IntendedPreparation as Preparation
import Mimir.PosteriorComputation as Posterior
import Mimir.PublicInput as Fields
import Mimir.PublicRequest as Public
import Mimir.RecordDecoding as Record
import Mimir.StandardLibrary as Library
import Mimir.OperationControls as Controls
import Mimir.StructuredValue as Wire
import Mimir.Validation as Validation
import Mimir.ToolCatalog as Tools

module Evaluate (library : Library.Contract) (postgres : Controls.PostgreSQL)
  (databaseSum : List Float → Float) where
  module Base = Preparation.Evaluate library postgres using
    (Expected; expected; numericalReadback; requestCorrection)
  module Decode = Public.Decode library
  module N = Inference.NumericalOutcome databaseSum using
    (Request; Context; Result; intervention; prepare; unavailable)

  Expected = Base.Expected N.Result
  Evaluation = Preparation.ObservationError ⊎ Expected

  record Observations : Set where
    field snapshotRead : Maybe ⊤
          report : Maybe Posterior.CalculationReport

  missing : String → Preparation.ObservationError
  missing receiptField = Preparation.observationError (Validation.fault
    (Validation.key "observations" ∷ Validation.key receiptField ∷ []) Validation.missingField
    "Capture this intervention's actual acknowledged snapshot/calculation report for the same attempt. Do not invent a read, posterior values or solver success, or report missing oracle input as a product correction.")

  returned : Store.World → N.Result → Expected
  returned before result = Base.expected before (just result) (Base.numericalReadback databaseSum result)

  -- The captured report fills the existing module dependency solely to reuse
  -- its pure report checker. No solver is run and no correctness is assumed.
  fromReport : N.Context → Posterior.CalculationReport → N.Result
  fromReport selected actual = Checked.fromReport selected actual
    where
    module Checked = Inference.InterventionRecovery databaseSum (λ _ _ _ _ → actual)
      using (fromReport)

  prepared : N.Request → Store.World → Observations → Evaluation
  prepared requested before observed with N.prepare requested before
  ... | inj₁ issue = inj₂ (returned before (N.unavailable issue))
  ... | inj₂ selected with Observations.report observed
  ... | nothing = inj₁ (missing "calculation_report")
  ... | just actual = inj₂ (returned before (fromReport selected actual))

  query : N.Request → Store.World → Observations → Evaluation
  query requested before observed with Observations.snapshotRead observed
  ... | nothing = inj₁ (missing "snapshot_read")
  ... | just tt = prepared requested before observed

  request : Wire.Object.View → Validation.Fault ⊎ N.Request
  request fields = Record._>>=_ (Fields.required "id" (Fields.readUUID library) fields) λ identity →
    Record.mapResult (N.intervention identity) (Fields.required "value" Decode.float fields)

  afterRequest : Validation.Fault ⊎ N.Request → Store.World → Observations → Evaluation
  afterRequest (inj₁ fault) before observed = inj₂ (Base.expected before nothing (Base.requestCorrection fault))
  afterRequest (inj₂ requested) before observed = query requested before observed

  evaluate : Wire.Value → Store.World → Observations → Evaluation
  evaluate raw before observed with Decode.readInvocation Tools.queryIntervention raw
  ... | inj₁ fault = inj₂ (Base.expected before nothing (Base.requestCorrection fault))
  ... | inj₂ admitted = afterRequest
    (request (Wire.Object.normalize (Decode.Invocation.suppliedFields admitted))) before observed

  malformedRequestDoesNotEnterBody : ∀ raw before observed fault →
    Decode.readInvocation Tools.queryIntervention raw ≡ inj₁ fault →
    evaluate raw before observed ≡ inj₂ (Base.expected before nothing (Base.requestCorrection fault))
  malformedRequestDoesNotEnterBody raw before observed fault rejected rewrite rejected = refl

  unavailableNeedsNoReport : ∀ requested before observed issue → N.prepare requested before ≡ inj₁ issue →
    prepared requested before observed ≡ inj₂ (returned before (N.unavailable issue))
  unavailableNeedsNoReport requested before observed issue unavailable rewrite unavailable = refl

  missingSnapshotIsOracleInputError : ∀ requested before observed → Observations.snapshotRead observed ≡ nothing →
    query requested before observed ≡ inj₁ (missing "snapshot_read")
  missingSnapshotIsOracleInputError requested before observed absent rewrite absent = refl

  KeepsWorld : Store.World → Evaluation → Set
  KeepsWorld before (inj₁ missingObservation) = ⊤
  KeepsWorld before (inj₂ result) = Base.Expected.world result ≡ before

  preparedKeepsWorld : ∀ requested before observed → KeepsWorld before (prepared requested before observed)
  preparedKeepsWorld requested before observed with N.prepare requested before
  ... | inj₁ issue = refl
  ... | inj₂ selected with Observations.report observed
  ... | nothing = tt
  ... | just actual = refl

  queryKeepsWorld : ∀ requested before observed → KeepsWorld before (query requested before observed)
  queryKeepsWorld requested before observed with Observations.snapshotRead observed
  ... | nothing = tt
  ... | just tt = preparedKeepsWorld requested before observed

  afterRequestKeepsWorld : ∀ received before observed → KeepsWorld before (afterRequest received before observed)
  afterRequestKeepsWorld (inj₁ fault) before observed = refl
  afterRequestKeepsWorld (inj₂ requested) before observed = queryKeepsWorld requested before observed

  neverChangesWorld : ∀ raw before observed → KeepsWorld before (evaluate raw before observed)
  neverChangesWorld raw before observed with Decode.readInvocation Tools.queryIntervention raw
  ... | inj₁ fault = refl
  ... | inj₂ admitted = afterRequestKeepsWorld
    (request (Wire.Object.normalize (Decode.Invocation.suppliedFields admitted))) before observed
