{-# OPTIONS --safe #-}
-- Propagation intent determines the complete changed-belief reply and world.
-- No expected posterior values or successful report are oracle inputs.
module Mimir.IntendedPropagation where

open import Data.Float.Base using (Float)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.ApplicationStore as Store
import Mimir.PropagationRecovery as Propagation
import Mimir.GroundingRecovery as Grounding
import Mimir.PublicEncoding as Encoding
import Mimir.InferenceStorageBinding as Inference
import Mimir.IntendedPreparation as Preparation
import Mimir.OperationControls as Controls
import Mimir.PosteriorComputation as Posterior
import Mimir.PublicRequest as Public
import Mimir.RecoverableStoreStep as Step
import Mimir.StandardLibrary as Library
import Mimir.StructuredValue as Wire
import Mimir.Validation as Validation
import Mimir.ToolCatalog as Tools

module Evaluate (library : Library.Contract) (postgres : Controls.PostgreSQL)
  (format : Encoding.Formatting) (databaseSum : List Float → Float) where
  module Base = Preparation.Evaluate library postgres using
    (module C; module Read; Observations; Evaluation; Outcome; Expected; expected;
     requestCorrection; operationReadback; checkedPosteriorProblem)
  module Registration = Propagation.Registration library using (original; key)
  module Diagnostic = Grounding.Diagnostics databaseSum using
    (Diagnostic; requestFault; preparation; rejectedReport; repeated)
  module N = Inference.NumericalOutcome databaseSum using (prepare; propagate)
  module Decode = Public.Decode library

  Body = Step.Result Diagnostic.Diagnostic
  Expected = Base.Expected Body
  Evaluation = Preparation.ObservationError ⊎ Expected

  record Observations : Set where
    field publicationTime : Maybe ℤ
          report : Maybe Posterior.CalculationReport

  missing : String → Preparation.ObservationError
  missing receiptField = Preparation.observationError (Validation.fault
    (Validation.key "observations" ∷ Validation.key receiptField ∷ []) Validation.missingField
    "Capture this propagation's actual locked PostgreSQL publication clock/calculation report for the same token and attempt. Do not invent time, posterior values or solver success, or turn missing oracle input into a product correction. Saved results need no fresh receipts.")

  reflected : ℕ → Store.World → Body → Expected
  reflected token after reply = Base.expected after (just reply) (Base.operationReadback (Base.Read.answer token after))

  refused : Store.World → Diagnostic.Diagnostic → Expected
  refused before diagnostic@(Diagnostic.requestFault fault) =
    Base.expected before (just (Step.needsInput diagnostic)) (Base.requestCorrection fault)
  refused before diagnostic = Base.expected before (just (Step.needsInput diagnostic))
    (Base.checkedPosteriorProblem databaseSum diagnostic)

  publication : ℕ → Store.World × Wire.Value → Expected
  publication token (changed , answer) = reflected token final (Step.done answer)
    where final = Store.saveAnswer (Store.saveAnswer changed token (Registration.key token) answer)
            token Step.resultKey answer

  checked : ℕ → ℕ → ℤ → Store.World → Posterior.CalculationReport → Expected
  checked token identity time before actual with proj₁ (Business.checked time identity before)
    where module Business = Propagation.Business format databaseSum (λ _ _ _ _ → actual)
  ... | inj₁ diagnostic = refused before diagnostic
  ... | inj₂ changed = publication token changed

  -- Missing seeds and invalid stored inputs refuse before any report is
  -- required; otherwise the actual report is checked by the existing intent.
  atTime : ℕ → ℕ → ℤ → Store.World → Observations → Evaluation
  atTime token identity time before observed with N.prepare (N.propagate identity) before
  ... | inj₁ issue = inj₂ (refused before (Diagnostic.preparation issue))
  ... | inj₂ selected with Observations.report observed
  ... | nothing = inj₁ (missing "calculation_report")
  ... | just actual = inj₂ (checked token identity time before actual)

  single : ℕ → ℕ → Store.World → Observations → Evaluation
  single token identity before observed with Store.lookupCancellation before token
  ... | just cancelled = inj₂ (reflected token before (Step.cancelled cancelled))
  ... | nothing with Store.lookupSaved before token (Registration.key token) | Store.lookupSaved before token Step.resultKey
  ... | just saved | just final = inj₂ (reflected token before (Step.done saved))
  ... | just _ | nothing = inj₂ (reflected token before Step.needsRecovery)
  ... | nothing | just _ = inj₂ (reflected token before Step.needsRecovery)
  ... | nothing | nothing with Observations.publicationTime observed
  ... | nothing = inj₁ (missing "posterior_publication_clock")
  ... | just time = atTime token identity time before observed

  business : ℕ → Store.World → Observations → Evaluation
  business token before observed with Registration.original token (Step.registration before)
  ... | inj₁ fault = inj₂ (refused before (Diagnostic.requestFault fault))
  ... | inj₂ (identity , reservedAt) = single token identity before observed

  unavailableNeedsNoReport : ∀ token identity time before observed issue →
    N.prepare (N.propagate identity) before ≡ inj₁ issue →
    atTime token identity time before observed ≡ inj₂ (refused before (Diagnostic.preparation issue))
  unavailableNeedsNoReport token identity time before observed issue unavailable rewrite unavailable = refl

  savedResultNeedsNoFreshReceipts : ∀ token identity before observed saved final →
    Store.lookupCancellation before token ≡ nothing →
    Store.lookupSaved before token (Registration.key token) ≡ just saved →
    Store.lookupSaved before token Step.resultKey ≡ just final →
    single token identity before observed ≡ inj₂ (reflected token before (Step.done saved))
  savedResultNeedsNoFreshReceipts token identity before observed saved final active stored completed
    rewrite active | stored | completed = refl

  module With (observed : (call : Base.C.Call) → Base.Observations call)
    (captured : Base.C.Call → Observations) where
    module Metadata = Preparation.Evaluate.With library postgres observed using (admitted)

    prepared : Base.C.Call → Base.Outcome → Evaluation
    prepared call (before , Base.C.needsInput fault) = inj₂ (Base.expected before nothing (Base.requestCorrection fault))
    prepared call (before , Base.C.returned outcome) = inj₂ (Base.expected before nothing (Base.operationReadback outcome))
    prepared call (before , Base.C.ready context) = business (Base.C.Call.token call) before (captured call)

    afterMetadata : Base.C.Call → Base.Evaluation → Evaluation
    afterMetadata call (inj₁ missingObservation) = inj₁ missingObservation
    afterMetadata call (inj₂ outcome) = prepared call outcome

    evaluate : Wire.Value → Store.World → Evaluation
    evaluate raw before with Decode.readInvocation Tools.propagateFrom raw
    ... | inj₁ fault = inj₂ (Base.expected before nothing (Base.requestCorrection fault))
    ... | inj₂ admitted = afterMetadata call (Metadata.admitted call before)
      where call = Base.C.admittedWrite Tools.propagateFrom raw refl admitted

    malformedRequestDoesNotEnterBody : ∀ raw before fault →
      Decode.readInvocation Tools.propagateFrom raw ≡ inj₁ fault →
      evaluate raw before ≡ inj₂ (Base.expected before nothing (Base.requestCorrection fault))
    malformedRequestDoesNotEnterBody raw before fault rejected rewrite rejected = refl
