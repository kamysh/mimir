{-# OPTIONS --safe #-}
-- Evidence intent and checked numerical consequences determine the world.
-- Tentative evidence changes never survive a refused calculation.
module Mimir.IntendedEvidence where

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
import Mimir.GroundingRecovery as Grounding
import Mimir.GroundingPublication as Ground
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
  (databaseSum : List Float → Float) where
  module Base = Preparation.Evaluate library postgres using
    (module C; module Read; Observations; Evaluation; Outcome; Expected; expected;
     requestCorrection; operationReadback; checkedPosteriorProblem)
  module Registration = Grounding.Registration Grounding.addition library using (original; key)
  module Diagnostic = Grounding.Diagnostics databaseSum using
    (Diagnostic; requestFault; preparation; rejectedReport; repeated)
  module N = Inference.NumericalOutcome databaseSum using (prepare; recompute)
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
    "Capture this evidence addition's actual locked PostgreSQL publication clock/calculation report for the same token and attempt. Do not invent time, posterior values or solver success, or turn missing oracle input into a product correction. Saved results need no fresh receipts.")

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

  checked : ℕ → Ground.Request → ℤ → Store.World → Posterior.CalculationReport → Expected
  checked token requested time before actual with proj₁ (Business.checked time requested before)
    where module Business = Grounding.Business databaseSum (λ _ _ _ _ → actual)
  ... | inj₁ diagnostic = refused before diagnostic
  ... | inj₂ changed = publication token changed

  -- Invalid references/weights and failed preparation need no fabricated
  -- calculation report, and never publish the tentative evidence change.
  atTime : ℕ → Ground.Request → ℤ → Store.World → Observations → Evaluation
  atTime token requested time before observed with Grounding.intendedEvidence requested before
  ... | inj₁ fault = inj₂ (refused before (Diagnostic.requestFault fault))
  ... | inj₂ proposed with N.prepare (N.recompute (Grounding.root requested ∷ [])) proposed
  ... | inj₁ issue = inj₂ (refused before (Diagnostic.preparation issue))
  ... | inj₂ selected with Observations.report observed
  ... | nothing = inj₁ (missing "calculation_report")
  ... | just actual = inj₂ (checked token requested time before actual)

  single : ℕ → Ground.Request → Store.World → Observations → Evaluation
  single token requested before observed with Store.lookupCancellation before token
  ... | just cancelled = inj₂ (reflected token before (Step.cancelled cancelled))
  ... | nothing with Store.lookupSaved before token (Registration.key token) | Store.lookupSaved before token Step.resultKey
  ... | just saved | just final = inj₂ (reflected token before (Step.done saved))
  ... | just _ | nothing = inj₂ (reflected token before Step.needsRecovery)
  ... | nothing | just _ = inj₂ (reflected token before Step.needsRecovery)
  ... | nothing | nothing with Observations.publicationTime observed
  ... | nothing = inj₁ (missing "posterior_publication_clock")
  ... | just time = atTime token requested time before observed

  business : ℕ → Store.World → Observations → Evaluation
  business token before observed with Registration.original token (Step.registration before)
  ... | inj₁ fault = inj₂ (refused before (Diagnostic.requestFault fault))
  ... | inj₂ (requested , reservedAt) = single token requested before observed

  invalidEvidenceNeedsNoReport : ∀ token requested time before observed fault →
    Grounding.intendedEvidence requested before ≡ inj₁ fault →
    atTime token requested time before observed ≡ inj₂ (refused before (Diagnostic.requestFault fault))
  invalidEvidenceNeedsNoReport token requested time before observed fault rejected rewrite rejected = refl

  unavailableNeedsNoReport : ∀ token requested time before observed proposed issue →
    Grounding.intendedEvidence requested before ≡ inj₂ proposed →
    N.prepare (N.recompute (Grounding.root requested ∷ [])) proposed ≡ inj₁ issue →
    atTime token requested time before observed ≡ inj₂ (refused before (Diagnostic.preparation issue))
  unavailableNeedsNoReport token requested time before observed proposed issue changed unavailable
    rewrite changed | unavailable = refl

  savedResultNeedsNoFreshReceipts : ∀ token requested before observed saved final →
    Store.lookupCancellation before token ≡ nothing →
    Store.lookupSaved before token (Registration.key token) ≡ just saved →
    Store.lookupSaved before token Step.resultKey ≡ just final →
    single token requested before observed ≡ inj₂ (reflected token before (Step.done saved))
  savedResultNeedsNoFreshReceipts token requested before observed saved final active stored completed
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
    evaluate raw before with Decode.readInvocation Tools.addEvidence raw
    ... | inj₁ fault = inj₂ (Base.expected before nothing (Base.requestCorrection fault))
    ... | inj₂ admitted = afterMetadata call (Metadata.admitted call before)
      where call = Base.C.admittedWrite Tools.addEvidence raw refl admitted

    malformedRequestDoesNotEnterBody : ∀ raw before fault →
      Decode.readInvocation Tools.addEvidence raw ≡ inj₁ fault →
      evaluate raw before ≡ inj₂ (Base.expected before nothing (Base.requestCorrection fault))
    malformedRequestDoesNotEnterBody raw before fault rejected rewrite rejected = refl
