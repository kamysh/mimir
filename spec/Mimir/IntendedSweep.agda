{-# OPTIONS --safe #-}
-- Sweep selection is computed from user policy and actual clocks on the
-- initial world, never supplied as an expected set or fixed by an aborted read.
module Mimir.IntendedSweep where

open import Data.Bool using (true; false)
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
import Mimir.BeliefDeletionRecovery as Deletion
import Mimir.GraphNumerics as Numeric
import Mimir.InferenceStorageBinding as Inference
import Mimir.IntendedPreparation as Preparation
import Mimir.OperationControls as Controls
import Mimir.PosteriorComputation as Posterior
import Mimir.PublicEncoding as Encoding
import Mimir.PublicRequest as Public
import Mimir.RecoverableStoreStep as Step
import Mimir.StandardLibrary as Library
import Mimir.StructuredValue as Wire
import Mimir.SweepRecovery as Sweep
import Mimir.Validation as Validation
import Mimir.ToolCatalog as Tools

module Evaluate (library : Library.Contract) (postgres : Controls.PostgreSQL)
  (format : Encoding.Formatting) (databaseSum : List Float → Float) where
  module Base = Preparation.Evaluate library postgres using
    (module C; module Read; Observations; Evaluation; Outcome; Expected; expected;
     requestCorrection; operationReadback; beliefDeletionProblem)
  module Registration = Sweep.Registration library
  module Diagnostic = Deletion.Diagnostics databaseSum using (Diagnostic; requestFault; preparation)
  module N = Inference.NumericalOutcome databaseSum using (prepare; recompute)
  module Decode = Public.Decode library

  Body = Step.Result Diagnostic.Diagnostic
  Expected = Base.Expected Body
  Evaluation = Preparation.ObservationError ⊎ Expected

  record Observations : Set where
    field currentPolicy : Maybe (Maybe Wire.Value)
          selectedAt publicationTime : Maybe ℤ
          report : Maybe Posterior.CalculationReport

  missing : String → Preparation.ObservationError
  missing receiptField = Preparation.observationError (Validation.fault
    (Validation.key "observations" ∷ Validation.key receiptField ∷ []) Validation.missingField
    "Capture this sweep's actual user-policy, PostgreSQL clock or calculation receipt for the same token and attempt. Do not invent a policy, time, selected set or posterior values, or turn missing oracle input into a product correction. Saved/refused work needs no unused fresh receipts.")

  reflected : ℕ → Store.World → Body → Expected
  reflected token after reply = Base.expected after (just reply) (Base.operationReadback (Base.Read.answer token after))

  refused : Store.World → Diagnostic.Diagnostic → Expected
  refused before diagnostic@(Diagnostic.requestFault fault) =
    Base.expected before (just (Step.needsInput diagnostic)) (Base.requestCorrection fault)
  refused before diagnostic = Base.expected before (just (Step.needsInput diagnostic))
    (Base.beliefDeletionProblem databaseSum diagnostic)

  publication : ℕ → Store.World × Wire.Value → Expected
  publication token (changed , answer) = reflected token final (Step.done answer)
    where final = Store.saveAnswer (Store.saveAnswer changed token (Registration.key token) answer)
            token Step.resultKey answer

  checked : ℕ → Sweep.Request → ℤ → ℤ → Store.World → Posterior.CalculationReport → Expected
  checked token requested selectedAt publishedAt before actual
    with proj₁ (Business.checked requested selectedAt publishedAt before)
    where module Business = Sweep.Business format databaseSum (λ _ _ _ _ → actual)
  ... | inj₁ diagnostic = refused before diagnostic
  ... | inj₂ changed = publication token changed

  atTimes : ℕ → Sweep.Request → ℤ → ℤ → Store.World → Observations → Evaluation
  atTimes token requested selectedAt publishedAt before observed
    with Numeric.probability (Sweep.Request.threshold requested)
  ... | false = inj₂ (refused before (Diagnostic.requestFault Sweep.Faults.invalidThreshold))
  ... | true with Sweep.selected requested selectedAt before
  ... | nothing = inj₂ (refused before (Diagnostic.requestFault Sweep.Faults.missingClock))
  ... | just [] = inj₂ (publication token (before , Sweep.PublicAnswer.answer format []))
  ... | just identities@(_ ∷ _) with N.prepare (N.recompute (Sweep.affected identities before)) (Sweep.erased identities before)
  ... | inj₁ issue = inj₂ (refused before (Diagnostic.preparation issue))
  ... | inj₂ selected with Observations.report observed
  ... | nothing = inj₁ (missing "calculation_report")
  ... | just actual = inj₂ (checked token requested selectedAt publishedAt before actual)

  clocks : ℕ → Sweep.Request → Store.World → Observations → Evaluation
  clocks token requested before observed with Observations.selectedAt observed
  ... | nothing = inj₁ (missing "selection_clock")
  ... | just selectedAt with Observations.publicationTime observed
  ... | nothing = inj₁ (missing "posterior_publication_clock")
  ... | just publishedAt = atTimes token requested selectedAt publishedAt before observed

  currentPolicy : ℕ → Registration.Bound → Registration.Policy → Store.World → Observations → Evaluation
  currentPolicy token bound chosen before observed with Observations.currentPolicy observed
  ... | nothing = inj₁ (missing "current_policy")
  ... | just actual with Registration.configured actual
  ... | inj₁ fault = inj₂ (refused before (Diagnostic.requestFault fault))
  ... | inj₂ current with Registration.samePolicy chosen current
  ... | false = inj₂ (refused before (Diagnostic.requestFault Registration.changedPolicy))
  ... | true = clocks token (Registration.requested bound chosen) before observed

  configured : ℕ → Registration.Bound → Store.World → Observations → Evaluation
  configured token bound before observed with Registration.storedPolicy (Registration.Bound.settings bound)
  ... | inj₁ fault = inj₂ (refused before (Diagnostic.requestFault fault))
  ... | inj₂ chosen = currentPolicy token bound chosen before observed

  single : ℕ → Registration.Bound → Store.World → Observations → Evaluation
  single token bound before observed with Store.lookupCancellation before token
  ... | just cancelled = inj₂ (reflected token before (Step.cancelled cancelled))
  ... | nothing with Store.lookupSaved before token (Registration.key token) | Store.lookupSaved before token Step.resultKey
  ... | just saved | just final = inj₂ (reflected token before (Step.done saved))
  ... | just _ | nothing = inj₂ (reflected token before Step.needsRecovery)
  ... | nothing | just _ = inj₂ (reflected token before Step.needsRecovery)
  ... | nothing | nothing = configured token bound before observed

  business : ℕ → Store.World → Observations → Evaluation
  business token before observed with Registration.original token (Step.registration before)
  ... | inj₁ fault = inj₂ (refused before (Diagnostic.requestFault fault))
  ... | inj₂ bound = single token bound before observed

  changedPolicyNeedsNoClocksOrReport : ∀ token bound chosen before observed actual current →
    Observations.currentPolicy observed ≡ just actual → Registration.configured actual ≡ inj₂ current →
    Registration.samePolicy chosen current ≡ false →
    currentPolicy token bound chosen before observed ≡ inj₂ (refused before (Diagnostic.requestFault Registration.changedPolicy))
  changedPolicyNeedsNoClocksOrReport token bound chosen before observed actual current captured decoded changed
    rewrite captured | decoded | changed = refl

  savedResultNeedsNoFreshReceipts : ∀ token bound before observed saved final →
    Store.lookupCancellation before token ≡ nothing →
    Store.lookupSaved before token (Registration.key token) ≡ just saved →
    Store.lookupSaved before token Step.resultKey ≡ just final →
    single token bound before observed ≡ inj₂ (reflected token before (Step.done saved))
  savedResultNeedsNoFreshReceipts token bound before observed saved final active stored completed
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
    evaluate raw before with Decode.readInvocation Tools.sweepExpiredDefeated raw
    ... | inj₁ fault = inj₂ (Base.expected before nothing (Base.requestCorrection fault))
    ... | inj₂ admitted = afterMetadata call (Metadata.admitted call before)
      where call = Base.C.admittedWrite Tools.sweepExpiredDefeated raw refl admitted

    malformedRequestDoesNotEnterBody : ∀ raw before fault →
      Decode.readInvocation Tools.sweepExpiredDefeated raw ≡ inj₁ fault →
      evaluate raw before ≡ inj₂ (Base.expected before nothing (Base.requestCorrection fault))
    malformedRequestDoesNotEnterBody raw before fault rejected rewrite rejected = refl
