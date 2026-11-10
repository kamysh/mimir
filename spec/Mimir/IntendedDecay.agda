{-# OPTIONS --safe #-}
-- Decay compares independent count/baseline intentions, then composes the
-- saved original answer. No script, expected world or desired count is input.
module Mimir.IntendedDecay where

open import Data.Float.Base using (Float)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.ApplicationStore as Store
import Mimir.DecayRecovery as Decay
import Mimir.IntendedPreparation as Preparation
import Mimir.OperationControls as Controls
import Mimir.PublicRequest as Public
import Mimir.RecoverableStoreStep as Step
import Mimir.StandardLibrary as Library
import Mimir.StructuredValue as Wire
import Mimir.Validation as Validation
import Mimir.ToolCatalog as Tools

module Evaluate (library : Library.Contract) (postgres : Controls.PostgreSQL)
  (databaseSum : List Float → Float) where
  module Base = Preparation.Evaluate library postgres
    using (module C; module Read; Observations; Evaluation; Outcome; Expected; expected;
      requestCorrection; operationReadback; invalidDecayInputs)
  module Registration = Decay.Registration library using (original; key; atTime)
  module Business = Decay.Business databaseSum using (Diagnostic; requestFault; invalidStoredInputs; checked)
  module Decode = Public.Decode library

  Body = Step.Result Business.Diagnostic
  Expected = Base.Expected Body
  Evaluation = Preparation.ObservationError ⊎ Expected

  missingClock : Preparation.ObservationError
  missingClock = Preparation.observationError (Validation.fault
    (Validation.key "observations" ∷ Validation.key "posterior_publication_clock" ∷ []) Validation.missingField
    "Capture the actual PostgreSQL clock sampled under this decay publication's writer lock. Do not reuse reservation time, invent a timestamp or expected counts, or turn missing oracle input into a product correction. Saved/refused results need no fresh publication receipt.")

  reflected : ℕ → Store.World → Body → Expected
  reflected token after reply = Base.expected after (just reply) (Base.operationReadback (Base.Read.answer token after))

  refused : Store.World → Business.Diagnostic → Expected
  refused before diagnostic@(Business.requestFault fault) =
    Base.expected before (just (Step.needsInput diagnostic)) (Base.requestCorrection fault)
  refused before diagnostic@Business.invalidStoredInputs =
    Base.expected before (just (Step.needsInput diagnostic)) Base.invalidDecayInputs

  publication : ℕ → ℤ → Decay.Request → Store.World → Expected
  publication token time requested before with proj₁ (Business.checked (Registration.atTime time requested) before)
  ... | inj₁ diagnostic = refused before diagnostic
  ... | inj₂ (changed , answer) = reflected token final (Step.done answer)
    where final = Store.saveAnswer (Store.saveAnswer changed token (Registration.key token) answer)
            token Step.resultKey answer

  single : ℕ → Decay.Request → Store.World → Maybe ℤ → Evaluation
  single token requested before receipt with Store.lookupCancellation before token
  ... | just cancelled = inj₂ (reflected token before (Step.cancelled cancelled))
  ... | nothing with Store.lookupSaved before token (Registration.key token) | Store.lookupSaved before token Step.resultKey
  ... | just saved | just final = inj₂ (reflected token before (Step.done saved))
  ... | just _ | nothing = inj₂ (reflected token before Step.needsRecovery)
  ... | nothing | just _ = inj₂ (reflected token before Step.needsRecovery)
  ... | nothing | nothing with receipt
  ... | nothing = inj₁ missingClock
  ... | just time = inj₂ (publication token time requested before)

  business : ℕ → Store.World → Maybe ℤ → Evaluation
  business token before receipt with Registration.original token (Step.registration before)
  ... | inj₁ fault = inj₂ (refused before (Business.requestFault fault))
  ... | inj₂ requested = single token requested before receipt

  savedResultNeedsNoFreshClock : ∀ token requested before saved final →
    Store.lookupCancellation before token ≡ nothing →
    Store.lookupSaved before token (Registration.key token) ≡ just saved →
    Store.lookupSaved before token Step.resultKey ≡ just final →
    single token requested before nothing ≡ inj₂ (reflected token before (Step.done saved))
  savedResultNeedsNoFreshClock token requested before saved final active stored completed
    rewrite active | stored | completed = refl

  freshNeedsActualPublicationClock : ∀ token requested before →
    Store.lookupCancellation before token ≡ nothing →
    Store.lookupSaved before token (Registration.key token) ≡ nothing →
    Store.lookupSaved before token Step.resultKey ≡ nothing →
    single token requested before nothing ≡ inj₁ missingClock
  freshNeedsActualPublicationClock token requested before active noStep noFinal
    rewrite active | noStep | noFinal = refl

  module With (observed : (call : Base.C.Call) → Base.Observations call)
    (publicationTime : Base.C.Call → Maybe ℤ) where
    module Metadata = Preparation.Evaluate.With library postgres observed using (admitted)

    prepared : Base.C.Call → Base.Outcome → Evaluation
    prepared call (before , Base.C.needsInput fault) = inj₂ (Base.expected before nothing (Base.requestCorrection fault))
    prepared call (before , Base.C.returned outcome) = inj₂ (Base.expected before nothing (Base.operationReadback outcome))
    prepared call (before , Base.C.ready context) = business (Base.C.Call.token call) before (publicationTime call)

    afterMetadata : Base.C.Call → Base.Evaluation → Evaluation
    afterMetadata call (inj₁ missingObservation) = inj₁ missingObservation
    afterMetadata call (inj₂ outcome) = prepared call outcome

    evaluate : Wire.Value → Store.World → Evaluation
    evaluate raw before with Decode.readInvocation Tools.decayAll raw
    ... | inj₁ fault = inj₂ (Base.expected before nothing (Base.requestCorrection fault))
    ... | inj₂ admitted = afterMetadata call (Metadata.admitted call before)
      where call = Base.C.admittedWrite Tools.decayAll raw refl admitted

    malformedRequestDoesNotEnterBody : ∀ raw before fault →
      Decode.readInvocation Tools.decayAll raw ≡ inj₁ fault →
      evaluate raw before ≡ inj₂ (Base.expected before nothing (Base.requestCorrection fault))
    malformedRequestDoesNotEnterBody raw before fault rejected rewrite rejected = refl
