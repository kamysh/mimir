{-# OPTIONS --safe #-}
-- Resolve the immutable original request before any saved-answer replay.
-- A wrong token or plan returns a concrete correction, without changing World.
module Mimir.RegisteredStoreAdmission where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ) renaming (_≟_ to _≟ℕ_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.String using (toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.ApplicationStore as Store
import Mimir.ProjectDeletion as Project
import Mimir.RecoverableStoreStep as Step
import Mimir.StructuredValue as Wire
import Mimir.Validation as Validation
import Mimir.RecordDecoding as Decode
import Mimir.JsonObjects as Objects

record Descriptor : Set where
  constructor descriptor
  field operation site key : Text

module Plan (registered : Descriptor) where
  open Descriptor registered
  open Project.Registered using (fields; fieldText; fieldNull; fieldFalse; singleton)

  shapeMatches : Wire.Value → Bool
  shapeMatches = fields (toList "site" ∷ toList "may_repeat" ∷ []) λ view →
    fieldText site (view (toList "site")) ∧ fieldFalse (view (toList "may_repeat"))

  stepMatches : Wire.Value → Bool
  stepMatches = fields (toList "site" ∷ toList "key" ∷ toList "id" ∷ []) λ view →
    fieldText site (view (toList "site")) ∧ fieldNull (view (toList "key")) ∧
      fieldText key (view (toList "id"))

  matches : Wire.Value → Bool
  matches = fields (toList "operation" ∷ toList "shape" ∷ toList "steps" ∷ []) λ view →
    fieldText operation (view (toList "operation")) ∧
      singleton shapeMatches (view (toList "shape")) ∧ singleton stepMatches (view (toList "steps"))

reservation : ℕ → List Store.ReservationRow → Maybe Store.ReservationRow
reservation token [] = nothing
reservation token (row ∷ rest) with token ≟ℕ Store.ReservationRow.token row
... | yes _ = just row
... | no _ = reservation token rest

-- Settings and business arguments are decoded by the concrete operation;
-- this shared layer resolves the original request and its durable plan.
originalPlan : Text → ℕ → Step.Registration →
  Validation.Fault ⊎ (Store.ReservationRow × Store.BindingRow × Wire.Value)
originalPlan operation token (reservations , requestKeys , bindings , plans) with reservation token reservations
... | nothing = inj₁ (Validation.fault (Validation.key "operation_token" ∷ []) Validation.missingReference
  "Unknown operation token. Reserve the original request with its stable request_key, or read its reservation reply if it was lost. Do not invent a token.")
... | just reserved with Project.Registered.binding token bindings
... | nothing = inj₁ (Validation.fault (Validation.key "operation_token" ∷ []) Validation.missingReference
  "This token has no bound request. Bind its original arguments and settings before execution; read the original outcome if a reply was lost.")
... | just original with does (Store.BindingRow.operation original ≟Text operation)
... | false = inj₁ (Validation.fault (Validation.key "operation_token" ∷ []) Validation.wrongIdentity
  "This token belongs to a different operation. Read its original binding and saved outcome. Keep the original request; ask the user before starting distinct work.")
... | true with Project.Registered.plan token plans
... | nothing = inj₁ (Validation.fault (Validation.key "plan" ∷ []) Validation.missingField
  "This operation has no saved plan. Prepare its original operation plan before execution; retain the original token and request.")
... | just saved = inj₂ (reserved , original , saved)

planMismatch : Validation.Fault
planMismatch = Validation.fault (Validation.key "plan" ∷ []) Validation.wrongIdentity
  "The saved plan does not match the registered statement boundaries. Read the original plan and outcome and ask the user to resolve the mismatch. Do not repeat changes or invent an answer."

resolve : Descriptor → ℕ → Step.Registration →
  Validation.Fault ⊎ (Store.ReservationRow × Store.BindingRow)
resolve registered token registration with originalPlan (Descriptor.operation registered) token registration
... | inj₁ fault = inj₁ fault
... | inj₂ (reserved , original , saved) with Plan.matches registered saved
... | false = inj₁ (Validation.fault (Validation.key "plan" ∷ []) Validation.wrongIdentity
  "The saved plan does not match the registered final step. Read the original plan and outcome and ask the user to resolve the mismatch. Do not repeat changes or invent an answer.")
... | true = inj₂ (reserved , original)

-- A defeat has two independently durable boundaries. Its complete original
-- plan is checked before either boundary or a saved answer can be used.
record PairDescriptor : Set where
  constructor pairDescriptor
  field operation firstSite firstKey secondSite secondKey : Text

module PairPlan (registered : PairDescriptor) where
  open PairDescriptor registered
  open Project.Registered using (fields; fieldText)
  module First = Plan (descriptor operation firstSite firstKey)
  module Second = Plan (descriptor operation secondSite secondKey)

  pair : (Wire.Value → Bool) → (Wire.Value → Bool) → Maybe Wire.Value → Bool
  pair first second (just (Wire.array (a ∷ b ∷ []))) = first a ∧ second b
  pair first second _ = false

  matches : Wire.Value → Bool
  matches = fields (toList "operation" ∷ toList "shape" ∷ toList "steps" ∷ []) λ view →
    fieldText operation (view (toList "operation")) ∧
      pair First.shapeMatches Second.shapeMatches (view (toList "shape")) ∧
      pair First.stepMatches Second.stepMatches (view (toList "steps"))

resolvePair : PairDescriptor → ℕ → Step.Registration →
  Validation.Fault ⊎ (Store.ReservationRow × Store.BindingRow)
resolvePair registered token registration with originalPlan (PairDescriptor.operation registered) token registration
... | inj₁ fault = inj₁ fault
... | inj₂ (reserved , original , saved) with PairPlan.matches registered saved
... | false = inj₁ planMismatch
... | true = inj₂ (reserved , original)

-- Shared projections of the existing typed plan records. They expose
-- checked field values; they do not parse bytes or format identifiers.
module RecordFields where
  andLeft : ∀ first second → first ∧ second ≡ true → first ≡ true
  andLeft false second ()
  andLeft true second known = refl
  andRight : ∀ first second → first ∧ second ≡ true → second ≡ true
  andRight false second ()
  andRight true second known = known

  thirdTrue : ∀ first second third → first ∧ second ∧ third ≡ true → third ≡ true
  thirdTrue first second third known = andRight second third (andRight first (second ∧ third) known)

  sameRecordView : ∀ {A : Set} firstNames secondNames
    (check : Wire.Object.View → Bool) (decode : Wire.Object.View → Validation.Fault ⊎ A) raw value →
    Project.Registered.fields firstNames check raw ≡ true →
    Decode.readRecord Objects.forbid Objects.rejectKnownRepeated secondNames decode raw ≡ inj₂ value →
    Σ Wire.Object.View (λ view → check view ≡ true × decode view ≡ inj₂ value)
  sameRecordView firstNames secondNames check decode raw value matched decoded with Wire.asObject raw
  ... | inj₁ fault with matched
  ... | ()
  sameRecordView firstNames secondNames check decode raw value matched decoded | inj₂ fields
    with Wire.Object.checkUnknowns Objects.forbid firstNames fields
  ... | Validation.rejected fault invalid with matched
  ... | ()
  sameRecordView firstNames secondNames check decode raw value matched decoded | inj₂ fields | Validation.accepted known
    with Wire.Object.checkDuplicates Objects.rejectKnownRepeated firstNames fields
  ... | Validation.rejected fault invalid with matched
  ... | ()
  sameRecordView firstNames secondNames check decode raw value matched decoded | inj₂ fields | Validation.accepted known | Validation.accepted unique
    with Wire.Object.checkUnknowns Objects.forbid secondNames fields
  ... | Validation.rejected fault invalid with decoded
  ... | ()
  sameRecordView firstNames secondNames check decode raw value matched decoded | inj₂ fields | Validation.accepted known | Validation.accepted unique | Validation.accepted knownSecond
    with Wire.Object.checkDuplicates Objects.rejectKnownRepeated secondNames fields
  ... | Validation.rejected fault invalid with decoded
  ... | ()
  sameRecordView firstNames secondNames check decode raw value matched decoded | inj₂ fields | Validation.accepted known | Validation.accepted unique | Validation.accepted knownSecond | Validation.accepted uniqueSecond =
    Wire.Object.normalize fields , matched , decoded

  textField : ∀ expected observed → Project.Registered.fieldText expected observed ≡ true →
    observed ≡ just (Wire.string expected)
  textField expected (just (Wire.string actual)) accepted with actual ≟Text expected
  ... | yes refl = refl
  ... | no different with accepted
  ... | ()
  textField expected (just Wire.null) ()
  textField expected (just (Wire.boolean _)) ()
  textField expected (just (Wire.unsigned _)) ()
  textField expected (just (Wire.signed _)) ()
  textField expected (just (Wire.floating _)) ()
  textField expected (just (Wire.array _)) ()
  textField expected (just (Wire.object _)) ()
  textField expected nothing ()

  nullField : ∀ observed → Project.Registered.fieldNull observed ≡ true → observed ≡ just Wire.null
  nullField (just Wire.null) accepted = refl
  nullField (just (Wire.boolean _)) ()
  nullField (just (Wire.unsigned _)) ()
  nullField (just (Wire.signed _)) ()
  nullField (just (Wire.floating _)) ()
  nullField (just (Wire.string _)) ()
  nullField (just (Wire.array _)) ()
  nullField (just (Wire.object _)) ()
  nullField nothing ()

  unfield : ∀ {A : Set} name (observed : Validation.Fault ⊎ A) value →
    Wire.withField name observed ≡ inj₂ value → observed ≡ inj₂ value
  unfield name (inj₁ fault) value ()
  unfield name (inj₂ observed) value known = known
