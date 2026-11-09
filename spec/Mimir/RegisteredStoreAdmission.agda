{-# OPTIONS --safe #-}
-- Resolve the immutable original request before any saved-answer replay.
-- A wrong token or plan returns a concrete correction, without changing World.
module Mimir.RegisteredStoreAdmission where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ) renaming (_≟_ to _≟ℕ_)
open import Data.Product using (_×_; _,_)
open import Data.String using (toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no; does)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.ApplicationStore as Store
import Mimir.ProjectDeletion as Project
import Mimir.RecoverableStoreStep as Step
import Mimir.StructuredValue as Wire
import Mimir.Validation as Validation

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
-- this shared layer only admits its one registered final statement boundary.
resolve : Descriptor → ℕ → Step.Registration →
  Validation.Fault ⊎ (Store.ReservationRow × Store.BindingRow)
resolve registered token (reservations , requestKeys , bindings , plans) with reservation token reservations
... | nothing = inj₁ (Validation.fault (Validation.key "operation_token" ∷ []) Validation.missingReference
  "Unknown operation token. Reserve the original request with its stable request_key, or read its reservation reply if it was lost. Do not invent a token.")
... | just reserved with Project.Registered.binding token bindings
... | nothing = inj₁ (Validation.fault (Validation.key "operation_token" ∷ []) Validation.missingReference
  "This token has no bound request. Bind its original arguments and settings before execution; read the original outcome if a reply was lost.")
... | just original with does (Store.BindingRow.operation original ≟Text Descriptor.operation registered)
... | false = inj₁ (Validation.fault (Validation.key "operation_token" ∷ []) Validation.wrongIdentity
  "This token belongs to a different operation. Read its original binding and saved outcome. Keep the original request; ask the user before starting distinct work.")
... | true with Project.Registered.plan token plans
... | nothing = inj₁ (Validation.fault (Validation.key "plan" ∷ []) Validation.missingField
  "This operation has no saved plan. Prepare its registered final-step plan before execution; retain the original token and request.")
... | just saved with Plan.matches registered saved
... | false = inj₁ (Validation.fault (Validation.key "plan" ∷ []) Validation.wrongIdentity
  "The saved plan does not match the registered final step. Read the original plan and outcome and ask the user to resolve the mismatch. Do not repeat changes or invent an answer.")
... | true = inj₂ (reserved , original)
