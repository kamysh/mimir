{-# OPTIONS --safe #-}
-- Field-indexed predicates survive slot updates and default resolution.
-- Predicates are explicit: this does not assume validity of reader outputs.
module Mimir.SerdeSlotInvariant where

open import Data.Fin using (Fin; zero; suc; _≟_)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
import Mimir.SerdeSlots as Slots
import Mimir.SerdeSequence as Sequence
open Sequence using (Field)

Predicates : List Field → Set₁
Predicates fields = (index : Fin (length fields)) → Field.Carrier (Slots.fieldAt fields index) → Set

Present : ∀ fields → Predicates fields → Slots.Slots fields → Set
Present fields properties slots = ∀ index value →
  Slots.get fields index slots ≡ just value → properties index value

Defaults : ∀ fields → Predicates fields → Set
Defaults fields properties = ∀ index value →
  Field.missing (Slots.fieldAt fields index) ≡ just value → properties index value

valueAt : ∀ fields (index : Fin (length fields)) → Slots.Values fields → Field.Carrier (Slots.fieldAt fields index)
valueAt [] () values
valueAt (entry ∷ rest) zero (value , values) = value
valueAt (entry ∷ rest) (suc index) (value , values) = valueAt rest index values

Valid : ∀ fields → Predicates fields → Slots.Values fields → Set
Valid fields properties values = ∀ index → properties index (valueAt fields index values)

empty : ∀ fields properties → Present fields properties (Slots.empty fields)
empty fields properties index value observed =
  case trans (sym (Slots.emptyAbsent fields index)) observed of λ ()

put : ∀ fields properties selected value slots →
  Present fields properties slots → properties selected value →
  Present fields properties (Slots.put fields selected value slots)
put fields properties selected value slots holds inserted index output observed with selected ≟ index
... | yes refl = subst (properties selected)
  (just-injective (trans (sym (Slots.getOwnPut fields selected value slots)) observed)) inserted
... | no different = holds index output
  (trans (sym (Slots.getOtherPut fields selected index value slots different)) observed)

resolved : ∀ {fields slots values} (properties : Predicates fields) →
  Slots.Resolved fields slots values → Present fields properties slots → Defaults fields properties →
  Valid fields properties values
resolved properties Slots.resolvedEmpty holds defaults = λ ()
resolved properties (Slots.supplied resolution) holds defaults = λ
  { zero → holds zero _ refl
  ; (suc index) → resolved (λ i → properties (suc i)) resolution
      (λ i → holds (suc i)) (λ i → defaults (suc i)) index
  }
resolved properties (Slots.defaulted fallback resolution) holds defaults = λ
  { zero → defaults zero _ fallback
  ; (suc index) → resolved (λ i → properties (suc i)) resolution
      (λ i → holds (suc i)) (λ i → defaults (suc i)) index
  }
