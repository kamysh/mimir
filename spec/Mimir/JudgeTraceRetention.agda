{-# OPTIONS --safe #-}
-- Starting a trace removes at most one oldest eligible attempt. A malformed
-- over-capacity input is not silently normalized, and UUID freshness is not
-- assumed. The source fallback removes index zero if no eligible entry exists.
module Mimir.JudgeTraceRetention where

open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.Maybe using (Maybe; just)
open import Data.Nat using (ℕ; suc; _≤_; _≤?_; z≤n; s≤s⁻¹)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_; _×-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst; cong)
import Mimir.Collections as Collections
import Mimir.JudgeStateRecords as Records
import Mimir.FirstListMatch as First

module Over (Id : Set) (equal : (x y : Id) → Dec (x ≡ y)) where
  module R = Records.Over Id

  module Selection (created : Id) (pinned : Maybe Id) where
    Eligible : R.Trace → Set
    Eligible trace = just (R.Trace.identity trace) ≢ pinned × R.Trace.identity trace ≢ created

    eligible? : ∀ trace → Dec (Eligible trace)
    eligible? trace = Collections.negate (Collections.maybeEqual equal (just (R.Trace.identity trace)) pinned) ×-dec
      Collections.negate (equal (R.Trace.identity trace) created)

    module F = First.Over R.Trace Eligible eligible?

    data Retained (limit : ℕ) (before : List R.Trace) : List R.Trace → Set where
      within : length before ≤ limit → Retained limit before before
      evicted : ¬ length before ≤ limit → (selected : F.Focus before) → Retained limit before (F.remove selected)
      fallback : ∀ first rest → before ≡ first ∷ rest → ¬ length before ≤ limit →
        All (λ trace → ¬ Eligible trace) before → Retained limit before rest

    record Result (limit : ℕ) (before : List R.Trace) : Set where
      constructor result
      field after : List R.Trace; meaning : Retained limit before after

    retain : ∀ limit before → Result limit before
    retain limit before with length before ≤? limit
    ... | yes bounded = result before (within bounded)
    ... | no over with F.find before
    ...   | F.found selected = result (F.remove selected) (evicted over selected)
    ...   | F.missing absent = firstOrImpossible before over absent
      where
      firstOrImpossible : ∀ values → ¬ length values ≤ limit → All (λ trace → ¬ Eligible trace) values → Result limit values
      firstOrImpossible [] over absent = ⊥-elim (over z≤n)
      firstOrImpossible (first ∷ rest) over absent = result rest (fallback first rest refl over absent)

    capacityPreserved : ∀ {limit before after} → Retained limit before after → length before ≤ suc limit → length after ≤ limit
    capacityPreserved (within bounded) initiallyBounded = bounded
    capacityPreserved {limit} (evicted over selected) initiallyBounded =
      s≤s⁻¹ (subst (_≤ suc limit) (sym (F.removeLength selected)) initiallyBounded)
    capacityPreserved (fallback first rest refl over absent) initiallyBounded = s≤s⁻¹ initiallyBounded

    createdSurvivesEligibleEviction : ∀ {before} (selected : F.Focus before) →
      Any (λ trace → R.Trace.identity trace ≡ created) before →
      Any (λ trace → R.Trace.identity trace ≡ created) (F.remove selected)
    createdSurvivesEligibleEviction selected = F.removeOther (F.Focus.meaning selected)
      (proj₂ (F.matches (F.Focus.meaning selected)))

    pinnedSurvivesEligibleEviction : ∀ {before} (selected : F.Focus before) →
      Any (λ trace → just (R.Trace.identity trace) ≡ pinned) before →
      Any (λ trace → just (R.Trace.identity trace) ≡ pinned) (F.remove selected)
    pinnedSurvivesEligibleEviction selected = F.removeOther (F.Focus.meaning selected)
      (proj₁ (F.matches (F.Focus.meaning selected)))
