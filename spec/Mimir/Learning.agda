{-# OPTIONS --safe #-}
-- Versioned review contributions. The database stores an immutable history;
-- exactly one review pointer per experience selects its current contribution.
-- Neither a retry nor an obsolete review contributes another observation.
module Mimir.Learning where

open import Data.Nat using (ℕ; _≟_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Data.Empty using (⊥-elim)

-- The payload is abstract: these laws apply equally to positive/negative Beta
-- contributions, typed causal edges, and explicit supersession decisions.
module Contributions (Evidence : Set) where
  Ledger : Set
  Ledger = List (ℕ × Evidence)

  remove : ℕ → Ledger → Ledger
  remove k [] = []
  remove k ((j , e) ∷ xs) with k ≟ j
  ... | yes _ = remove k xs
  ... | no _ = (j , e) ∷ remove k xs

  replace : ℕ → Evidence → Ledger → Ledger
  replace k e xs = (k , e) ∷ remove k xs

  remove-idempotent : ∀ k xs → remove k (remove k xs) ≡ remove k xs
  remove-idempotent k [] = refl
  remove-idempotent k ((j , e) ∷ xs) with k ≟ j
  ... | yes _ = remove-idempotent k xs
  ... | no neq with k ≟ j
  ...   | yes eq = ⊥-elim (neq eq)
  ...   | no _ = cong ((j , e) ∷_) (remove-idempotent k xs)

  -- Re-applying the same review cannot accumulate evidence.
  replace-idempotent : ∀ k e xs → replace k e (replace k e xs) ≡ replace k e xs
  replace-idempotent k e xs with k ≟ k
  ... | yes _ = cong ((k , e) ∷_) (remove-idempotent k xs)
  ... | no neq = ⊥-elim (neq refl)

  -- A correction replaces the old contribution completely, irrespective of
  -- its content. Thus a reviewer can retract or reverse an earlier judgment.
  replacement-forgets-old : ∀ k new old xs → replace k new (replace k old xs) ≡ replace k new xs
  replacement-forgets-old k new old xs with k ≟ k
  ... | yes _ = cong ((k , new) ∷_) (remove-idempotent k xs)
  ... | no neq = ⊥-elim (neq refl)

  active : ℕ → ℕ → List Evidence → List Evidence
  active current reviewed es with current ≟ reviewed
  ... | yes _ = es
  ... | no _ = []

  stale-review-contributes-nothing : ∀ current reviewed es → current ≢ reviewed → active current reviewed es ≡ []
  stale-review-contributes-nothing current reviewed es neq with current ≟ reviewed
  ... | yes eq = ⊥-elim (neq eq)
  ... | no _ = refl

  current-review-preserved : ∀ revision es → active revision revision es ≡ es
  current-review-preserved revision es with revision ≟ revision
  ... | yes _ = refl
  ... | no neq = ⊥-elim (neq refl)
