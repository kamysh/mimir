{-# OPTIONS --safe #-}
-- Immutable observations survive any sequence of accepted corrections.
module Mimir.Retention where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Mimir.Collections
open import Mimir.Validation

module Elements (A : Set) (eq : (x y : A) → Dec (x ≡ y)) where
  module Set = Equality A eq

  Retained : List A → List A → Set
  Retained old new = All (λ x → Set.Present x new) old

  validate : ∀ old new → Checked (Retained old new)
  validate old new = allChecked
    (λ x → check (fault [] missingReference "correction must retain the original observation")
      (Set.present? x new)) old

  prependNew : ∀ {old new} x → Retained old new → Retained old (x ∷ new)
  prependNew x [] = []
  prependNew x (p ∷ ps) = there p ∷ prependNew x ps

  reflexive : ∀ xs → Retained xs xs
  reflexive [] = []
  reflexive (x ∷ xs) = here refl ∷ prependNew x (reflexive xs)

  kept : ∀ {old new x} → Retained old new → Set.Present x old → Set.Present x new
  kept (p ∷ ps) (here refl) = p
  kept (p ∷ ps) (there member) = kept ps member

  transitive : ∀ {first second third} → Retained first second → Retained second third → Retained first third
  transitive [] later = []
  transitive (p ∷ ps) later = kept later p ∷ transitive ps later

  presentAppend : ∀ {x xs} ys → Set.Present x xs → Set.Present x (xs ++ ys)
  presentAppend ys (here same) = here same
  presentAppend ys (there p) = there (presentAppend ys p)

  append : ∀ old additional → Retained old (old ++ additional)
  append [] additional = []
  append (x ∷ xs) additional = here refl ∷ prependNew x (append xs additional)

  acceptedCorrectionNeverLoses : ∀ old new → Retained old new → reported (validate old new) ≡ []
  acceptedCorrectionNeverLoses old new = noFalseRejection (validate old new)
