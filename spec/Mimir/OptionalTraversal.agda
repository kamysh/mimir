{-# OPTIONS --safe #-}
module Mimir.OptionalTraversal where

open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (suc)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)

nothingNotJust : ∀ {A : Set} {x : A} → nothing ≢ just x
nothingNotJust ()

traverse : ∀ {A B : Set} → (A → Maybe B) → List A → Maybe (List B)
traverse f [] = just []
traverse f (x ∷ xs) with f x
... | nothing = nothing
... | just y with traverse f xs
...   | nothing = nothing
...   | just ys = just (y ∷ ys)

preservesLength : ∀ {A B : Set} (f : A → Maybe B) xs ys →
  traverse f xs ≡ just ys → length ys ≡ length xs
preservesLength f [] .[] refl = refl
preservesLength f (x ∷ xs) ys eq with f x
... | nothing = ⊥-elim (nothingNotJust eq)
... | just y with traverse f xs in tail
...   | nothing = ⊥-elim (nothingNotJust eq)
...   | just rest with eq
...     | refl = cong suc (preservesLength f xs rest tail)

allOutputs : ∀ {A B : Set} {P : B → Set} (f : A → Maybe B) →
  (∀ x y → f x ≡ just y → P y) → ∀ xs ys → traverse f xs ≡ just ys → All P ys
allOutputs f property [] .[] refl = []
allOutputs f property (x ∷ xs) ys eq with f x in head
... | nothing = ⊥-elim (nothingNotJust eq)
... | just y with traverse f xs in tail
...   | nothing = ⊥-elim (nothingNotJust eq)
...   | just rest with eq
...     | refl = property x y head ∷ allOutputs f property xs rest tail

unchanged : ∀ {A : Set} (f : A → Maybe A) xs →
  All (λ x → f x ≡ just x) xs → traverse f xs ≡ just xs
unchanged f [] [] = refl
unchanged f (x ∷ xs) (head ∷ rest) rewrite head | unchanged f xs rest = refl
