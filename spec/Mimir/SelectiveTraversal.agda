{-# OPTIONS --safe #-}
-- Ordered extraction with ignored entries and first-error short circuit.
-- Used for provider responses containing reasoning/text beside tool calls.
module Mimir.SelectiveTraversal where

open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties using (m≤n⇒m≤1+n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module Traversal (A B Error : Set) (read : A → Error ⊎ Maybe B) where
  run : List A → Error ⊎ List B
  run [] = inj₂ []
  run (entry ∷ rest) with read entry
  ... | inj₁ failure = inj₁ failure
  ... | inj₂ nothing = run rest
  ... | inj₂ (just value) with run rest
  ...   | inj₁ failure = inj₁ failure
  ...   | inj₂ values = inj₂ (value ∷ values)

  data Extracted : List A → List B → Set where
    empty : Extracted [] []
    ignored : ∀ {entry rest values} → read entry ≡ inj₂ nothing →
      Extracted rest values → Extracted (entry ∷ rest) values
    retained : ∀ {entry value rest values} → read entry ≡ inj₂ (just value) →
      Extracted rest values → Extracted (entry ∷ rest) (value ∷ values)

  sound : ∀ entries values → run entries ≡ inj₂ values → Extracted entries values
  sound [] .[] refl = empty
  sound (entry ∷ rest) values observed with read entry in decoded
  ... | inj₁ failure with observed
  ...   | ()
  sound (entry ∷ rest) values observed | inj₂ nothing = ignored decoded (sound rest values observed)
  sound (entry ∷ rest) values observed | inj₂ (just value) with run rest in tail
  ... | inj₁ failure with observed
  ...   | ()
  sound (entry ∷ rest) .(value ∷ values) refl | inj₂ (just value) | inj₂ values =
    retained decoded (sound rest values tail)

  complete : ∀ {entries values} → Extracted entries values → run entries ≡ inj₂ values
  complete empty = refl
  complete (ignored decoded rest) rewrite decoded = complete rest
  complete (retained decoded rest) rewrite decoded | complete rest = refl

  countBound : ∀ {entries values} → Extracted entries values → length values ≤ length entries
  countBound empty = z≤n
  countBound (ignored decoded rest) = m≤n⇒m≤1+n (countBound rest)
  countBound (retained decoded rest) = s≤s (countBound rest)

  everyOutput : ∀ {P : B → Set} → (∀ entry value → read entry ≡ inj₂ (just value) → P value) →
    ∀ {entries values} → Extracted entries values → All P values
  everyOutput property empty = []
  everyOutput property (ignored decoded rest) = everyOutput property rest
  everyOutput property (retained decoded rest) = property _ _ decoded ∷ everyOutput property rest

  firstFailureStops : ∀ entry rest failure → read entry ≡ inj₁ failure → run (entry ∷ rest) ≡ inj₁ failure
  firstFailureStops entry rest failure observed rewrite observed = refl
