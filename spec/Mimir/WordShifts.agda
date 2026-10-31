{-# OPTIONS --safe #-}
-- Least-significant-bit-first shifts and rotations. No bits are silently
-- widened: every operation preserves the word width by construction.
module Mimir.WordShifts where

open import Data.Vec using ([]; _∷_; _∷ʳ_; init; last)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans)
open import Mimir.Bits using (Bit; Word; O)

rightOnce leftOnce rotateRightOnce rotateLeftOnce : ∀ {width} → Word width → Word width
rightOnce [] = []
rightOnce (bit ∷ rest) = rest ∷ʳ O
leftOnce {zero} word = []
leftOnce {suc width} word = O ∷ init word
rotateRightOnce [] = []
rotateRightOnce (bit ∷ rest) = rest ∷ʳ bit
rotateLeftOnce {zero} word = []
rotateLeftOnce {suc width} word = last word ∷ init word

iterate : ∀ {A : Set} → (A → A) → ℕ → A → A
iterate step zero value = value
iterate step (suc count) value = step (iterate step count value)

right left rotateRight rotateLeft : ∀ {width} → ℕ → Word width → Word width
right = iterate rightOnce
left = iterate leftOnce
rotateRight = iterate rotateRightOnce
rotateLeft = iterate rotateLeftOnce

iterateStep : ∀ {A : Set} (step : A → A) count value →
  iterate step count (step value) ≡ step (iterate step count value)
iterateStep step zero value = refl
iterateStep step (suc count) value = cong step (iterateStep step count value)

iterateAdd : ∀ {A : Set} (step : A → A) first second value →
  iterate step (first + second) value ≡ iterate step first (iterate step second value)
iterateAdd step zero second value = refl
iterateAdd step (suc first) second value = cong step (iterateAdd step first second value)

initSnoc : ∀ {width} (word : Word width) bit → init (word ∷ʳ bit) ≡ word
initSnoc [] bit = refl
initSnoc (first ∷ rest) bit = cong (first ∷_) (initSnoc rest bit)

lastSnoc : ∀ {width} (word : Word width) bit → last (word ∷ʳ bit) ≡ bit
lastSnoc [] bit = refl
lastSnoc (first ∷ rest) bit = lastSnoc rest bit

snocParts : ∀ {width} (word : Word (suc width)) → init word ∷ʳ last word ≡ word
snocParts (bit ∷ []) = refl
snocParts (bit ∷ next ∷ rest) = cong (bit ∷_) (snocParts (next ∷ rest))

leftRightOnce : ∀ {width} (word : Word width) → rotateLeftOnce (rotateRightOnce word) ≡ word
leftRightOnce [] = refl
leftRightOnce (bit ∷ rest) = cong₂ _∷_ (lastSnoc rest bit) (initSnoc rest bit)

rightLeftOnce : ∀ {width} (word : Word width) → rotateRightOnce (rotateLeftOnce word) ≡ word
rightLeftOnce [] = refl
rightLeftOnce word@(_ ∷ _) = snocParts word

leftRight : ∀ {width} count (word : Word width) → rotateLeft count (rotateRight count word) ≡ word
leftRight zero word = refl
leftRight (suc count) word =
  trans (Relation.Binary.PropositionalEquality.sym
    (iterateStep rotateLeftOnce count (rotateRightOnce (rotateRight count word))))
    (trans (cong (rotateLeft count) (leftRightOnce (rotateRight count word))) (leftRight count word))

rightLeft : ∀ {width} count (word : Word width) → rotateRight count (rotateLeft count word) ≡ word
rightLeft zero word = refl
rightLeft (suc count) word =
  trans (Relation.Binary.PropositionalEquality.sym
    (iterateStep rotateRightOnce count (rotateLeftOnce (rotateLeft count word))))
    (trans (cong (rotateRight count) (rightLeftOnce (rotateLeft count word))) (rightLeft count word))

rotateInjective : ∀ {width} count (first second : Word width) → rotateRight count first ≡ rotateRight count second → first ≡ second
rotateInjective count first second same = trans
  (Relation.Binary.PropositionalEquality.sym (leftRight count first))
  (trans (cong (rotateLeft count) same) (leftRight count second))
