{-# OPTIONS --safe #-}
-- General progress laws for structurally terminating parser composition.
module Mimir.CursorProgress where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++; length-++-≤ʳ)
open import Data.Nat using (suc; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (+-monoˡ-≤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
import Mimir.SequenceCursor as Cursor

module Over (Atom Code : Set) where
  module C = Cursor.Over Atom Code

  remainingBound : ∀ {Value input} (result : C.Result Value input) → length (C.remaining result) ≤ length input
  remainingBound (C.success value consumed remaining refl) = length-++-≤ʳ remaining {xs = consumed}
  remainingBound (C.failure code consumed remaining refl) = length-++-≤ʳ remaining {xs = consumed}

  positiveRemaining : ∀ {Value input} (result : C.Result Value input) →
    1 ≤ length (C.consumed result) → length (C.remaining result) < length input
  positiveRemaining (C.success value consumed remaining refl) progress =
    subst (suc (length remaining) ≤_) (sym (length-++ consumed)) (+-monoˡ-≤ (length remaining) progress)
  positiveRemaining (C.failure code consumed remaining refl) progress =
    subst (suc (length remaining) ≤_) (sym (length-++ consumed)) (+-monoˡ-≤ (length remaining) progress)

  prefixPositive : ∀ {Value input} byte (result : C.Result Value input) → 1 ≤ length (C.consumed (C.prefix (byte ∷ []) result))
  prefixPositive byte (C.success value consumed remaining exact) = s≤s z≤n
  prefixPositive byte (C.failure code consumed remaining exact) = s≤s z≤n
