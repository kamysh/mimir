{-# OPTIONS --safe #-}
-- Exact consumed prefix and remaining input for parser errors. An error offset
-- is derived from those bytes and cannot point beyond the supplied input.
module Mimir.ByteCursor where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc; ++-identityʳ; length-++-≤ˡ)
open import Data.Nat using (ℕ; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
open import Mimir.Bits using (Byte)

module WithCode (Code : Set) where
  record Failure (input : List Byte) : Set where
    constructor failed
    field
      code : Code
      consumed remaining : List Byte
      exact : input ≡ consumed ++ remaining

  offset : ∀ {input} → Failure input → ℕ
  offset failure = length (Failure.consumed failure)

  offsetWithinInput : ∀ {input} (failure : Failure input) → offset failure ≤ length input
  offsetWithinInput (failed code consumed remaining refl) = length-++-≤ˡ consumed

  prefix : ∀ bytes {input} → Failure input → Failure (bytes ++ input)
  prefix bytes (failed code consumed remaining exact) = failed code (bytes ++ consumed) remaining
    (trans (cong (bytes ++_) exact) (sym (++-assoc bytes consumed remaining)))

  reframe : ∀ {input source} → input ≡ source → Failure source → Failure input
  reframe refl failure = failure

  end : ∀ input code → Failure input
  end input code = failed code input [] (sym (++-identityʳ input))
