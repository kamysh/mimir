{-# OPTIONS --safe #-}
-- Parser composition with exact consumption on both success and failure.
module Mimir.SequenceCursor where

open import Data.List using (List; []; _++_; length)
open import Data.List.Properties using (++-assoc; length-++-≤ˡ)
open import Data.Nat using (_≤_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)

module Over (Atom Code : Set) where
  data Result (Value : Set) (input : List Atom) : Set where
    success : Value → (consumed remaining : List Atom) → input ≡ consumed ++ remaining → Result Value input
    failure : Code → (consumed remaining : List Atom) → input ≡ consumed ++ remaining → Result Value input

  consumed : ∀ {Value input} → Result Value input → List Atom
  consumed (success value prefix suffix exact) = prefix
  consumed (failure code prefix suffix exact) = prefix

  remaining : ∀ {Value input} → Result Value input → List Atom
  remaining (success value prefix suffix exact) = suffix
  remaining (failure code prefix suffix exact) = suffix

  reconstruct : ∀ {Value input} (result : Result Value input) → input ≡ consumed result ++ remaining result
  reconstruct (success value prefix suffix exact) = exact
  reconstruct (failure code prefix suffix exact) = exact

  offsetBound : ∀ {Value input} (result : Result Value input) → length (consumed result) ≤ length input
  offsetBound (success value prefix suffix refl) = length-++-≤ˡ prefix
  offsetBound (failure code prefix suffix refl) = length-++-≤ˡ prefix

  prefix : ∀ {Value input} bytes → Result Value input → Result Value (bytes ++ input)
  prefix bytes (success value consumed remaining exact) = success value (bytes ++ consumed) remaining
    (trans (cong (bytes ++_) exact) (sym (++-assoc bytes consumed remaining)))
  prefix bytes (failure code consumed remaining exact) = failure code (bytes ++ consumed) remaining
    (trans (cong (bytes ++_) exact) (sym (++-assoc bytes consumed remaining)))

  reframe : ∀ {Value input source} → input ≡ source → Result Value source → Result Value input
  reframe refl result = result

  done : ∀ {Value} → Value → ∀ input → Result Value input
  done value input = success value [] input refl

  fail : ∀ {Value} → Code → ∀ input → Result Value input
  fail code input = failure code [] input refl

  andThen : ∀ {First Second input} → Result First input →
    (First → ∀ rest → Result Second rest) → Result Second input
  andThen (failure code consumed remaining exact) next = failure code consumed remaining exact
  andThen (success value consumed remaining exact) next = reframe exact (prefix consumed (next value remaining))
