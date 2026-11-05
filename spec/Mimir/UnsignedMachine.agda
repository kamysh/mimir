{-# OPTIONS --safe #-}
-- Unsigned arithmetic used by persisted counters. Release wrapping and
-- checked-profile panic are separate outcomes; no unbounded counter is assumed.
module Mimir.UnsignedMachine where

open import Data.Nat using (ℕ; suc; _≤_; _≤?_; _⊓_; _+_; s≤s⁻¹)
open import Data.Nat.Properties using (m⊓n≤n; m≤n⇒m⊓n≡m)
open import Data.Nat.DivMod using (_%_; m%n<n; m≤n⇒m%n≡m)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.SignedMachine as Profile
import Mimir.Binary64 as Binary

module Maximum (maximum : ℕ) where
  record Natural : Set where
    constructor natural
    field number : ℕ; bounded : number ≤ maximum

  wrap : ℕ → Natural
  wrap input = natural (input % suc maximum) (s≤s⁻¹ (m%n<n input (suc maximum)))

  wrapExact : ∀ input → input ≤ maximum → Natural.number (wrap input) ≡ input
  wrapExact input bounded = m≤n⇒m%n≡m bounded

  saturate : ℕ → Natural
  saturate input = natural (input ⊓ maximum) (m⊓n≤n input maximum)

  saturateExact : ∀ input → input ≤ maximum → Natural.number (saturate input) ≡ input
  saturateExact input bounded = m≤n⇒m⊓n≡m bounded

  data Evaluation (input : ℕ) : Set where
    returned : Natural → Evaluation input
    panic : ¬ input ≤ maximum → Evaluation input

  execute : Profile.OverflowChecks → ∀ input → Evaluation input
  execute Profile.disabled input = returned (wrap input)
  execute Profile.enabled input with input ≤? maximum
  ... | yes bounded = returned (natural input bounded)
  ... | no overflow = panic overflow

  checkedReturnExact : ∀ input result → execute Profile.enabled input ≡ returned result → Natural.number result ≡ input
  checkedReturnExact input result observed with input ≤? maximum
  ... | no overflow with observed
  ...   | ()
  checkedReturnExact input result observed | yes bounded with observed
  ... | refl = refl

  increment : Profile.OverflowChecks → (before : Natural) → Evaluation (suc (Natural.number before))
  increment checks before = execute checks (suc (Natural.number before))

module Width (bits : ℕ) = Maximum (Binary.powerMinusOne bits)
