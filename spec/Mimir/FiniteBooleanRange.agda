{-# OPTIONS --safe #-}
-- Balanced exhaustive decision over a finite natural-number interval. The
-- general elimination law turns the closed Boolean computation into a proof
-- for every member; there is no sampling or trusted external certificate.
module Mimir.FiniteBooleanRange where

open import Data.Bool using (Bool; true; false; _∧_; T)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _<_; _<?_; s≤s⁻¹)
open import Data.Nat.Properties using (≤-antisym; ≮⇒≥; +-assoc; +-identityʳ; +-suc)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import Data.Unit using (tt)
open import Agda.Builtin.Strict using (primForce; primForceLemma)

span : ℕ → ℕ
span zero = 1
span (suc width) = 2 * span width

rangeEnd : ∀ start width → start + span (suc width) ≡ (start + span width) + span width
rangeEnd start width = trans (cong (λ size → start + size)
  (cong (span width +_) (+-identityʳ (span width)))) (sym (+-assoc start (span width) (span width)))

firstTrue : ∀ first second → T (first ∧ second) → T first
firstTrue true second proof = tt
firstTrue false second ()

secondTrue : ∀ first second → T (first ∧ second) → T second
secondTrue true second proof = proof
secondTrue false second ()

bothTrue : ∀ first second → T first → T second → T (first ∧ second)
bothTrue true second firstProof secondProof = secondProof
bothTrue false second () secondProof

singleton : ∀ start number → start ≤ number → number < start + 1 → start ≡ number
singleton start number lower upper = ≤-antisym lower
  (s≤s⁻¹ (subst (number <_) (trans (+-suc start 0) (Data.Nat.Properties.+-identityʳ (suc start))) upper))

module Check (predicate : ℕ → Bool) where
  all : ℕ → ℕ → Bool
  all zero start = predicate start
  all (suc width) start = all width start ∧ primForce (start + span width) (all width)

  join : ∀ width start → T (all width start) → T (all width (start + span width)) → T (all (suc width) start)
  join width start first second rewrite primForceLemma (start + span width) (all width) =
    bothTrue (all width start) (all width (start + span width)) first second

  every : ∀ width start → T (all width start) → ∀ number →
    start ≤ number → number < start + span width → T (predicate number)
  every zero start checked number lower upper rewrite sym (singleton start number lower upper) = checked
  every (suc width) start checked number lower upper
    rewrite primForceLemma (start + span width) (all width)
    with number <? start + span width
  ... | yes left = every width start (firstTrue (all width start) (all width (start + span width)) checked)
      number lower left
  ... | no right = every width (start + span width)
      (secondTrue (all width start) (all width (start + span width)) checked)
      number (≮⇒≥ right) (subst (number <_) (rangeEnd start width) upper)
