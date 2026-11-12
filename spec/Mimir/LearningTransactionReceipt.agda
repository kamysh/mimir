{-# OPTIONS --safe #-}
-- A reported fresh success must have an observed commit acknowledgement.
-- Asking to commit or writing successfully cannot supply this receipt.
module Mimir.LearningTransactionReceipt where

open import Data.List using (List; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.LearningTransaction as Transaction

module Over (State Value Failure : Set) (database key : ℕ) where
  module T = Transaction.Over State Value Failure database key
  open T

  Receipt : List E.Event → Set
  Receipt events = Σ Transaction (λ tx → Any (_≡ (commit tx , committed)) events)

  prepend : ∀ event {events} → Receipt events → Receipt (event ∷ events)
  prepend event (tx , member) = tx , there member

  writeReceipt : ∀ tx value reply events actual →
    E.Runs (afterWrite tx value reply) events (applied actual) → Receipt events
  writeReceipt tx value (inj₁ detail) events actual (E.replied _ _ cleanup ())
  writeReceipt tx value (inj₂ tt) events actual (E.replied _ _ committed (E.returned _)) = tx , here refl
  writeReceipt tx value (inj₂ tt) events actual (E.replied _ _ (aborted detail) ())

  decisionReceipt : ∀ tx decision events actual →
    E.Runs (decide tx decision) events (applied actual) → Receipt events
  decisionReceipt tx (reject detail) events actual (E.replied _ _ cleanup ())
  decisionReceipt tx (replay value) events actual (E.replied _ _ cleanup ())
  decisionReceipt tx (replace proposed value) events actual (E.replied _ _ reply execution) = prepend (write tx proposed , reply)
    (writeReceipt tx value reply _ actual execution)

  allocationReceipt : ∀ tx plan events actual →
    E.Runs (executeAllocation tx plan) events (applied actual) → Receipt events
  allocationReceipt tx (resolved decision) events actual execution = decisionReceipt tx decision events actual execution
  allocationReceipt tx (reserve experience name source actor next) events actual (E.replied _ _ reply execution) =
    prepend (allocateItem tx experience name source actor , reply) (allocationReceipt tx (next reply) _ actual execution)

  module WithPreparedPlan (plan : State → Allocation Decision) where
    open T.PreparedPlan plan

    readReceipt : ∀ tx reply events actual →
      E.Runs (afterRead tx reply) events (applied actual) → Receipt events
    readReceipt tx (inj₁ detail) events actual (E.replied _ _ cleanup ())
    readReceipt tx (inj₂ before) events actual execution = allocationReceipt tx (plan before) events actual execution

    lockReceipt : ∀ tx reply events actual →
      E.Runs (afterLock tx reply) events (applied actual) → Receipt events
    lockReceipt tx (inj₁ detail) events actual (E.replied _ _ cleanup ())
    lockReceipt tx (inj₂ tt) events actual (E.replied _ _ reply execution) =
      prepend (read tx , reply) (readReceipt tx reply _ actual execution)

    beginReceipt : ∀ reply events actual →
      E.Runs (afterBegin reply) events (applied actual) → Receipt events
    beginReceipt (inj₂ tx) events actual (E.replied _ _ reply execution) =
      prepend (acquire tx key , reply) (lockReceipt tx reply _ actual execution)

    successRequiresCommit : ∀ events actual → E.Runs start events (applied actual) → Receipt events
    successRequiresCommit events actual (E.replied _ _ reply execution) =
      prepend (begin database , reply) (beginReceipt reply _ actual execution)

  module WithPlan (plan : State → Decision) where
    open T.Plan plan

    readReceipt : ∀ tx reply events actual →
      E.Runs (afterRead tx reply) events (applied actual) → Receipt events
    readReceipt tx (inj₁ detail) events actual (E.replied _ _ cleanup ())
    readReceipt tx (inj₂ before) events actual execution = decisionReceipt tx (plan before) events actual execution

    lockReceipt : ∀ tx reply events actual →
      E.Runs (afterLock tx reply) events (applied actual) → Receipt events
    lockReceipt tx (inj₁ detail) events actual (E.replied _ _ cleanup ())
    lockReceipt tx (inj₂ tt) events actual (E.replied _ _ reply execution) = prepend (read tx , reply) (readReceipt tx reply _ actual execution)

    beginReceipt : ∀ reply events actual →
      E.Runs (afterBegin reply) events (applied actual) → Receipt events
    beginReceipt (inj₂ tx) events actual (E.replied _ _ reply execution) = prepend (acquire tx key , reply)
      (lockReceipt tx reply _ actual execution)

    successRequiresCommit : ∀ events actual → E.Runs start events (applied actual) → Receipt events
    successRequiresCommit events actual (E.replied _ _ reply execution) = prepend (begin database , reply)
      (beginReceipt reply _ actual execution)
