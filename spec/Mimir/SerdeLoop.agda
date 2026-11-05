{-# OPTIONS --safe #-}
-- A typed visitor state machine terminates by consuming bytes. The internal
-- recursion measure is not an input limit and does not alter the result.
module Mimir.SerdeLoop where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; length)
open import Data.Nat using (ℕ; zero; suc; _≤_; s≤s⁻¹)
open import Data.Nat.Properties using (≤-trans; ≤-refl)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Mimir.Bits using (Byte)
import Mimir.SerdeFlow as Flow
module F = Flow.F

Advances : ∀ {State Value input} → Flow.Result (State ⊎ Value) input → Set
Advances (Flow.ordinary (F.success (inj₁ state) position)) = 1 ≤ length (F.Cursor.consumed position)
Advances (Flow.ordinary (F.success (inj₂ value) position)) = ⊤
Advances (Flow.ordinary (F.failure error)) = ⊤
Advances (Flow.panicked position) = ⊤

record Step (State Value : Set) (input : List Byte) : Set where
  constructor step
  field result : Flow.Result (State ⊎ Value) input; advances : Advances result

continuingProgress : ∀ {First State Value input} (next : First → State) (result : Flow.Result First input) →
  Flow.Progress result → Advances (Flow.map (λ value → inj₁ {B = Value} (next value)) result)
continuingProgress next (Flow.ordinary (F.success value position)) progress = progress
continuingProgress next (Flow.ordinary (F.failure error)) progress = tt
continuingProgress next (Flow.panicked position) progress = tt

continuing : ∀ {First State Value input} → (First → State) → Flow.Productive First input → Step State Value input
continuing next (Flow.productive result progress) =
  step (Flow.map (λ value → inj₁ (next value)) result) (continuingProgress next result progress)

nextBound : ∀ fuel {input} (position : F.Cursor input) →
  1 ≤ length (F.Cursor.consumed position) → length input ≤ suc fuel →
  length (F.Cursor.remaining position) ≤ fuel
nextBound fuel position positive bounded = s≤s⁻¹ (≤-trans (Flow.positiveRemaining position positive) bounded)

zeroImpossible : ∀ {input} (position : F.Cursor input) →
  1 ≤ length (F.Cursor.consumed position) → length input ≤ zero → ⊥
zeroImpossible position positive bounded = Data.Nat.Properties.n≮0 (≤-trans (Flow.positiveRemaining position positive) bounded)

module Machine (State Value : Set) (transition : State → ∀ input → Step State Value input) where
  data Execution (state : State) (input : List Byte) : Flow.Result Value input → Set where
    rejected : ∀ error → Step.result (transition state input) ≡ Flow.ordinary (F.failure error) →
      Execution state input (Flow.ordinary (F.failure error))
    panicked : ∀ position → Step.result (transition state input) ≡ Flow.panicked position →
      Execution state input (Flow.panicked position)
    completed : ∀ value position → Step.result (transition state input) ≡ Flow.ordinary (F.success (inj₂ value) position) →
      Execution state input (Flow.ordinary (F.success value position))
    continued : ∀ following position → Step.result (transition state input) ≡ Flow.ordinary (F.success (inj₁ following) position) →
      ∀ result → Execution following (F.Cursor.remaining position) result →
      Execution state input (Flow.prefix position result)

  record Checked (state : State) (input : List Byte) : Set where
    constructor checked
    field result : Flow.Result Value input; execution : Execution state input result

  run : ∀ fuel state input → length input ≤ fuel → Checked state input
  run zero state input bounded with transition state input in equation
  ... | step (Flow.ordinary (F.failure error)) progress =
    checked (Flow.ordinary (F.failure error)) (rejected error (cong Step.result equation))
  ... | step (Flow.panicked position) progress =
    checked (Flow.panicked position) (panicked position (cong Step.result equation))
  ... | step (Flow.ordinary (F.success (inj₂ value) position)) progress =
    checked (Flow.ordinary (F.success value position)) (completed value position (cong Step.result equation))
  ... | step (Flow.ordinary (F.success (inj₁ following) position)) progress =
    ⊥-elim (zeroImpossible position progress bounded)
  run (suc fuel) state input bounded with transition state input in equation
  ... | step (Flow.ordinary (F.failure error)) progress =
    checked (Flow.ordinary (F.failure error)) (rejected error (cong Step.result equation))
  ... | step (Flow.panicked position) progress =
    checked (Flow.panicked position) (panicked position (cong Step.result equation))
  ... | step (Flow.ordinary (F.success (inj₂ value) position)) progress =
    checked (Flow.ordinary (F.success value position)) (completed value position (cong Step.result equation))
  ... | step (Flow.ordinary (F.success (inj₁ following) position)) progress
    with run fuel following (F.Cursor.remaining position) (nextBound fuel position progress bounded)
  ... | checked result executed =
    checked (Flow.prefix position result) (continued following position (cong Step.result equation) result executed)

  scan : ∀ state input → Checked state input
  scan state input = run (length input) state input ≤-refl

  read : State → ∀ input → Flow.Result Value input
  read state input = Checked.result (scan state input)

  faithful : ∀ state input → Execution state input (read state input)
  faithful state input = Checked.execution (scan state input)

  deterministic : ∀ {state input first second} → Execution state input first →
    Execution state input second → first ≡ second
  deterministic (rejected error first) (rejected other second) with trans (sym first) second
  ... | refl = refl
  deterministic (rejected error first) (panicked position second) with trans (sym first) second
  ... | ()
  deterministic (rejected error first) (completed value position second) with trans (sym first) second
  ... | ()
  deterministic (rejected error first) (continued following position second result tail) with trans (sym first) second
  ... | ()
  deterministic (panicked position first) (rejected error second) with trans (sym first) second
  ... | ()
  deterministic (panicked position first) (panicked other second) with trans (sym first) second
  ... | refl = refl
  deterministic (panicked position first) (completed value other second) with trans (sym first) second
  ... | ()
  deterministic (panicked position first) (continued following other second result tail) with trans (sym first) second
  ... | ()
  deterministic (completed value position first) (rejected error second) with trans (sym first) second
  ... | ()
  deterministic (completed value position first) (panicked other second) with trans (sym first) second
  ... | ()
  deterministic (completed value position first) (completed other after second) with trans (sym first) second
  ... | refl = refl
  deterministic (completed value position first) (continued following other second result tail) with trans (sym first) second
  ... | ()
  deterministic (continued following position first result tail) (rejected error second) with trans (sym first) second
  ... | ()
  deterministic (continued following position first result tail) (panicked other second) with trans (sym first) second
  ... | ()
  deterministic (continued following position first result tail) (completed value other second) with trans (sym first) second
  ... | ()
  deterministic (continued following position first result tail)
    (continued next after second output rest) with trans (sym first) second
  ... | refl = cong (Flow.prefix position) (deterministic tail rest)

  measureIndependent : ∀ first second state input firstBound secondBound →
    Checked.result (run first state input firstBound) ≡ Checked.result (run second state input secondBound)
  measureIndependent first second state input firstBound secondBound =
    deterministic (Checked.execution (run first state input firstBound)) (Checked.execution (run second state input secondBound))

  complete : ∀ state input result → Execution state input result → read state input ≡ result
  complete state input result executed = deterministic (faithful state input) executed
