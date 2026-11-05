{-# OPTIONS --safe #-}
-- A terminating execution of the ignored-value transition protocol. The
-- recursion measure is input length, not an externally imposed parser limit.
import Mimir.FloatConversion
module Mimir.JsonIgnoredRun (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _++_; length)
open import Data.Nat using (ℕ; zero; suc; _≤_; s≤s⁻¹)
open import Data.Nat.Properties using (≤-trans; ≤-refl)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Mimir.Bits using (Byte)
import Mimir.JsonIgnoredStep as SDependency
private
  module S = SDependency floatConversion
import Mimir.JsonControls as Controls
import Mimir.CursorProgress as Progress
module C = Controls.C
module P = Progress.Over Byte Controls.Code

data Execution (state : S.State) (input : List Byte) : C.Result ⊤ input → Set where
  rejected : ∀ code consumed remaining exact →
    S.Step.result (S.transition state input) ≡ C.failure code consumed remaining exact →
    Execution state input (C.failure code consumed remaining exact)
  completed : ∀ consumed remaining exact →
    S.Step.result (S.transition state input) ≡ C.success S.finished consumed remaining exact →
    Execution state input (C.success tt consumed remaining exact)
  continued : ∀ following consumed remaining exact →
    S.Step.result (S.transition state input) ≡ C.success (S.next following) consumed remaining exact →
    ∀ result → Execution following remaining result →
    Execution state input (C.reframe exact (C.prefix consumed result))

record Checked (state : S.State) (input : List Byte) : Set where
  constructor checked
  field result : C.Result ⊤ input; execution : Execution state input result

oneNotZero : 1 ≤ 0 → ⊥
oneNotZero ()

nextBound : ∀ fuel {input} (result : C.Result S.Move input) →
  1 ≤ length (C.consumed result) → length input ≤ suc fuel →
  length (C.remaining result) ≤ fuel
nextBound fuel result positive bounded =
  s≤s⁻¹ (≤-trans (P.positiveRemaining result positive) bounded)

noNextAtZero : ∀ {input} (result : C.Result S.Move input) →
  1 ≤ length (C.consumed result) → length input ≤ zero → ⊥
noNextAtZero result positive bounded =
  oneNotZero (≤-trans positive (≤-trans (C.offsetBound result) bounded))

run : ∀ fuel state input → length input ≤ fuel → Checked state input
run zero state input bounded with S.transition state input in equation
... | S.step (C.failure code consumed remaining exact) progress =
  checked (C.failure code consumed remaining exact)
    (rejected code consumed remaining exact (cong S.Step.result equation))
... | S.step (C.success S.finished consumed remaining exact) progress =
  checked (C.success tt consumed remaining exact)
    (completed consumed remaining exact (cong S.Step.result equation))
... | S.step result@(C.success (S.next following) consumed remaining exact) progress =
  ⊥-elim (noNextAtZero result progress bounded)
run (suc fuel) state input bounded with S.transition state input in equation
... | S.step (C.failure code consumed remaining exact) progress =
  checked (C.failure code consumed remaining exact)
    (rejected code consumed remaining exact (cong S.Step.result equation))
... | S.step (C.success S.finished consumed remaining exact) progress =
  checked (C.success tt consumed remaining exact)
    (completed consumed remaining exact (cong S.Step.result equation))
... | S.step result@(C.success (S.next following) consumed remaining exact) progress
  with run fuel following remaining (nextBound fuel result progress bounded)
... | checked parsed executed = checked (C.reframe exact (C.prefix consumed parsed))
    (continued following consumed remaining exact (cong S.Step.result equation) parsed executed)

scan : ∀ input → Checked (S.value []) input
scan input = run (length input) (S.value []) input ≤-refl

read : ∀ input → C.Result ⊤ input
read input = Checked.result (scan input)

faithful : ∀ input → Execution (S.value []) input (read input)
faithful input = Checked.execution (scan input)

deterministic : ∀ {state input first second} → Execution state input first →
  Execution state input second → first ≡ second
deterministic (rejected code consumed remaining exact first)
  (rejected other consumed′ remaining′ exact′ second) with trans (sym first) second
... | refl = refl
deterministic (rejected code consumed remaining exact first)
  (completed consumed′ remaining′ exact′ second) with trans (sym first) second
... | ()
deterministic (rejected code consumed remaining exact first)
  (continued following consumed′ remaining′ exact′ second result tail) with trans (sym first) second
... | ()
deterministic (completed consumed remaining exact first)
  (rejected code consumed′ remaining′ exact′ second) with trans (sym first) second
... | ()
deterministic (completed consumed remaining exact first)
  (completed consumed′ remaining′ exact′ second) with trans (sym first) second
... | refl = refl
deterministic (completed consumed remaining exact first)
  (continued following consumed′ remaining′ exact′ second result tail) with trans (sym first) second
... | ()
deterministic (continued following consumed remaining exact first result tail)
  (rejected code consumed′ remaining′ exact′ second) with trans (sym first) second
... | ()
deterministic (continued following consumed remaining exact first result tail)
  (completed consumed′ remaining′ exact′ second) with trans (sym first) second
... | ()
deterministic (continued following consumed remaining exact first result tail)
  (continued following′ consumed′ remaining′ exact′ second result′ tail′) with trans (sym first) second
... | refl = cong (λ parsed → C.reframe exact (C.prefix consumed parsed)) (deterministic tail tail′)

-- Every sufficiently large recursion measure gives the same result, including
-- the same consumed prefix and failure position.
measureIndependent : ∀ first second state input firstBound secondBound →
  Checked.result (run first state input firstBound) ≡
  Checked.result (run second state input secondBound)
measureIndependent first second state input firstBound secondBound = deterministic
  (Checked.execution (run first state input firstBound))
  (Checked.execution (run second state input secondBound))

complete : ∀ input result → Execution (S.value []) input result → read input ≡ result
complete input result executed = deterministic (faithful input) executed
