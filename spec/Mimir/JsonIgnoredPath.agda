{-# OPTIONS --safe #-}
-- Finite successful transition segments compose with any later execution.
import Mimir.FloatConversion
module Mimir.JsonIgnoredPath (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Bool using (true)
open import Data.List using (List; []; _++_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; trans)
open import Mimir.Bits using (Byte)
import Mimir.JsonIgnoredStep as StepDependency
private
  module Step = StepDependency floatConversion
import Mimir.JsonIgnoredRun as RunDependency
private
  module Run = RunDependency floatConversion
import Mimir.SerdeFlow as Flow
import Mimir.SerdeReadBack as Back
module C = Step.C

data Path (state : Step.State) (input : List Byte) : Step.State → List Byte → Set where
  stop : Path state input state input
  next : ∀ following consumed remaining exact →
    Step.Step.result (Step.transition state input) ≡ C.success (Step.next following) consumed remaining exact →
    ∀ {target suffix} → Path following remaining target suffix → Path state input target suffix

fromResult : ∀ state target input (result : C.Result ⊤ input) suffix →
  Back.Returned (Flow.lift result) tt suffix →
  Step.Step.result (Step.transition state input) ≡ C.prefix [] (Step.advance target result) →
  Path state input target suffix
fromResult state target input (C.failure code consumed remaining exact) suffix (Back.returned position () end) equation
fromResult state target input (C.success tt consumed remaining exact) suffix (Back.returned position refl end) equation = subst (Path state input target) end
  (next target consumed remaining _ equation stop)

append : ∀ {state input middle rest target suffix} → Path state input middle rest →
  Path middle rest target suffix → Path state input target suffix
append stop second = second
append (next following consumed remaining exact observed tail) second = next following consumed remaining exact observed
  (append tail second)

prepend : ∀ {Value state input target suffix} → Path state input target suffix →
  C.Result Value suffix → C.Result Value input
prepend stop result = result
prepend (next following consumed remaining exact observed tail) result =
  C.reframe exact (C.prefix consumed (prepend tail result))

continue : ∀ {state input target suffix} (path : Path state input target suffix) result →
  Run.Execution target suffix result → Run.Execution state input (prepend path result)
continue stop result executed = executed
continue (next following consumed remaining exact observed tail) result executed = Run.continued following consumed remaining exact observed
  (prepend tail result) (continue tail result executed)

prefixRemaining : ∀ {Value input} consumed remaining (exact : input ≡ consumed ++ remaining)
  (result : C.Result Value remaining) →
  C.remaining (C.reframe exact (C.prefix consumed result)) ≡ C.remaining result
prefixRemaining consumed remaining refl (C.success value before after exact) = refl
prefixRemaining consumed remaining refl (C.failure code before after exact) = refl

remaining : ∀ {Value state input target suffix} (path : Path state input target suffix)
  (result : C.Result Value suffix) → C.remaining (prepend path result) ≡ C.remaining result
remaining stop result = refl
remaining (next following consumed middle exact observed tail) result = trans (prefixRemaining consumed middle exact (prepend tail result))
  (remaining tail result)

prefixSuccess : ∀ {input suffix} consumed middle (exact : input ≡ consumed ++ middle)
  (result : C.Result ⊤ middle) → Back.Returned (Flow.lift result) tt suffix →
  Back.Returned (Flow.lift (C.reframe exact (C.prefix consumed result))) tt suffix
prefixSuccess consumed middle refl (C.failure code before after exact) (Back.returned position () end)
prefixSuccess consumed middle refl (C.success tt before after exact) (Back.returned position refl end) = Back.returned _ refl end

success : ∀ {state input target suffix end} (path : Path state input target suffix)
  (result : C.Result ⊤ suffix) → Back.Returned (Flow.lift result) tt end →
  Back.Returned (Flow.lift (prepend path result)) tt end
success stop result receipt = receipt
success (next following consumed middle exact observed tail) result receipt = prefixSuccess consumed middle exact (prepend tail result)
  (success tail result receipt)

closed : ∀ input suffix → Path (Step.value []) input (Step.boundary [] true) suffix →
  Back.Returned (Flow.lift (Run.read input)) tt suffix
closed input suffix path = subst (λ result → Back.Returned (Flow.lift result) tt suffix)
  (sym
   (Run.complete input (prepend path (C.done tt suffix))
    (continue path (C.done tt suffix)
     (Run.completed [] suffix refl refl))))
  (success path (C.done tt suffix)
   (Back.returned (Flow.F.initial suffix) refl refl))
