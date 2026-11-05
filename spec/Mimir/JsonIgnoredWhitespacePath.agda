{-# OPTIONS --safe #-}
-- Leading JSON whitespace prefixes the first real transition, not a new state.
import Mimir.FloatConversion
module Mimir.JsonIgnoredWhitespacePath (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
open import Data.Product using (Σ; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans)
open import Mimir.Bits using (Byte)
import Mimir.JsonIgnoredStep as StepDependency
private
  module Step = StepDependency floatConversion
import Mimir.JsonIgnoredPath as PathDependency
private
  module Path = PathDependency floatConversion
import Mimir.JsonWhitespace as White
module C = Step.C

sameSuccess : ∀ {Value input} (value : Value) before after (first second : input ≡ before ++ after) →
  C.success value before after first ≡ C.success value before after second
sameSuccess value before after refl refl = refl

sameFailure : ∀ {Value input} code before after (first second : input ≡ before ++ after) →
  C.failure {Value = Value} code before after first ≡ C.failure code before after second
sameFailure code before after refl refl = refl

prefixCons : ∀ {Value input} byte before (result : C.Result Value input) →
  C.prefix (byte ∷ before) result ≡ C.prefix (byte ∷ []) (C.prefix before result)
prefixCons byte before (C.success value consumed remaining exact) = sameSuccess value (byte ∷ before ++ consumed) remaining _ _
prefixCons byte before (C.failure code consumed remaining exact) = sameFailure code (byte ∷ before ++ consumed) remaining _ _

skipSpace : ∀ byte → White.Space byte → ∀ input action →
  Step.Step.result (Step.skip (byte ∷ input) action) ≡
  C.prefix (byte ∷ []) (Step.Step.result (Step.skip input action))
skipSpace byte admitted input action with White.space? byte
... | no refused = ⊥-elim (refused admitted)
... | yes checked with White.take input
...   | White.run before spaces rest refl stopped with action rest
...     | Step.step result progress = prefixCons byte before result

data Skips : Step.State → Set where
  atValue : ∀ frames → Skips (Step.value frames)
  atKey : ∀ frames → Skips (Step.key frames)
  inContainer : ∀ frame frames comma → Skips (Step.boundary (frame ∷ frames) comma)

transitionSpace : ∀ {state} → Skips state → ∀ byte → White.Space byte → ∀ input →
  Step.Step.result (Step.transition state (byte ∷ input)) ≡
  C.prefix (byte ∷ []) (Step.Step.result (Step.transition state input))
transitionSpace (atValue frames) byte admitted input = skipSpace byte admitted input (Step.valueAt frames)
transitionSpace (atKey frames) byte admitted input = skipSpace byte admitted input (Step.keyAt frames)
transitionSpace (inContainer frame frames comma) byte admitted input = skipSpace byte admitted input (Step.boundaryAt frame frames comma)

data Started {state input target suffix} : Path.Path state input target suffix → Set where
  started : ∀ {following consumed remaining exact observed tail} →
    Started (Path.next following consumed remaining exact observed tail)

different : ∀ {state input target suffix} → state ≢ target →
  (path : Path.Path state input target suffix) → Started path
different unequal Path.stop = ⊥-elim (unequal refl)
different unequal (Path.next following consumed remaining exact observed tail) = started

appendStarted : ∀ {state input middle rest target suffix}
  (first : Path.Path state input middle rest) → Started first →
  (second : Path.Path middle rest target suffix) → Started (Path.append first second)
appendStarted (Path.next following consumed remaining exact observed tail) started second = started

space : ∀ {state input target suffix} → Skips state → ∀ byte → White.Space byte →
  (path : Path.Path state input target suffix) → Started path →
  Σ (Path.Path state (byte ∷ input) target suffix) Started
space skips byte admitted (Path.next following consumed remaining exact observed tail) started = Path.next following (byte ∷ consumed) remaining _
  (trans (transitionSpace skips byte admitted _)
   (cong (C.prefix (byte ∷ [])) observed))
  tail
  , started

spaces : ∀ {state input target suffix} → Skips state → ∀ before → All White.Space before →
  (path : Path.Path state input target suffix) → Started path →
  Σ (Path.Path state (before ++ input) target suffix) Started
spaces skips [] All.[] path positive = path , positive
spaces skips (byte ∷ before) (admitted All.∷ valid) path positive
  with spaces skips before valid path positive
... | following , begun = space skips byte admitted following begun
