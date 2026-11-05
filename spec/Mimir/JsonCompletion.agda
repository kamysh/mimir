{-# OPTIONS --safe #-}
-- Every successful document parse consumes the complete supplied byte string.
import Mimir.FloatConversion
module Mimir.JsonCompletion (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.List using ([]; _∷_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.JsonControls as Controls
import Mimir.JsonWhitespace as White
import Mimir.JsonFlow as Flow
import Mimir.JsonTreeParser as ParserDependency
private
  module Parser = ParserDependency floatConversion
import Mimir.SignedMachine as Machine
module F = Flow.F
module C = Controls.C

AtomicComplete : ∀ {Value input} → C.Result Value input → Set
AtomicComplete (C.success value consumed remaining exact) = remaining ≡ []
AtomicComplete (C.failure code consumed remaining exact) = ⊤

Complete : ∀ {Value input} → Flow.Result Value input → Set
Complete (Flow.panicked position) = ⊤
Complete (Flow.ordinary (F.failure error)) = ⊤
Complete (Flow.ordinary (F.success value position)) = F.Cursor.remaining position ≡ []

atomicPrefix : ∀ {Value input} bytes (result : C.Result Value input) → AtomicComplete result → AtomicComplete (C.prefix bytes result)
atomicPrefix bytes (C.success value consumed remaining exact) complete = complete
atomicPrefix bytes (C.failure code consumed remaining exact) complete = tt

atomicReframe : ∀ {Value input source} (exact : input ≡ source) (result : C.Result Value source) →
  AtomicComplete result → AtomicComplete (C.reframe exact result)
atomicReframe refl result complete = complete

liftComplete : ∀ {Value input} (result : C.Result Value input) → AtomicComplete result → Complete (Flow.lift result)
liftComplete (C.success value consumed remaining exact) complete = complete
liftComplete (C.failure code consumed remaining exact) complete = tt

prefixComplete : ∀ {Value input} (before : F.Cursor input) (result : Flow.Result Value (F.Cursor.remaining before)) →
  Complete result → Complete (Flow.prefix before result)
prefixComplete before (Flow.panicked position) complete = tt
prefixComplete before (Flow.ordinary (F.failure error)) complete = tt
prefixComplete before (Flow.ordinary (F.success value position)) complete = complete

mapComplete : ∀ {First Second input} (change : First → Second) (result : Flow.Result First input) → Complete result → Complete (Flow.map change result)
mapComplete change (Flow.panicked position) complete = tt
mapComplete change (Flow.ordinary (F.failure error)) complete = tt
mapComplete change (Flow.ordinary (F.success value position)) complete = complete

andThenComplete : ∀ {First Second input} (first : Flow.Result First input) (next : First → ∀ rest → Flow.Result Second rest) →
  (∀ value rest → Complete (next value rest)) → Complete (Flow.andThen first next)
andThenComplete (Flow.panicked position) next complete = tt
andThenComplete (Flow.ordinary (F.failure error)) next complete = tt
andThenComplete (Flow.ordinary (F.success value before)) next complete =
  prefixComplete before (next value (F.Cursor.remaining before)) (complete value (F.Cursor.remaining before))

bindProductiveComplete : ∀ {First Second input} (first : Flow.Productive First input) (next : First → ∀ rest → Flow.Result Second rest) →
  (∀ value rest → Complete (next value rest)) → Complete (Flow.Productive.result (Flow.bindProductive first next))
bindProductiveComplete (Flow.productive result progress) next complete = andThenComplete result next complete

mapProductiveComplete : ∀ {First Second input} (change : First → Second) (first : Flow.Productive First input) →
  Complete (Flow.Productive.result first) → Complete (Flow.Productive.result (Flow.mapProductive change first))
mapProductiveComplete change (Flow.productive result progress) complete = mapComplete change result complete

module For (checks : Machine.OverflowChecks) where
  module P = Parser.Parser checks

  endComplete : ∀ input → AtomicComplete (P.endAt input)
  endComplete [] = refl
  endComplete (byte ∷ rest) = tt

  whitespaceEndComplete : ∀ input → AtomicComplete (Controls.skipWhitespace input P.endAt)
  whitespaceEndComplete input with White.take input
  ... | White.run consumed spaces remaining exact stopped =
      atomicReframe exact (C.prefix consumed (P.endAt remaining)) (atomicPrefix consumed (P.endAt remaining) (endComplete remaining))

  boundedDocumentComplete : ∀ input → Complete (Flow.Productive.result (P.boundedDocument input))
  boundedDocumentComplete input = bindProductiveComplete (P.value 127 input)
    (λ tree rest → Flow.map (λ unit → tree) (Flow.lift (Controls.skipWhitespace rest P.endAt)))
    (λ tree rest → mapComplete (λ unit → tree) (Flow.lift (Controls.skipWhitespace rest P.endAt))
      (liftComplete (Controls.skipWhitespace rest P.endAt) (whitespaceEndComplete rest)))
