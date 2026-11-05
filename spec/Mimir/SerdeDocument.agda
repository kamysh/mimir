{-# OPTIONS --safe #-}
-- Typed documents require whitespace-only suffixes. Every successful read
-- consumes the complete input; failed visitors and panics bypass this check.
import Mimir.FloatConversion
module Mimir.SerdeDocument (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.List using ([])
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
import Mimir.SerdeFlow as Flow
import Mimir.JsonFlow as JSON
import Mimir.JsonCompletion as CompletionDependency
private
  module Completion = CompletionDependency floatConversion
import Mimir.JsonTreeParser as TreeDependency
private
  module Tree = TreeDependency floatConversion
import Mimir.JsonControls as Controls
import Mimir.SignedMachine as Machine
module F = Flow.F

Complete : ∀ {Value input} → Flow.Result Value input → Set
Complete (Flow.panicked position) = ⊤
Complete (Flow.ordinary (F.failure error)) = ⊤
Complete (Flow.ordinary (F.success value position)) = F.Cursor.remaining position ≡ []

fromJsonComplete : ∀ {Value input} (result : JSON.Result Value input) →
  Completion.Complete result → Complete (Flow.fromJson result)
fromJsonComplete (JSON.ordinary (JSON.F.success value position)) complete = complete
fromJsonComplete (JSON.ordinary (JSON.F.failure error)) complete = tt
fromJsonComplete (JSON.panicked position) complete = tt

prefixComplete : ∀ {Value input} (before : F.Cursor input) (result : Flow.Result Value (F.Cursor.remaining before)) →
  Complete result → Complete (Flow.prefix before result)
prefixComplete before (Flow.ordinary (F.success value position)) complete = complete
prefixComplete before (Flow.ordinary (F.failure error)) complete = tt
prefixComplete before (Flow.panicked position) complete = tt

mapComplete : ∀ {First Second input} (change : First → Second) (result : Flow.Result First input) →
  Complete result → Complete (Flow.map change result)
mapComplete change (Flow.ordinary (F.success value position)) complete = complete
mapComplete change (Flow.ordinary (F.failure error)) complete = tt
mapComplete change (Flow.panicked position) complete = tt

andThenComplete : ∀ {First Second input} (result : Flow.Result First input)
  (next : First → ∀ rest → Flow.Result Second rest) →
  (∀ value rest → Complete (next value rest)) → Complete (Flow.andThen result next)
andThenComplete (Flow.ordinary (F.success value position)) next complete = prefixComplete position (next value (F.Cursor.remaining position)) (complete value (F.Cursor.remaining position))
andThenComplete (Flow.ordinary (F.failure error)) next complete = tt
andThenComplete (Flow.panicked position) next complete = tt

module Parser (checks : Machine.OverflowChecks) where
  module T = Tree.Parser checks
  module C = Completion.For checks

  finish : ∀ input → Flow.Result ⊤ input
  finish input = Flow.lift (Controls.skipWhitespace input T.endAt)

  finishComplete : ∀ input → Complete (finish input)
  finishComplete input = fromJsonComplete (JSON.lift (Controls.skipWhitespace input T.endAt))
    (Completion.liftComplete (Controls.skipWhitespace input T.endAt) (C.whitespaceEndComplete input))

  read : ∀ {Value} → Flow.Parser Value → Flow.Parser Value
  read child input = Flow.bindProductive (child input) λ value rest → Flow.map (λ unit → value) (finish rest)

  readComplete : ∀ {Value} (child : Flow.Parser Value) input → Complete (Flow.Productive.result (read child input))
  readComplete child input = andThenComplete (Flow.Productive.result (child input))
    (λ value rest → Flow.map (λ unit → value) (finish rest))
    (λ value rest → mapComplete (λ unit → value) (finish rest) (finishComplete rest))

  successExhausts : ∀ {Value} (child : Flow.Parser Value) input value position →
    Flow.Productive.result (read child input) ≡ Flow.ordinary (F.success value position) → F.Cursor.remaining position ≡ []
  successExhausts child input value position observed = subst Complete observed (readComplete child input)

  firstFailurePreserved : ∀ {Value} (child : Flow.Parser Value) input error →
    Flow.Productive.result (child input) ≡ Flow.ordinary (F.failure error) →
    Flow.Productive.result (read child input) ≡ Flow.ordinary (F.failure error)
  firstFailurePreserved child input error failed rewrite failed = refl
