{-# OPTIONS --safe #-}
-- Compositional success invariants for typed visitors. Errors and panics
-- carry no value; successful values must satisfy the stated predicate.
module Mimir.SerdeSuccess where

open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.SerdeFlow as Flow
import Mimir.Validation as V
module F = Flow.F

Ensures : ∀ {Value input} → (Value → Set) → Flow.Result Value input → Set
Ensures property (Flow.ordinary (F.success value position)) = property value
Ensures property (Flow.ordinary (F.failure error)) = ⊤
Ensures property (Flow.panicked position) = ⊤

trivial : ∀ {Value input} (result : Flow.Result Value input) → Ensures (λ _ → ⊤) result
trivial (Flow.ordinary (F.success value position)) = tt
trivial (Flow.ordinary (F.failure error)) = tt
trivial (Flow.panicked position) = tt

prefix : ∀ {Value input} (property : Value → Set) (before : F.Cursor input)
  (result : Flow.Result Value (F.Cursor.remaining before)) →
  Ensures property result → Ensures property (Flow.prefix before result)
prefix property before (Flow.ordinary (F.success value position)) holds = holds
prefix property before (Flow.ordinary (F.failure error)) holds = tt
prefix property before (Flow.panicked position) holds = tt

map : ∀ {First Second input} (before : First → Set) (after : Second → Set) (change : First → Second) →
  (∀ value → before value → after (change value)) → (result : Flow.Result First input) →
  Ensures before result → Ensures after (Flow.map change result)
map before after change preserves (Flow.ordinary (F.success value position)) holds = preserves value holds
map before after change preserves (Flow.ordinary (F.failure error)) holds = tt
map before after change preserves (Flow.panicked position) holds = tt

andThen : ∀ {First Second input} (before : First → Set) (after : Second → Set)
  (result : Flow.Result First input) (next : First → ∀ rest → Flow.Result Second rest) →
  Ensures before result → (∀ value → before value → ∀ rest → Ensures after (next value rest)) →
  Ensures after (Flow.andThen result next)
andThen before after (Flow.ordinary (F.success value position)) next holds preserves = prefix after position (next value (F.Cursor.remaining position)) (preserves value holds (F.Cursor.remaining position))
andThen before after (Flow.ordinary (F.failure error)) next holds preserves = tt
andThen before after (Flow.panicked position) next holds preserves = tt

validate : ∀ {First Second input} (check : First → V.Fault ⊎ Second) (property : Second → Set) →
  (∀ value output → check value ≡ inj₂ output → property output) →
  (parsed : Flow.Productive First input) → Ensures property (Flow.Productive.result (Flow.validate check parsed))
validate check property sound (Flow.productive (Flow.ordinary (F.success value position)) progress) with check value in selected
... | inj₁ error = tt
... | inj₂ output = sound value output selected
validate check property sound (Flow.productive (Flow.ordinary (F.failure error)) progress) = tt
validate check property sound (Flow.productive (Flow.panicked position) progress) = tt

extract : ∀ {Value input} (property : Value → Set) (result : Flow.Result Value input) value position →
  Ensures property result → result ≡ Flow.ordinary (F.success value position) → property value
extract property result value position holds refl = holds
