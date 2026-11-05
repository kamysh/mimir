{-# OPTIONS --safe #-}
-- Typed serde visitors add validation errors to JSON syntax failures. Keep
-- their origins and cleanup cursors distinct; arithmetic panics bypass cleanup.
module Mimir.SerdeFlow where

open import Data.List using (List; []; _++_; length)
open import Data.List.Properties using (length-++-≤ˡ; length-++-≤ʳ; length-++)
open import Data.Nat using (suc; _≤_; _<_)
open import Data.Nat.Properties using (≤-trans; +-monoˡ-≤)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Mimir.Bits using (Byte)
import Mimir.Validation as V
import Mimir.JsonControls as Controls
import Mimir.JsonFlow as JSON
import Mimir.FinalizingCursor as Final

data Code : Set where
  syntaxFault : Controls.Code → Code
  visitor : V.Fault → Code

module F = Final.Over Byte Code

data Result (Value : Set) (input : List Byte) : Set where
  ordinary : F.Result Value input → Result Value input
  panicked : F.Cursor input → Result Value input

current : ∀ {Value input} → Result Value input → F.Cursor input
current (ordinary result) = F.current result
current (panicked position) = position

copyCursor : ∀ {input} → JSON.F.Cursor input → F.Cursor input
copyCursor (JSON.F.cursor consumed remaining exact) = F.cursor consumed remaining exact

fromJson : ∀ {Value input} → JSON.Result Value input → Result Value input
fromJson (JSON.panicked position) = panicked (copyCursor position)
fromJson (JSON.ordinary (JSON.F.success value position)) = ordinary (F.success value (copyCursor position))
fromJson (JSON.ordinary (JSON.F.failure
  (JSON.F.rejected (JSON.F.fault code (JSON.F.cursor consumed remaining exact)) cleanup))) =
  ordinary (F.failure (F.rejected (F.fault (syntaxFault code) (F.cursor consumed remaining exact)) (copyCursor cleanup)))

lift : ∀ {Value input} → Controls.C.Result Value input → Result Value input
lift result = fromJson (JSON.lift result)

done : ∀ {Value} → Value → ∀ input → Result Value input
done value input = ordinary (F.success value (F.initial input))

reject : ∀ {Value} → V.Fault → ∀ input → Result Value input
reject fault input = ordinary (F.lift (F.C.fail (visitor fault) input))

prefix : ∀ {Value input} (before : F.Cursor input) → Result Value (F.Cursor.remaining before) → Result Value input
prefix before (panicked after) = panicked (F.append before after)
prefix before (ordinary (F.success value after)) = ordinary (F.success value (F.append before after))
prefix before (ordinary (F.failure error)) = ordinary (F.failure (F.prefixRejected before error))

map : ∀ {First Second input} → (First → Second) → Result First input → Result Second input
map change (panicked position) = panicked position
map change (ordinary (F.failure error)) = ordinary (F.failure error)
map change (ordinary (F.success value position)) = ordinary (F.success (change value) position)

andThen : ∀ {First Second input} → Result First input →
  (First → ∀ rest → Result Second rest) → Result Second input
andThen (panicked position) next = panicked position
andThen (ordinary (F.failure error)) next = ordinary (F.failure error)
andThen (ordinary (F.success value before)) next = prefix before (next value (F.Cursor.remaining before))

finishSyntax : ∀ input → Controls.C.Result ⊤ input → F.Result ⊤ input
finishSyntax input (Controls.C.success tt consumed remaining exact) = F.lift (F.C.success tt consumed remaining exact)
finishSyntax input (Controls.C.failure code consumed remaining exact) = F.lift (F.C.failure (syntaxFault code) consumed remaining exact)

finalize : ∀ {Value input} → Result Value input → (∀ rest → Controls.C.Result ⊤ rest) → Result Value input
finalize (panicked position) finish = panicked position
finalize (ordinary result) finish = ordinary (F.finalize result (λ rest → finishSyntax rest (finish rest)))

Progress : ∀ {Value input} → Result Value input → Set
Progress (panicked position) = ⊤
Progress (ordinary (F.failure error)) = ⊤
Progress (ordinary (F.success value position)) = 1 ≤ length (F.Cursor.consumed position)

record Productive (Value : Set) (input : List Byte) : Set where
  constructor productive
  field result : Result Value input; progress : Progress result

Parser : Set → Set
Parser Value = ∀ input → Productive Value input

fromJsonProgress : ∀ {Value input} (result : JSON.Result Value input) → JSON.Progress result → Progress (fromJson result)
fromJsonProgress (JSON.panicked position) progress = tt
fromJsonProgress (JSON.ordinary (JSON.F.success value (JSON.F.cursor consumed remaining exact))) progress = progress
fromJsonProgress (JSON.ordinary (JSON.F.failure
  (JSON.F.rejected (JSON.F.fault code (JSON.F.cursor consumed remaining exact)) cleanup))) progress = tt

fromJsonProductive : ∀ {Value input} → JSON.Productive Value input → Productive Value input
fromJsonProductive (JSON.productive result progress) = productive (fromJson result) (fromJsonProgress result progress)

prefixProgress : ∀ {Value input} (before : F.Cursor input) → 1 ≤ length (F.Cursor.consumed before) →
  (after : Result Value (F.Cursor.remaining before)) → Progress (prefix before after)
prefixProgress before positive (panicked position) = tt
prefixProgress before positive (ordinary (F.failure error)) = tt
prefixProgress (F.cursor consumed remaining exact) positive (ordinary (F.success value after)) = ≤-trans positive (length-++-≤ˡ consumed {ys = F.Cursor.consumed after})

preserveProgress : ∀ {Value input} (before : F.Cursor input) → (after : Result Value (F.Cursor.remaining before)) →
  Progress after → Progress (prefix before after)
preserveProgress before (panicked position) positive = tt
preserveProgress before (ordinary (F.failure error)) positive = tt
preserveProgress (F.cursor consumed remaining exact) (ordinary (F.success value after)) positive = ≤-trans positive (length-++-≤ʳ (F.Cursor.consumed after) {xs = consumed})

mapProgress : ∀ {First Second input} (change : First → Second) (result : Result First input) →
  Progress result → Progress (map change result)
mapProgress change (panicked position) progress = tt
mapProgress change (ordinary (F.failure error)) progress = tt
mapProgress change (ordinary (F.success value position)) progress = progress

bindProgress : ∀ {First Second input} (first : Result First input) → Progress first →
  (next : First → ∀ rest → Result Second rest) → Progress (andThen first next)
bindProgress (panicked position) progress next = tt
bindProgress (ordinary (F.failure error)) progress next = tt
bindProgress (ordinary (F.success value position)) progress next = prefixProgress position progress (next value (F.Cursor.remaining position))

mapProductive : ∀ {First Second input} → (First → Second) → Productive First input → Productive Second input
mapProductive change (productive result progress) = productive (map change result) (mapProgress change result progress)

bindProductive : ∀ {First Second input} → Productive First input →
  (First → ∀ rest → Result Second rest) → Productive Second input
bindProductive (productive result progress) next = productive (andThen result next) (bindProgress result progress next)

validate : ∀ {First Second input} → (First → V.Fault ⊎ Second) → Productive First input → Productive Second input
validate check parsed = bindProductive parsed (λ value rest → convert (check value) rest)
  where
  convert : ∀ {Value} → V.Fault ⊎ Value → ∀ input → Result Value input
  convert (inj₁ fault) input = reject fault input
  convert (inj₂ value) input = done value input

remainingBound : ∀ {input} (position : F.Cursor input) → length (F.Cursor.remaining position) ≤ length input
remainingBound (F.cursor consumed remaining refl) = length-++-≤ʳ remaining {xs = consumed}

positiveRemaining : ∀ {input} (position : F.Cursor input) →
  1 ≤ length (F.Cursor.consumed position) → length (F.Cursor.remaining position) < length input
positiveRemaining (F.cursor consumed remaining refl) positive = subst (suc (length remaining) ≤_) (sym (length-++ consumed)) (+-monoˡ-≤ (length remaining) positive)

firstError : ∀ {Value input} → Result Value input → Maybe (F.Fault input)
firstError (panicked position) = nothing
firstError (ordinary result) = F.firstError result

cleanupPreservesError : ∀ {Value input} (error : F.Rejected input) finish →
  firstError (finalize {Value} (ordinary (F.failure error)) finish) ≡ just (F.Rejected.firstError error)
cleanupPreservesError {Value} error finish =
  F.preservesFirstError {Value = Value} error (λ rest → finishSyntax rest (finish rest))

panicBypassesCleanup : ∀ {Value input} (position : F.Cursor input) finish →
  finalize {Value} (panicked position) finish ≡ panicked position
panicBypassesCleanup position finish = refl
