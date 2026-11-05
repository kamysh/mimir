{-# OPTIONS --safe #-}
-- Distinguish an ordinary JSON error from a native arithmetic panic. Ordinary
-- errors retain their origin through finalization; panics unwind past it.
module Mimir.JsonFlow where

open import Data.List using (List; []; _++_; length)
open import Data.List.Properties using (length-++-≤ʳ; length-++-≤ˡ; length-++)
open import Data.Nat using (_≤_; _<_; suc)
open import Data.Nat.Properties using (+-monoˡ-≤; ≤-trans)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Mimir.Bits using (Byte)
import Mimir.JsonControls as Controls
import Mimir.FinalizingCursor as Final

module F = Final.Over Byte Controls.Code

data Result (Value : Set) (input : List Byte) : Set where
  ordinary : F.Result Value input → Result Value input
  panicked : F.Cursor input → Result Value input

current : ∀ {Value input} → Result Value input → F.Cursor input
current (ordinary result) = F.current result
current (panicked position) = position

lift : ∀ {Value input} → Controls.C.Result Value input → Result Value input
lift result = ordinary (F.lift result)

done : ∀ {Value} → Value → ∀ input → Result Value input
done value input = ordinary (F.success value (F.initial input))

fail : ∀ {Value} → Controls.Code → ∀ input → Result Value input
fail code input = lift (Controls.C.fail code input)

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

finalize : ∀ {Value input} → Result Value input → (∀ rest → Controls.C.Result ⊤ rest) → Result Value input
finalize (panicked position) finish = panicked position
finalize (ordinary result) finish = ordinary (F.finalize result (λ rest → F.lift (finish rest)))

Progress : ∀ {Value input} → Result Value input → Set
Progress (panicked position) = ⊤
Progress (ordinary (F.failure error)) = ⊤
Progress (ordinary (F.success value position)) = 1 ≤ length (F.Cursor.consumed position)

record Productive (Value : Set) (input : List Byte) : Set where
  constructor productive
  field result : Result Value input; progress : Progress result

Parser : Set → Set
Parser Value = ∀ input → Productive Value input

remainingBound : ∀ {input} (position : F.Cursor input) → length (F.Cursor.remaining position) ≤ length input
remainingBound (F.cursor consumed remaining refl) = length-++-≤ʳ remaining {xs = consumed}

positiveRemaining : ∀ {input} (position : F.Cursor input) →
  1 ≤ length (F.Cursor.consumed position) → length (F.Cursor.remaining position) < length input
positiveRemaining (F.cursor consumed remaining refl) progress =
  subst (suc (length remaining) ≤_) (sym (length-++ consumed)) (+-monoˡ-≤ (length remaining) progress)

prefixProgress : ∀ {Value input} (before : F.Cursor input) → 1 ≤ length (F.Cursor.consumed before) →
  (after : Result Value (F.Cursor.remaining before)) → Progress (prefix before after)
prefixProgress before positive (panicked after) = tt
prefixProgress before positive (ordinary (F.failure error)) = tt
prefixProgress (F.cursor consumed remaining exact) positive (ordinary (F.success value after)) =
  ≤-trans positive (length-++-≤ˡ consumed {ys = F.Cursor.consumed after})

preserveProgress : ∀ {Value input} (before : F.Cursor input) → (after : Result Value (F.Cursor.remaining before)) →
  Progress after → Progress (prefix before after)
preserveProgress before (panicked after) progress = tt
preserveProgress before (ordinary (F.failure error)) progress = tt
preserveProgress before (ordinary (F.success value after)) progress =
  ≤-trans progress (length-++-≤ʳ (F.Cursor.consumed after) {xs = F.Cursor.consumed before})

mapProgress : ∀ {First Second input} (change : First → Second) (result : Result First input) →
  Progress result → Progress (map change result)
mapProgress change (panicked position) progress = tt
mapProgress change (ordinary (F.failure error)) progress = tt
mapProgress change (ordinary (F.success value position)) progress = progress

mapProductive : ∀ {First Second input} → (First → Second) → Productive First input → Productive Second input
mapProductive change (productive result progress) = productive (map change result) (mapProgress change result progress)

bindProgress : ∀ {First Second input} (first : Result First input) → Progress first →
  (next : First → ∀ rest → Result Second rest) → Progress (andThen first next)
bindProgress (panicked position) progress next = tt
bindProgress (ordinary (F.failure error)) progress next = tt
bindProgress (ordinary (F.success value before)) progress next = prefixProgress before progress (next value (F.Cursor.remaining before))

bindProductive : ∀ {First Second input} → Productive First input →
  (First → ∀ rest → Result Second rest) → Productive Second input
bindProductive (productive result progress) next = productive (andThen result next) (bindProgress result progress next)
