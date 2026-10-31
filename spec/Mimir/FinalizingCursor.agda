{-# OPTIONS --safe #-}
-- A parser may consume more input during cleanup after recording an error.
-- Keep the first error location separate from the final cursor, and preserve
-- first-error precedence when cleanup itself also fails.
module Mimir.FinalizingCursor where

open import Data.List using (List; []; _++_; length)
open import Data.List.Properties using (++-assoc; ++-identityʳ; length-++-≤ˡ)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (_≤_)
open import Data.Product using (_×_; _,_)
import Data.Unit
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
import Mimir.SequenceCursor as Atomic

module Over (Atom Code : Set) where
  module C = Atomic.Over Atom Code

  record Cursor (input : List Atom) : Set where
    constructor cursor
    field consumed remaining : List Atom; exact : input ≡ consumed ++ remaining

  initial : ∀ input → Cursor input
  initial input = cursor [] input refl

  append : ∀ {input} (first : Cursor input) → Cursor (Cursor.remaining first) → Cursor input
  append (cursor before rest exact) (cursor later suffix restExact) = cursor (before ++ later) suffix
    (trans exact (trans (cong (before ++_) restExact) (sym (++-assoc before later suffix))))

  record Fault (input : List Atom) : Set where
    constructor fault
    field code : Code; origin : Cursor input

  record Rejected (input : List Atom) : Set where
    constructor rejected
    field firstError : Fault input; cleanup : Cursor (Cursor.remaining (Fault.origin firstError))

  finalCursor : ∀ {input} → Rejected input → Cursor input
  finalCursor (rejected firstError cleanup) = append (Fault.origin firstError) cleanup

  errorOffsetBeforeFinal : ∀ {input} (failure : Rejected input) →
    length (Cursor.consumed (Fault.origin (Rejected.firstError failure))) ≤ length (Cursor.consumed (finalCursor failure))
  errorOffsetBeforeFinal (rejected (fault code (cursor before rest exact)) (cursor later suffix restExact)) = length-++-≤ˡ before

  data Result (Value : Set) (input : List Atom) : Set where
    success : Value → Cursor input → Result Value input
    failure : Rejected input → Result Value input

  current : ∀ {Value input} → Result Value input → Cursor input
  current (success value position) = position
  current (failure rejection) = finalCursor rejection

  firstError : ∀ {Value input} → Result Value input → Maybe (Fault input)
  firstError (success value position) = nothing
  firstError (failure rejection) = just (Rejected.firstError rejection)

  lift : ∀ {Value input} → C.Result Value input → Result Value input
  lift (C.success value consumed remaining exact) = success value (cursor consumed remaining exact)
  lift (C.failure code consumed remaining exact) = failure
    (rejected (fault code (cursor consumed remaining exact)) (initial remaining))

  prefixFault : ∀ {input} (before : Cursor input) → Fault (Cursor.remaining before) → Fault input
  prefixFault before (fault code origin) = fault code (append before origin)

  prefixRejected : ∀ {input} (before : Cursor input) → Rejected (Cursor.remaining before) → Rejected input
  prefixRejected before (rejected error cleanup) = rejected (prefixFault before error) cleanup

  extendRejected : ∀ {input} (error : Rejected input) → Cursor (Cursor.remaining (finalCursor error)) → Rejected input
  extendRejected (rejected error cleanup) later = rejected error (append cleanup later)

  -- Run cleanup regardless of the first result. Its error matters only when
  -- the original operation succeeded.
  finalize : ∀ {Value input} (result : Result Value input) →
    (∀ rest → Result Data.Unit.⊤ rest) → Result Value input
  finalize (success value before) finish with finish (Cursor.remaining before)
  ... | success unit later = success value (append before later)
  ... | failure error = failure (prefixRejected before error)
  finalize (failure error) finish = failure
    (extendRejected error (current (finish (Cursor.remaining (finalCursor error)))))

  preservesFirstError : ∀ {Value input} (error : Rejected input) finish →
    firstError (finalize {Value} (failure error) finish) ≡ just (Rejected.firstError error)
  preservesFirstError error finish = refl

  andThen : ∀ {First Second input} → Result First input →
    (First → ∀ rest → Result Second rest) → Result Second input
  andThen (failure error) next = failure error
  andThen (success value before) next with next value (Cursor.remaining before)
  ... | success nextValue later = success nextValue (append before later)
  ... | failure error = failure (prefixRejected before error)
