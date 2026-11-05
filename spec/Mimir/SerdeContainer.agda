{-# OPTIONS --safe #-}
-- Enter a recognized typed container, preserving the first error through
-- closing-delimiter cleanup. A panic bypasses cleanup.
module Mimir.SerdeContainer where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just)
open import Data.Nat using (s≤s; z≤n)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Bits using (Byte)
import Mimir.SerdeFlow as Flow
import Mimir.JsonControls as Controls
module F = Flow.F

enter : ∀ {Value} (byte : Byte) rest → Flow.Result Value rest →
  (∀ input → Controls.C.Result ⊤ input) → Flow.Productive Value (byte ∷ rest)
enter byte rest result finish = Flow.productive (Flow.prefix before cleaned)
  (Flow.prefixProgress before (s≤s z≤n) cleaned)
  where
  before = F.cursor (byte ∷ []) rest refl
  cleaned = Flow.finalize result finish

firstErrorPreserved : ∀ {Value} byte rest (error : F.Rejected rest) finish →
  Flow.firstError (Flow.Productive.result (enter {Value} byte rest (Flow.ordinary (F.failure error)) finish)) ≡
    just (F.prefixFault (F.cursor (byte ∷ []) rest refl) (F.Rejected.firstError error))
firstErrorPreserved byte rest error finish = refl

panicBypassesCleanup : ∀ {Value} byte rest (position : F.Cursor rest) finish →
  Flow.Productive.result (enter {Value} byte rest (Flow.panicked position) finish) ≡
    Flow.panicked (F.append (F.cursor (byte ∷ []) rest refl) position)
panicBypassesCleanup byte rest position finish = refl

successfulClose : ∀ {Value} byte rest (value : Value) (before : F.Cursor rest) finish consumed remaining exact →
  finish (F.Cursor.remaining before) ≡ Controls.C.success tt consumed remaining exact →
  Flow.Productive.result (enter byte rest (Flow.ordinary (F.success value before)) finish) ≡
    Flow.ordinary (F.success value
      (F.append (F.cursor (byte ∷ []) rest refl) (F.append before (F.cursor consumed remaining exact))))
successfulClose byte rest value before finish consumed remaining exact closed rewrite closed = refl
