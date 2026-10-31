{-# OPTIONS --safe #-}
-- Bounded newline-delimited MCP frames. The buffer contains bytes, not decoded
-- characters. JSON/UTF-8 validation happens only after a complete frame.
module Mimir.Framing where

open import Data.Fin using (Fin; toℕ)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; length; reverse)
open import Data.List.Properties using (length-reverse)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _<?_; _≟_; z≤n)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

Byte = Fin 256

module Stream (limit : ℕ) where
  record Buffer : Set where
    constructor buffer
    field
      reversed : List Byte
      bounded : length reversed ≤ limit
  open Buffer

  empty : Buffer
  empty = buffer [] z≤n

  record Frame : Set where
    constructor frame
    field bytes : List Byte; bounded : length bytes ≤ limit

  finish : Buffer → Frame
  finish (buffer bytes bounded) = frame (reverse bytes)
    (subst (_≤ limit) (Relation.Binary.PropositionalEquality.sym (length-reverse bytes)) bounded)

  data Failure : Set where oversized streamEnded readFailure deadline : Failure

  data State : Set where
    receiving : Buffer → State
    failed : Failure → State

  data Event : Set where byte : Byte → Event; eof error timeout : Event

  data Emission : Set where none : Emission; complete : Frame → Emission

  record Step : Set where
    constructor next
    field state : State; output : Emission

  feed : State → Event → Step
  feed (failed why) event = next (failed why) none
  feed (receiving b) eof = next (failed streamEnded) none
  feed (receiving b) error = next (failed readFailure) none
  feed (receiving b) timeout = next (failed deadline) none
  feed (receiving b) (byte x) with toℕ x ≟ 10
  ... | yes _ = next (receiving empty) (complete (finish b))
  ... | no _ with length (reversed b) <? limit
  ...   | yes fits = next (receiving (buffer (x ∷ reversed b) fits)) none
  ...   | no _ = next (failed oversized) none

  noOversizedFrame : ∀ before input emitted →
    Step.output (feed before input) ≡ complete emitted → length (Frame.bytes emitted) ≤ limit
  noOversizedFrame before input emitted proof = Frame.bounded emitted

  noPartialFrameAtEOF : ∀ b → Step.output (feed (receiving b) eof) ≡ none
  noPartialFrameAtEOF b = refl

  noPartialFrameOnTimeout : ∀ b → Step.output (feed (receiving b) timeout) ≡ none
  noPartialFrameOnTimeout b = refl

  failedAbsorbs : ∀ failure input → feed (failed failure) input ≡ next (failed failure) none
  failedAbsorbs failure input = refl

  emittedExactBytes : ∀ b x → toℕ x ≡ 10 →
    Step.output (feed (receiving b) (byte x)) ≡ complete (finish b)
  emittedExactBytes b x isNewline with toℕ x ≟ 10
  ... | yes _ = refl
  ... | no notNewline = Data.Empty.⊥-elim (notNewline isNewline)
