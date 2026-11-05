{-# OPTIONS --safe #-}
-- LF framing as an open state machine. Any number of bytes can precede LF;
-- EOF without LF is an error, and diagnostic capture remains bounded elsewhere.
module Mimir.McpClientLine where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as All
open import Data.Fin using (toℕ)
open import Data.Nat using (_≟_)
open import Data.Product using (Σ; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Bits using (Byte)
import Mimir.Effects as Effects
import Mimir.ReadLine as Lines

data ByteReply : Set where
  byteRead : Byte → ByteReply
  ioEnded : ByteReply

data Effect : Set where
  readByte settleStderr snapshotStderr : Effect

Reply : Effect → Set
Reply readByte = ByteReply
Reply settleStderr = ⊤
Reply snapshotStderr = List Byte
module E = Effects.Protocol Effect Reply

data Failure : Set where streamEnded : List Byte → Failure

module Framing where
  record Buffer : Set where
    constructor buffer
    field bytes : List Byte; noLF : All Lines.NotLF bytes

  advance : Buffer → ∀ byte → Lines.NotLF byte → Buffer
  advance previous byte ordinary = buffer (Buffer.bytes previous ++ (byte ∷ []))
    (All.++⁺ (Buffer.noLF previous) (ordinary ∷ []))

  data Outcome : Set where
    failed : Failure → Outcome
    complete : Buffer → Outcome

  data State : Set where
    reading : Buffer → State
    settling diagnostic : State
    finished : Outcome → State

  data Step : Set where
    external : (effect : Effect) → (Reply effect → State) → Step
    stopped : Outcome → Step

  afterByte : Buffer → ByteReply → State
  afterByte accumulated ioEnded = settling
  afterByte accumulated (byteRead byte) with toℕ byte ≟ 10
  ... | yes lf = finished (complete accumulated)
  ... | no ordinary = reading (advance accumulated byte ordinary)

  next : State → Step
  next (reading accumulated) = external readByte (afterByte accumulated)
  next settling = external settleStderr (λ _ → diagnostic)
  next diagnostic = external snapshotStderr (λ bytes → finished (failed (streamEnded bytes)))
  next (finished outcome) = stopped outcome

  data Runs : State → List E.Event → Outcome → Set where
    returned : ∀ outcome → Runs (finished outcome) [] outcome
    replied : ∀ {state effect continuation events outcome} → next state ≡ external effect continuation →
      (reply : Reply effect) → Runs (continuation reply) events outcome →
      Runs state ((effect , reply) ∷ events) outcome

  start : State
  start = reading (buffer [] [])

  ordinaryByteContinues : ∀ accumulated byte → Lines.NotLF byte →
    Σ Buffer (λ next → afterByte accumulated (byteRead byte) ≡ reading next)
  ordinaryByteContinues accumulated byte ordinary with toℕ byte ≟ 10
  ... | yes lf = Data.Empty.⊥-elim (ordinary lf)
    where import Data.Empty
  ... | no notLF = advance accumulated byte notLF , refl
