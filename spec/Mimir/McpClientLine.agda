{-# OPTIONS --safe #-}
-- LF framing as an open state machine. Any number of bytes can precede LF;
-- EOF without LF ends the protocol. Owned cleanup and joining the stderr
-- reader, rather than elapsed time, establish when diagnostics are available.
module Mimir.McpClientLine where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as All
open import Data.Fin using (toℕ)
open import Data.Nat using (_≟_)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Unit using (⊤; tt)
open import Mimir.Text using (Text)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Bits using (Byte)
import Mimir.Effects as Effects
import Mimir.ReadLine as Lines

data ByteReply : Set where
  byteRead : Byte → ByteReply
  ioEnded : ByteReply

record Capture : Set where
  constructor capture
  field bytes : List Byte; issues : List Text

data Effect : Set where
  readByte stopAndReapChild joinStderr : Effect

Reply : Effect → Set
Reply readByte = ByteReply
Reply stopAndReapChild = List Text
Reply joinStderr = Capture
module E = Effects.Protocol Effect Reply

data Failure : Set where streamEnded : Capture → Failure

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
    settling : State
    diagnostic : List Text → State
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
  next settling = external stopAndReapChild diagnostic
  next (diagnostic cleanup) = external joinStderr (λ captured →
    finished (failed (streamEnded (capture (Capture.bytes captured) (cleanup ++ Capture.issues captured)))))
  next (finished outcome) = stopped outcome

  data Runs : State → List E.Event → Outcome → Set where
    returned : ∀ outcome → Runs (finished outcome) [] outcome
    replied : ∀ {state effect continuation events outcome} → next state ≡ external effect continuation →
      (reply : Reply effect) → Runs (continuation reply) events outcome →
      Runs state ((effect , reply) ∷ events) outcome

  start : State
  start = reading (buffer [] [])

  joinedDiagnosticIsComplete : ∀ cleanup captured final →
    Runs (diagnostic cleanup) ((joinStderr , captured) ∷ []) (failed (streamEnded final)) →
    Capture.bytes final ≡ Capture.bytes captured ×
    Capture.issues final ≡ cleanup ++ Capture.issues captured
  joinedDiagnosticIsComplete cleanup captured final (replied refl .captured (returned ._)) = refl , refl

  ordinaryByteContinues : ∀ accumulated byte → Lines.NotLF byte →
    Σ Buffer (λ next → afterByte accumulated (byteRead byte) ≡ reading next)
  ordinaryByteContinues accumulated byte ordinary with toℕ byte ≟ 10
  ... | yes lf = Data.Empty.⊥-elim (ordinary lf)
    where import Data.Empty
  ... | no notLF = advance accumulated byte notLF , refl
