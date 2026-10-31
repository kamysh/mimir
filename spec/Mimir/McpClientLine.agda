{-# OPTIONS --safe #-}
-- Byte-level client framing. LF ends the line before the capacity check;
-- EOF, timeout and a final unterminated fragment are not successful lines.
-- Clock samples and timed I/O receipts remain explicit environment inputs.
module Mimir.McpClientLine where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as All
open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; _≟_; _<?_; z≤n)
open import Data.Nat.Properties using (≤-refl; +-suc; +-identityʳ; ≤-trans; 1+n≰n)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_; _×_)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym)
open import Mimir.Bits using (Byte)
import Mimir.Effects as Effects
import Mimir.ReadLine as Lines

data ByteReply : Set where
  byteRead : Byte → ByteReply
  timedOut ioEnded : ByteReply

data Effect : Set where
  clockNow : Effect
  timedRead : ℕ → Effect
  settleStderr snapshotStderr : Effect

Reply : Effect → Set
Reply clockNow = ℕ
Reply (timedRead duration) = ByteReply
Reply settleStderr = ⊤
Reply snapshotStderr = List Byte

module E = Effects.Protocol Effect Reply

readCost : Effect → ℕ
readCost (timedRead duration) = 1
readCost _ = 0
module Reads = E.Counting readCost

data Failure : Set where
  deadlineExceeded readTimeout tooLarge : Failure
  streamEnded : List Byte → Failure

module Framing (limit deadline : ℕ) where
  record Buffer (remaining : ℕ) : Set where
    constructor buffer
    field
      bytes : List Byte
      capacity : length bytes + remaining ≡ limit
      noLF : All Lines.NotLF bytes

  appendRoom : ∀ (prefix : List Byte) byte remaining →
    length (prefix ++ (byte ∷ [])) + remaining ≡ length prefix + suc remaining
  appendRoom prefix byte remaining rewrite length-++ prefix {ys = byte ∷ []} |
    +-suc (length prefix) 0 | +-identityʳ (length prefix) = sym (+-suc (length prefix) remaining)

  advance : ∀ remaining → Buffer (suc remaining) → ∀ byte → Lines.NotLF byte → Buffer remaining
  advance remaining previous byte ordinary = buffer (Buffer.bytes previous ++ (byte ∷ []))
    (trans (appendRoom (Buffer.bytes previous) byte remaining) (Buffer.capacity previous))
    (All.++⁺ (Buffer.noLF previous) (ordinary ∷ []))

  data Outcome : Set where
    failed : Failure → Outcome
    complete : ∀ remaining → Buffer remaining → Outcome

  initial : Buffer limit
  initial = buffer [] refl []

  afterStderr : List Byte → E.Script Outcome
  afterStderr bytes = E.done (failed (streamEnded bytes))

  afterSettle : ⊤ → E.Script Outcome
  afterSettle tt = E.ask snapshotStderr afterStderr

  mutual
    read : ∀ remaining → Buffer remaining → E.Script Outcome
    read remaining accumulated = E.ask clockNow (afterClock remaining accumulated)

    afterClock : ∀ remaining → Buffer remaining → ℕ → E.Script Outcome
    afterClock remaining accumulated now with now <? deadline
    ... | no expired = E.done (failed deadlineExceeded)
    ... | yes available = E.ask (timedRead (deadline ∸ now)) (afterByte remaining accumulated)

    afterByte : ∀ remaining → Buffer remaining → ByteReply → E.Script Outcome
    afterByte remaining accumulated timedOut = E.done (failed readTimeout)
    afterByte remaining accumulated ioEnded = E.ask settleStderr afterSettle
    afterByte remaining accumulated (byteRead byte) with toℕ byte ≟ 10
    ... | yes lf = E.done (complete remaining accumulated)
    afterByte zero accumulated (byteRead byte) | no ordinary = E.done (failed tooLarge)
    afterByte (suc remaining) accumulated (byteRead byte) | no ordinary =
      read remaining (advance remaining accumulated byte ordinary)

  start : E.Script Outcome
  start = read limit initial

  stderrBound : ∀ bytes → Reads.Bounded 0 (afterStderr bytes)
  stderrBound bytes = Reads.done _

  settleBound : ∀ reply → Reads.Bounded 0 (afterSettle reply)
  settleBound tt = Reads.ask snapshotStderr afterStderr 0 ≤-refl stderrBound

  mutual
    readBound : ∀ remaining accumulated → Reads.Bounded (suc remaining) (read remaining accumulated)
    readBound remaining accumulated = Reads.ask clockNow _ (suc remaining) ≤-refl (clockBound remaining accumulated)

    clockBound : ∀ remaining accumulated now → Reads.Bounded (suc remaining) (afterClock remaining accumulated now)
    clockBound remaining accumulated now with now <? deadline
    ... | no expired = Reads.done _
    ... | yes available = Reads.ask (timedRead (deadline ∸ now)) _ remaining ≤-refl (byteBound remaining accumulated)

    byteBound : ∀ remaining accumulated reply → Reads.Bounded remaining (afterByte remaining accumulated reply)
    byteBound remaining accumulated timedOut = Reads.done _
    byteBound remaining accumulated ioEnded = Reads.ask settleStderr afterSettle 0 z≤n settleBound
    byteBound remaining accumulated (byteRead byte) with toℕ byte ≟ 10
    ... | yes lf = Reads.done _
    byteBound zero accumulated (byteRead byte) | no ordinary = Reads.done _
    byteBound (suc remaining) accumulated (byteRead byte) | no ordinary = readBound remaining _

  boundedReads : ∀ events outcome → E.Runs start events outcome → Reads.count events ≤ suc limit
  boundedReads events outcome execution = Reads.runBounded (readBound limit initial) execution

  boundedPrefixReads : ∀ events residual → E.Prefix start events residual → Reads.count events ≤ suc limit
  boundedPrefixReads events residual execution = Reads.prefixBounded (readBound limit initial) execution

  expiredDoesNotRead : ∀ remaining accumulated now → (deadline ≤ now) →
    afterClock remaining accumulated now ≡ E.done (failed deadlineExceeded)
  expiredDoesNotRead remaining accumulated now expired with now <? deadline
  ... | no unavailable = refl
  ... | yes available = ⊥-elim (1+n≰n (≤-trans available expired))
