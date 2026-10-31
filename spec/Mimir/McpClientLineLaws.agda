{-# OPTIONS --safe #-}
-- Independent trace grammar for client framing: successful bytes are exactly
-- the observed bytes before the first LF, in order, with no skipped read.
module Mimir.McpClientLineLaws where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Relation.Unary.All using (All)
open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; _≟_; _<?_)
open import Data.Nat.Properties using (m≤m+n)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Unit using (tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst)
open import Mimir.Bits using (Byte)
open import Mimir.McpClientLine
import Mimir.ReadLine as Lines

module Laws (limit deadline : ℕ) where
  module F = Framing limit deadline
  open F

  mutual
    data Frame : List E.Event → List Byte → Set where
      frame : ∀ now reply events payload → now < deadline → Tail reply events payload →
        Frame ((clockNow , now) ∷ (timedRead (deadline ∸ now) , reply) ∷ events) payload

    data Tail : ByteReply → List E.Event → List Byte → Set where
      newline : ∀ byte → toℕ byte ≡ 10 → Tail (byteRead byte) [] []
      ordinary : ∀ byte events payload → Lines.NotLF byte → Frame events payload →
        Tail (byteRead byte) events (byte ∷ payload)

  mutual
    readSound : ∀ remaining accumulated events finalRemaining final →
      E.Runs (read remaining accumulated) events (complete finalRemaining final) →
      Σ (List Byte) (λ payload → Frame events payload × Buffer.bytes final ≡ Buffer.bytes accumulated ++ payload)
    readSound remaining accumulated .((clockNow , now) ∷ events) finalRemaining final
      (E.replied .clockNow _ now {events} execution) =
      clockSound remaining accumulated now events finalRemaining final execution

    clockSound : ∀ remaining accumulated now events finalRemaining final →
      E.Runs (afterClock remaining accumulated now) events (complete finalRemaining final) →
      Σ (List Byte) (λ payload → Frame ((clockNow , now) ∷ events) payload ×
        Buffer.bytes final ≡ Buffer.bytes accumulated ++ payload)
    clockSound remaining accumulated now events finalRemaining final execution with now <? deadline
    ... | no expired with execution
    ...   | ()
    clockSound remaining accumulated now .((timedRead (deadline ∸ now) , reply) ∷ events) finalRemaining final
      (E.replied .(timedRead (deadline ∸ now)) _ reply {events} execution) | yes available
      with byteSound remaining accumulated reply events finalRemaining final execution
    ... | payload , suffix , exact = payload , frame now reply events payload available suffix , exact

    byteSound : ∀ remaining accumulated reply events finalRemaining final →
      E.Runs (afterByte remaining accumulated reply) events (complete finalRemaining final) →
      Σ (List Byte) (λ payload → Tail reply events payload ×
        Buffer.bytes final ≡ Buffer.bytes accumulated ++ payload)
    byteSound remaining accumulated timedOut events finalRemaining final ()
    byteSound remaining accumulated ioEnded events finalRemaining final
      (E.replied .settleStderr _ tt (E.replied .snapshotStderr _ bytes ()))
    byteSound remaining accumulated (byteRead byte) events finalRemaining final execution with toℕ byte ≟ 10
    ... | yes lf with execution
    ...   | E.returned _ = [] , newline byte lf , sym (++-identityʳ (Buffer.bytes accumulated))
    byteSound zero accumulated (byteRead byte) events finalRemaining final execution | no notLF with execution
    ... | ()
    byteSound (suc remaining) accumulated (byteRead byte) events finalRemaining final execution | no notLF
      with readSound remaining (advance remaining accumulated byte notLF) events finalRemaining final execution
    ... | payload , framed , exact = (byte ∷ payload) , ordinary byte events payload notLF framed ,
      trans exact (++-assoc (Buffer.bytes accumulated) (byte ∷ []) payload)

  completeFramed : ∀ events remaining final → E.Runs start events (complete remaining final) →
    Frame events (Buffer.bytes final)
  completeFramed events remaining final execution with readSound limit initial events remaining final execution
  ... | payload , framed , exact = subst (Frame events) (sym exact) framed

  capacityBound : ∀ remaining (accumulated : Buffer remaining) → length (Buffer.bytes accumulated) ≤ limit
  capacityBound remaining accumulated = subst (length (Buffer.bytes accumulated) ≤_)
    (Buffer.capacity accumulated) (m≤m+n (length (Buffer.bytes accumulated)) remaining)

  successfulBodyContainsNoLF : ∀ remaining (accumulated : Buffer remaining) →
    All Lines.NotLF (Buffer.bytes accumulated)
  successfulBodyContainsNoLF remaining accumulated = Buffer.noLF accumulated
