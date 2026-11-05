{-# OPTIONS --safe #-}
-- One trace event updates budget observations even when the event is omitted.
-- Serialization is an explicit operation carrying the complete candidate;
-- its concrete JSON encoder is a separate composition obligation.
module Mimir.JudgeTraceEvent where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++)
open import Data.Nat using (ℕ; suc; _≤_; _<_; _<?_; _≤?_; z≤n)
open import Data.Nat.Properties using (≤-refl; +-identityʳ; +-suc)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym; subst)
open import Mimir.Bits using (Byte)
open import Mimir.Text using (Text)
import Mimir.Effects as Effects
import Mimir.JudgeStateRecords as Records
import Mimir.UnsignedMachine as Unsigned
import Mimir.SignedMachine as Machine

module Over (Id : Set) (maximum eventLimit byteLimit : ℕ) (checks : Machine.OverflowChecks) where
  module R = Records.Over Id
  module U = Unsigned.Maximum maximum

  budget : R.Event → R.Trace → R.Trace
  budget event before = record before
    { modelRequests = R.Event.modelRequests event ; toolAttempts = R.Event.toolAttempts event }

  candidate : R.Event → R.Trace → R.Trace
  candidate event before = record (budget event before) { events = R.Trace.events before ++ (event ∷ []) }

  omitted : R.Event → R.Trace → U.Natural → R.Trace
  omitted event before count = record (budget event before) { eventsOmitted = U.Natural.number count }

  data Change (event : R.Event) (before : R.Trace) : R.Trace → Set where
    kept : length (R.Trace.events before) < eventLimit → (bytes : List Byte) → length bytes ≤ byteLimit →
      Change event before (candidate event before)
    dropped : ∀ count → U.execute checks (suc (R.Trace.eventsOmitted before)) ≡ U.returned count →
      Change event before (omitted event before count)

  data Result (event : R.Event) (before : R.Trace) : Set where
    ready : ∀ after → Change event before after → Result event before
    serializationFailed : Text → Result event before
    arithmeticPanic : Result event before

  data Operation : Set where serialize : R.Trace → Operation
  Reply : Operation → Set
  Reply (serialize value) = Text ⊎ List Byte
  open Effects.Protocol Operation Reply public
  module Cost = Counting (λ _ → 1)

  omit : ∀ event before → Result event before
  omit event before with U.execute checks (suc (R.Trace.eventsOmitted before)) in evaluated
  ... | U.returned count = ready (omitted event before count) (dropped count evaluated)
  ... | U.panic overflow = arithmeticPanic

  received : ∀ event before → length (R.Trace.events before) < eventLimit → Reply (serialize (candidate event before)) → Result event before
  received event before room (inj₁ problem) = serializationFailed problem
  received event before room (inj₂ bytes) with length bytes ≤? byteLimit
  ... | yes fits = ready (candidate event before) (kept room bytes fits)
  ... | no tooLarge = omit event before

  append : ∀ event before → Script (Result event before)
  append event before with length (R.Trace.events before) <? eventLimit
  ... | no full = done (omit event before)
  ... | yes room = ask (serialize (candidate event before)) (λ reply → done (received event before room reply))

  budgetPreserved : ∀ {event before after} → Change event before after →
    R.Trace.modelRequests after ≡ R.Event.modelRequests event ×
    R.Trace.toolAttempts after ≡ R.Event.toolAttempts event
  budgetPreserved (kept room bytes fits) = refl , refl
  budgetPreserved (dropped count evaluated) = refl , refl

  eventsExact : ∀ {event before after} → Change event before after →
    R.Trace.events after ≡ R.Trace.events before ⊎
    R.Trace.events after ≡ R.Trace.events before ++ (event ∷ [])
  eventsExact (kept room bytes fits) = inj₂ refl
  eventsExact (dropped count evaluated) = inj₁ refl

  metadataRetained : ∀ {event before after} → Change event before after →
    R.Trace.identity after ≡ R.Trace.identity before ×
    (R.Trace.status after ≡ R.Trace.status before × R.Trace.selectedIds after ≡ R.Trace.selectedIds before)
  metadataRetained (kept room bytes fits) = refl , refl , refl
  metadataRetained (dropped count evaluated) = refl , refl , refl

  eventBound : ∀ {event before after} → Change event before after →
    length (R.Trace.events before) ≤ eventLimit → length (R.Trace.events after) ≤ eventLimit
  eventBound {event} {before} (kept room bytes fits) bounded = subst (_≤ eventLimit)
    (sym (trans (length-++ (R.Trace.events before))
      (trans (+-suc (length (R.Trace.events before)) 0) (cong suc (+-identityʳ (length (R.Trace.events before))))))) room
  eventBound (dropped count evaluated) bounded = bounded

  appendBounded : ∀ event before → Cost.Bounded 1 (append event before)
  appendBounded event before with length (R.Trace.events before) <? eventLimit
  ... | no full = Cost.done (omit event before)
  ... | yes room = Cost.ask (serialize (candidate event before)) _ 0 ≤-refl
    (λ reply → Cost.done (received event before room reply))

  atMostOneSerialization : ∀ event before events result → Runs (append event before) events result → Cost.count events ≤ 1
  atMostOneSerialization event before events result = Cost.runBounded (appendBounded event before)

  interruptedAtMostOneSerialization : ∀ event before events residual → Prefix (append event before) events residual → Cost.count events ≤ 1
  interruptedAtMostOneSerialization event before events residual = Cost.prefixBounded (appendBounded event before)
