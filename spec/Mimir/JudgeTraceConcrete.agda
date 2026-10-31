{-# OPTIONS --safe #-}
-- Execute trace-event serialization with the concrete compact JSON codec.
-- Every serialization receipt names its exact input and emitted bytes.
module Mimir.JudgeTraceConcrete where

open import Data.List using (List; []; _∷_; _++_; length)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Nat using (ℕ; _≤_; _<_; _<?_; _≤?_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; trans)
open import Mimir.Bits using (Byte)
import Mimir.SignedMachine as Machine
import Mimir.UUIDGroups as UUID
import Mimir.JudgeTraceEvent as Trace
import Mimir.JudgeStateText as Text
import Mimir.JudgeStateSerialize as Serialize
import Mimir.JsonCompactRecords as Compact
import Mimir.JudgeStateWire as Wire

module Limits (maximum eventLimit byteLimit : ℕ) (checks : Machine.OverflowChecks) where
  module E = Trace.Over UUID.UUID maximum eventLimit byteLimit checks
  module R = E.R

  candidateText : ∀ event before → Text.EventText event → Text.TraceText before → Text.TraceText (E.candidate event before)
  candidateText event before eventValid beforeValid = record
    { status = Text.TraceText.status beforeValid ; reason = Text.TraceText.reason beforeValid
    ; events = ++⁺ (Text.TraceText.events beforeValid) (eventValid All.∷ All.[]) }

  abstract
    candidateBytes : ∀ event before → Text.EventText event → Text.TraceText before → List Byte
    candidateBytes event before eventValid beforeValid = Serialize.traceBytes (E.candidate event before)
      (candidateText event before eventValid beforeValid)

    candidateExact : ∀ event before eventValid beforeValid → candidateBytes event before eventValid beforeValid ≡
      Serialize.traceBytes (E.candidate event before) (candidateText event before eventValid beforeValid)
    candidateExact event before eventValid beforeValid = refl

    candidateSize : ∀ event before eventValid beforeValid → length (candidateBytes event before eventValid beforeValid) ≡
      Compact.count (Wire.trace (E.candidate event before))
        (Serialize.trace (E.candidate event before) (candidateText event before eventValid beforeValid))
    candidateSize event before eventValid beforeValid = Serialize.traceSizeExact (E.candidate event before)
      (candidateText event before eventValid beforeValid)

  ExactReceipt : E.Event → Set
  ExactReceipt (E.serialize value , inj₁ problem) = ⊥
  ExactReceipt (E.serialize value , inj₂ bytes) = Σ (Text.TraceText value) (λ valid → bytes ≡ Serialize.traceBytes value valid)

  record Evaluation (event : R.Event) (before : R.Trace) : Set where
    constructor evaluation
    field
      result : E.Result event before
      events : List E.Event
      run : E.Runs (E.append event before) events result
      receipts : All.All ExactReceipt events

  fullScript : ∀ event before (full : ¬ (length (R.Trace.events before) < eventLimit)) →
    (length (R.Trace.events before) <? eventLimit) ≡ no full → E.append event before ≡ E.done (E.omit event before)
  fullScript event before full observed rewrite observed = refl

  roomScript : ∀ event before (room : length (R.Trace.events before) < eventLimit) →
    (length (R.Trace.events before) <? eventLimit) ≡ yes room → E.append event before ≡
      E.ask (E.serialize (E.candidate event before)) (λ reply → E.done (E.received event before room reply))
  roomScript event before room observed rewrite observed = refl

  outcomeFrom : ∀ event before → Text.EventText event → Text.TraceText before →
    Dec (length (R.Trace.events before) < eventLimit) → E.Result event before
  outcomeFrom event before eventValid beforeValid (no full) = E.omit event before
  outcomeFrom event before eventValid beforeValid (yes room) =
    E.received event before room (inj₂ (candidateBytes event before eventValid beforeValid))

  evaluateFrom : ∀ event before → Text.EventText event → Text.TraceText before →
    (choice : Dec (length (R.Trace.events before) < eventLimit)) →
    (length (R.Trace.events before) <? eventLimit) ≡ choice → Evaluation event before
  evaluateFrom event before eventValid beforeValid (no full) observed = evaluation (E.omit event before) []
    (subst (λ program → E.Runs program [] (E.omit event before)) (sym (fullScript event before full observed))
      (E.returned (E.omit event before))) All.[]
  evaluateFrom event before eventValid beforeValid (yes room) observed = evaluation
    (E.received event before room (inj₂ (candidateBytes event before eventValid beforeValid)))
    ((E.serialize (E.candidate event before) , inj₂ (candidateBytes event before eventValid beforeValid)) ∷ [])
    (subst (λ program → E.Runs program
        ((E.serialize (E.candidate event before) , inj₂ (candidateBytes event before eventValid beforeValid)) ∷ [])
        (E.received event before room (inj₂ (candidateBytes event before eventValid beforeValid))))
      (sym (roomScript event before room observed))
      (E.replied (E.serialize (E.candidate event before))
      (λ reply → E.done (E.received event before room reply))
      (inj₂ (candidateBytes event before eventValid beforeValid))
      (E.returned (E.received event before room (inj₂ (candidateBytes event before eventValid beforeValid))))))
    ((candidateText event before eventValid beforeValid , candidateExact event before eventValid beforeValid) All.∷ All.[])

  evaluate : ∀ event before → Text.EventText event → Text.TraceText before → Evaluation event before
  evaluate event before eventValid beforeValid = evaluateFrom event before eventValid beforeValid
    (length (R.Trace.events before) <? eventLimit) refl

  resultFrom : ∀ event before eventValid beforeValid choice observed →
    Evaluation.result (evaluateFrom event before eventValid beforeValid choice observed) ≡
      outcomeFrom event before eventValid beforeValid choice
  resultFrom event before eventValid beforeValid (no full) observed = refl
  resultFrom event before eventValid beforeValid (yes room) observed = refl

  resultExact : ∀ event before eventValid beforeValid → Evaluation.result (evaluate event before eventValid beforeValid) ≡
    outcomeFrom event before eventValid beforeValid (length (R.Trace.events before) <? eventLimit)
  resultExact event before eventValid beforeValid = resultFrom event before eventValid beforeValid _ refl

  serializationBound : ∀ event before eventValid beforeValid →
    E.Cost.count (Evaluation.events (evaluate event before eventValid beforeValid)) ≤ 1
  serializationBound event before eventValid beforeValid = E.atMostOneSerialization event before _ _
    (Evaluation.run (evaluate event before eventValid beforeValid))

  fitsOutcome : ∀ event before eventValid beforeValid → length (R.Trace.events before) < eventLimit →
    length (candidateBytes event before eventValid beforeValid) ≤ byteLimit →
    Σ (E.Change event before (E.candidate event before)) (λ change →
      outcomeFrom event before eventValid beforeValid (length (R.Trace.events before) <? eventLimit) ≡ E.ready (E.candidate event before) change)
  fitsOutcome event before eventValid beforeValid room fits with length (R.Trace.events before) <? eventLimit
  ... | no impossible = ⊥-elim (impossible room)
  ... | yes actualRoom with length (candidateBytes event before eventValid beforeValid) ≤? byteLimit
  ...   | no impossible = ⊥-elim (impossible fits)
  ...   | yes actualFits = E.kept actualRoom (candidateBytes event before eventValid beforeValid) actualFits , refl

  fitsKept : ∀ event before eventValid beforeValid → length (R.Trace.events before) < eventLimit →
    length (candidateBytes event before eventValid beforeValid) ≤ byteLimit →
    Σ (E.Change event before (E.candidate event before)) (λ change →
      Evaluation.result (evaluate event before eventValid beforeValid) ≡ E.ready (E.candidate event before) change)
  fitsKept event before eventValid beforeValid room fits with fitsOutcome event before eventValid beforeValid room fits
  ... | change , observed = change , trans (resultExact event before eventValid beforeValid) observed

  changedText : ∀ {event before after} → Text.EventText event → Text.TraceText before →
    E.Change event before after → Text.TraceText after
  changedText {event} {before} eventValid beforeValid (E.kept room bytes fits) = candidateText event before eventValid beforeValid
  changedText eventValid beforeValid (E.dropped count observed) = record
    { status = Text.TraceText.status beforeValid ; reason = Text.TraceText.reason beforeValid
    ; events = Text.TraceText.events beforeValid }
