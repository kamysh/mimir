{-# OPTIONS --safe #-}
-- Finish-time trace trimming removes newest events until serialized metadata
-- fits. Serialization failure, metadata-only overflow, and counter panic stop.
module Mimir.JudgeTraceTrim where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Nat using (ℕ; zero; suc; _≤_; _≤?_; z≤n)
open import Data.Product using (Σ; _,_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; trans; cong)
open import Mimir.Bits using (Byte)
open import Mimir.Text using (Text)
import Mimir.JudgeStateRecords as Records
import Mimir.JudgeTraceEvent as Event
import Mimir.UnsignedMachine as Unsigned
import Mimir.SignedMachine as Machine
import Mimir.LastElement as Last

module Over (Id : Set) (maximum eventLimit byteLimit : ℕ) (checks : Machine.OverflowChecks) where
  module R = Records.Over Id
  module U = Unsigned.Maximum maximum
  module E = Event.Over Id maximum eventLimit byteLimit checks
  module P = Last.Over R.Event
  module Cost = E.Cost
  open E using (Script; done; ask; serialize; Reply)

  shorten : (before : R.Trace) → P.Popped (R.Trace.events before) → U.Natural → R.Trace
  shorten before selection count = record before { events = P.Popped.prefix selection ; eventsOmitted = U.Natural.number count }

  data Step (before : R.Trace) : R.Trace → Set where
    removed : (selection : P.Popped (R.Trace.events before)) → ∀ count →
      U.execute checks (suc (R.Trace.eventsOmitted before)) ≡ U.returned count →
      (bytes : List Byte) → ¬ length bytes ≤ byteLimit → Step before (shorten before selection count)

  data Trimmed (before : R.Trace) : R.Trace → Set where
    unchanged : Trimmed before before
    shortened : ∀ {middle after} → Step before middle → Trimmed middle after → Trimmed before after

  data Result (before : R.Trace) : Set where
    ready : ∀ after → Trimmed before after → (bytes : List Byte) → length bytes ≤ byteLimit → Result before
    serializationFailed : Text → Result before
    metadataTooLarge arithmeticPanic : Result before

  lift : ∀ {before middle} → Step before middle → Result middle → Result before
  lift step (ready after trimmed bytes fits) = ready after (shortened step trimmed) bytes fits
  lift step (serializationFailed problem) = serializationFailed problem
  lift step metadataTooLarge = metadataTooLarge
  lift step arithmeticPanic = arithmeticPanic

  mapResult : ∀ {A B : Set} → (A → B) → Script A → Script B
  mapResult change (done value) = done (change value)
  mapResult change (ask operation next) = ask operation (λ reply → mapResult change (next reply))

  emptyCannotPop : ∀ before → P.Popped (R.Trace.events before) → length (R.Trace.events before) ≤ 0 → ⊥
  emptyCannotPop before selection bounded with subst (_≤ 0) (P.lengthExact selection) bounded
  ... | ()

  mutual
    trim : ∀ fuel before → length (R.Trace.events before) ≤ fuel → Script (Result before)
    trim fuel before bounded = ask (serialize before) (receive fuel before bounded)

    receive : ∀ fuel before → length (R.Trace.events before) ≤ fuel → Reply (serialize before) → Script (Result before)
    receive fuel before bounded (inj₁ problem) = done (serializationFailed problem)
    receive fuel before bounded (inj₂ bytes) with length bytes ≤? byteLimit
    ... | yes fits = done (ready before unchanged bytes fits)
    ... | no tooLarge = shrink fuel before bounded bytes tooLarge

    shrink : ∀ fuel before → length (R.Trace.events before) ≤ fuel →
      (bytes : List Byte) → ¬ length bytes ≤ byteLimit → Script (Result before)
    shrink fuel before bounded bytes tooLarge = shrinkView fuel before bounded bytes tooLarge (P.view (R.Trace.events before))

    shrinkView : ∀ fuel before → length (R.Trace.events before) ≤ fuel →
      (bytes : List Byte) → ¬ length bytes ≤ byteLimit → P.View (R.Trace.events before) → Script (Result before)
    shrinkView fuel before bounded bytes tooLarge (P.empty exact) = done metadataTooLarge
    shrinkView zero before bounded bytes tooLarge (P.nonempty selection) = ⊥-elim (emptyCannotPop before selection bounded)
    shrinkView (suc fuel) before bounded bytes tooLarge (P.nonempty selection) =
      shrinkEvaluated fuel before bounded bytes tooLarge selection (U.execute checks (suc (R.Trace.eventsOmitted before))) refl

    shrinkEvaluated : ∀ fuel before → length (R.Trace.events before) ≤ suc fuel →
      (bytes : List Byte) → ¬ length bytes ≤ byteLimit → (selection : P.Popped (R.Trace.events before)) →
      (evaluation : U.Evaluation (suc (R.Trace.eventsOmitted before))) →
      U.execute checks (suc (R.Trace.eventsOmitted before)) ≡ evaluation → Script (Result before)
    shrinkEvaluated fuel before bounded bytes tooLarge selection (U.panic overflow) evaluated = done arithmeticPanic
    shrinkEvaluated fuel before bounded bytes tooLarge selection (U.returned count) evaluated =
      mapResult (lift (removed selection count evaluated bytes tooLarge))
      (trim fuel (shorten before selection count) (P.decreases fuel selection bounded))

  frame : R.Trace → R.Trace
  frame before = record before { events = [] ; eventsOmitted = 0 }

  stepFrame : ∀ {before after} → Step before after → frame after ≡ frame before
  stepFrame (removed selection count evaluated bytes tooLarge) = refl

  framePreserved : ∀ {before after} → Trimmed before after → frame after ≡ frame before
  framePreserved unchanged = refl
  framePreserved (shortened step later) = trans (framePreserved later) (stepFrame step)

  prefixPreserved : ∀ {before after} → Trimmed before after →
    Σ (List R.Event) (λ suffix → R.Trace.events before ≡ R.Trace.events after ++ suffix)
  prefixPreserved {before} unchanged = [] , sym (++-identityʳ (R.Trace.events before))
  prefixPreserved (shortened (removed selection count evaluated bytes tooLarge) later) with prefixPreserved later
  ... | suffix , exact = (suffix ++ (P.Popped.last selection ∷ [])) ,
    trans (P.Popped.exact selection) (trans (cong (_++ (P.Popped.last selection ∷ [])) exact)
      (++-assoc _ suffix (P.Popped.last selection ∷ [])))

  mapBounded : ∀ {A B : Set} {budget} {program : Script A} (change : A → B) →
    Cost.Bounded budget program → Cost.Bounded budget (mapResult change program)
  mapBounded change (Cost.done value) = Cost.done (change value)
  mapBounded change (Cost.ask operation next remaining bounded children) =
    Cost.ask operation _ remaining bounded (λ reply → mapBounded change (children reply))

  mutual
    trimBounded : ∀ fuel before bounded → Cost.Bounded (suc fuel) (trim fuel before bounded)
    trimBounded fuel before bounded = Cost.ask (serialize before) _ fuel ≤-refl (receiveBounded fuel before bounded)

    receiveBounded : ∀ fuel before bounded reply → Cost.Bounded fuel (receive fuel before bounded reply)
    receiveBounded fuel before bounded (inj₁ problem) = Cost.done (serializationFailed problem)
    receiveBounded fuel before bounded (inj₂ bytes) with length bytes ≤? byteLimit
    ... | yes fits = Cost.done (ready before unchanged bytes fits)
    ... | no tooLarge = shrinkBounded fuel before bounded bytes tooLarge

    shrinkBounded : ∀ fuel before bounded bytes tooLarge → Cost.Bounded fuel (shrink fuel before bounded bytes tooLarge)
    shrinkBounded fuel before bounded bytes tooLarge = shrinkViewBounded fuel before bounded bytes tooLarge (P.view (R.Trace.events before))

    shrinkViewBounded : ∀ fuel before bounded bytes tooLarge view →
      Cost.Bounded fuel (shrinkView fuel before bounded bytes tooLarge view)
    shrinkViewBounded fuel before bounded bytes tooLarge (P.empty exact) = Cost.done metadataTooLarge
    shrinkViewBounded zero before bounded bytes tooLarge (P.nonempty selection) = ⊥-elim (emptyCannotPop before selection bounded)
    shrinkViewBounded (suc fuel) before bounded bytes tooLarge (P.nonempty selection) =
      shrinkEvaluatedBounded fuel before bounded bytes tooLarge selection (U.execute checks (suc (R.Trace.eventsOmitted before))) refl

    shrinkEvaluatedBounded : ∀ fuel before bounded bytes tooLarge selection evaluation evaluated →
      Cost.Bounded (suc fuel) (shrinkEvaluated fuel before bounded bytes tooLarge selection evaluation evaluated)
    shrinkEvaluatedBounded fuel before bounded bytes tooLarge selection (U.panic overflow) evaluated = Cost.done arithmeticPanic
    shrinkEvaluatedBounded fuel before bounded bytes tooLarge selection (U.returned count) evaluated =
      mapBounded (lift (removed selection count evaluated bytes tooLarge))
      (trimBounded fuel (shorten before selection count) (P.decreases fuel selection bounded))

  serializationsBounded : ∀ fuel before bounded events result → E.Runs (trim fuel before bounded) events result →
    Cost.count events ≤ suc fuel
  serializationsBounded fuel before bounded events result = Cost.runBounded (trimBounded fuel before bounded)

  interruptedSerializationsBounded : ∀ fuel before bounded events residual → E.Prefix (trim fuel before bounded) events residual →
    Cost.count events ≤ suc fuel
  interruptedSerializationsBounded fuel before bounded events residual = Cost.prefixBounded (trimBounded fuel before bounded)
