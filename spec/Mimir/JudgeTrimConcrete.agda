{-# OPTIONS --safe #-}
-- Complete trimming executions use the concrete record serializer at every
-- pass. Removed-event prefixes remain valid text; receipts and the finite
-- serialization bound are inherited by the composed execution.
module Mimir.JudgeTrimConcrete where

open import Data.List using (length)
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.All.Properties as All
open import Data.Nat using (ℕ; zero; suc; _≤_; _≤?_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (refl; subst)
import Mimir.SignedMachine as Machine
import Mimir.UUIDGroups as UUID
import Mimir.JudgeTraceTrim as Trim
import Mimir.JudgeTraceConcrete as Concrete
import Mimir.JudgeStateText as Text
import Mimir.JudgeStateSerialize as Serialize
import Mimir.EffectsInterpret as Interpret

module Limits (maximum eventLimit byteLimit : ℕ) (checks : Machine.OverflowChecks) where
  module T = Trim.Over UUID.UUID maximum eventLimit byteLimit checks
  module E = T.E
  module R = T.R
  module P = T.P
  module U = T.U
  module C = Concrete.Limits maximum eventLimit byteLimit checks

  Admitted : E.Operation → Set
  Admitted (E.serialize value) = Text.TraceText value

  respond : ∀ operation → Admitted operation → E.Reply operation
  respond (E.serialize value) valid = inj₂ (Serialize.traceBytes value valid)

  module Run = Interpret.With E.Operation E.Reply Admitted respond

  shortenText : ∀ before selection count → Text.TraceText before → Text.TraceText (T.shorten before selection count)
  shortenText before selection count valid = record
    { status = Text.TraceText.status valid ; reason = Text.TraceText.reason valid
    ; events = All.++⁻ˡ (P.Popped.prefix selection)
        (subst (All.All Text.EventText) (P.Popped.exact selection) (Text.TraceText.events valid)) }

  mapSupported : ∀ {A B : Set} {program : E.Script A} (change : A → B) → Run.Supported program → Run.Supported (T.mapResult change program)
  mapSupported change (Run.returned value) = Run.returned (change value)
  mapSupported change (Run.requested operation next valid supported) = Run.requested operation _ valid
    (λ reply → mapSupported change (supported reply))

  mutual
    trimSupported : ∀ fuel before bounded → Text.TraceText before → Run.Supported (T.trim fuel before bounded)
    trimSupported fuel before bounded valid = Run.requested (E.serialize before) _ valid (receiveSupported fuel before bounded valid)

    receiveSupported : ∀ fuel before bounded → Text.TraceText before → ∀ reply → Run.Supported (T.receive fuel before bounded reply)
    receiveSupported fuel before bounded valid (inj₁ problem) = Run.returned (T.serializationFailed problem)
    receiveSupported fuel before bounded valid (inj₂ bytes) with length bytes ≤? byteLimit
    ... | yes fits = Run.returned (T.ready before T.unchanged bytes fits)
    ... | no tooLarge = shrinkSupported fuel before bounded valid bytes tooLarge

    shrinkSupported : ∀ fuel before bounded → Text.TraceText before → ∀ bytes tooLarge → Run.Supported (T.shrink fuel before bounded bytes tooLarge)
    shrinkSupported fuel before bounded valid bytes tooLarge = shrinkViewSupported fuel before bounded valid bytes tooLarge (P.view (R.Trace.events before))

    shrinkViewSupported : ∀ fuel before bounded → Text.TraceText before → ∀ bytes tooLarge view →
      Run.Supported (T.shrinkView fuel before bounded bytes tooLarge view)
    shrinkViewSupported fuel before bounded valid bytes tooLarge (P.empty exact) = Run.returned T.metadataTooLarge
    shrinkViewSupported zero before bounded valid bytes tooLarge (P.nonempty selection) = ⊥-elim (T.emptyCannotPop before selection bounded)
    shrinkViewSupported (suc fuel) before bounded valid bytes tooLarge (P.nonempty selection) =
      shrinkEvaluatedSupported fuel before bounded valid bytes tooLarge selection (U.execute checks (suc (R.Trace.eventsOmitted before))) refl

    shrinkEvaluatedSupported : ∀ fuel before bounded → Text.TraceText before → ∀ bytes tooLarge selection evaluation evaluated →
      Run.Supported (T.shrinkEvaluated fuel before bounded bytes tooLarge selection evaluation evaluated)
    shrinkEvaluatedSupported fuel before bounded valid bytes tooLarge selection (U.panic overflow) evaluated = Run.returned T.arithmeticPanic
    shrinkEvaluatedSupported fuel before bounded valid bytes tooLarge selection (U.returned count) evaluated =
      mapSupported (T.lift (T.removed selection count evaluated bytes tooLarge))
        (trimSupported fuel (T.shorten before selection count) (P.decreases fuel selection bounded) (shortenText before selection count valid))

  evaluate : ∀ before → Text.TraceText before → Run.Evaluation (T.trim (length (R.Trace.events before)) before ≤-refl)
  evaluate before valid = Run.evaluate (T.trim (length (R.Trace.events before)) before ≤-refl)
    (trimSupported (length (R.Trace.events before)) before ≤-refl valid)

  exactReceipt : ∀ event → Run.Receipt event → C.ExactReceipt event
  exactReceipt (E.serialize value , .(inj₂ (Serialize.traceBytes value valid))) (valid , refl) = valid , refl

  exactReceipts : ∀ before valid → All.All C.ExactReceipt (Run.Evaluation.events (evaluate before valid))
  exactReceipts before valid = All.map (λ {event} receipt → exactReceipt event receipt) (Run.Evaluation.receipts (evaluate before valid))

  serializationsBounded : ∀ before valid → E.Cost.count (Run.Evaluation.events (evaluate before valid)) ≤ suc (length (R.Trace.events before))
  serializationsBounded before valid = T.serializationsBounded (length (R.Trace.events before)) before ≤-refl _ _
    (Run.Evaluation.run (evaluate before valid))
