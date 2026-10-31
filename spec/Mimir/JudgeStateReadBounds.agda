{-# OPTIONS --safe #-}
-- Every successfully loaded state record satisfies the native field widths,
-- whether it came from an object or a positional array. Defaults and nested
-- collections are covered by the same field-origin proof.
module Mimir.JudgeStateReadBounds where

open import Data.List using ([])
import Data.List.Relation.Unary.All as All
open import Data.Nat using (ℕ; z≤n)
open import Data.Product using (_,_)
open import Data.String using (toList)
open import Data.Sum using (inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Function.Base using (_$_)
import Mimir.SerdeSequence as S
import Mimir.SerdeObtained as O
import Mimir.JudgeStateDecode as Decode
import Mimir.JudgeStateBounds as Bounds
import Mimir.JudgeStateFieldLaws as L
import Mimir.JudgeStatePrimitives as P
import Mimir.StructuredValue as JSON
import Mimir.RecordDecoding as Array

open S using (empty; more)

module Size (sizeMaximum : ℕ) where
  module D = Decode.Size sizeMaximum
  module B = Bounds.Size sizeMaximum

  sourceRules : O.Rules D.sourceFields
  sourceRules = O.Rules.next (O.trivial _) $ O.Rules.next (O.trivial _) $
    O.Rules.next (L.required (toList "total_bytes") D.size (L.unsigned sizeMaximum)) $
    O.Rules.next (L.required (toList "excerpt_start") D.size (L.unsigned sizeMaximum)) $ O.Rules.next (O.trivial _) O.Rules.done

  sourceProperty : ∀ values → O.Satisfied sourceRules values → B.SourceBounds (D.buildSource values)
  sourceProperty (more stage (more detail (more total (more start (more excerpt empty)))))
    (tt , tt , totalBound , startBound , tt , tt) = record { total = totalBound ; start = startBound }

  source : ∀ raw value → D.source raw ≡ inj₂ value → B.SourceBounds value
  source = L.recordBound D.sourceFields D.buildSource sourceRules sourceProperty

  deferredRules : O.Rules D.deferredFields
  deferredRules = O.Rules.next (O.trivial _) $ O.Rules.next (L.required (toList "revision") P.signed L.signed) O.Rules.done

  deferredProperty : ∀ values → O.Satisfied deferredRules values → B.DeferredBounds (D.buildDeferred values)
  deferredProperty (more identity (more revision empty)) (tt , bounded , tt) = bounded

  deferred : ∀ raw value → D.deferred raw ≡ inj₂ value → B.DeferredBounds value
  deferred = L.recordBound D.deferredFields D.buildDeferred deferredRules deferredProperty

  diagnosticRules : O.Rules D.diagnosticFields
  diagnosticRules = O.Rules.next (L.defaulted (toList "observed_at") D.u64 0 (L.unsigned P.u64Maximum) z≤n) $
    O.Rules.next (O.trivial _) $ O.Rules.next (O.trivial _) $ O.Rules.next (O.trivial _) O.Rules.done

  diagnosticProperty : ∀ values → O.Satisfied diagnosticRules values → B.DiagnosticBounds (D.buildDiagnostic values)
  diagnosticProperty (more observed (more identity (more tool (more detail empty)))) (bounded , tt , tt , tt , tt) = bounded

  diagnostic : ∀ raw value → D.diagnostic raw ≡ inj₂ value → B.DiagnosticBounds value
  diagnostic = L.recordBound D.diagnosticFields D.buildDiagnostic diagnosticRules diagnosticProperty

  reportRules : O.Rules D.reportFields
  reportRules = O.Rules.next (O.trivial _) $ O.Rules.next (O.trivial _) $
    O.Rules.next (L.optional (toList "diagnostic") D.diagnostic diagnostic) $ O.Rules.next (O.trivial _) $
    O.Rules.next (L.optional (toList "failure_source") D.source source) $ O.Rules.next (O.trivial _) $ O.Rules.next (O.trivial _) $
    O.Rules.next (L.required (toList "selected") D.size (L.unsigned sizeMaximum)) $
    O.Rules.next (L.required (toList "confirmed") D.size (L.unsigned sizeMaximum)) $
    O.Rules.next (L.required (toList "corrected") D.size (L.unsigned sizeMaximum)) $
    O.Rules.next (L.required (toList "pending") D.size (L.unsigned sizeMaximum)) $
    O.Rules.next (L.required (toList "unavailable") D.size (L.unsigned sizeMaximum)) $
    O.Rules.next (L.defaulted (toList "deferred_reviews") (Array.readArray D.deferred) [] (L.array D.deferred deferred) All.[]) $
    O.Rules.next (O.trivial _) $ O.Rules.next (L.required (toList "recorded_at") D.u64 (L.unsigned P.u64Maximum)) O.Rules.done

  reportProperty : ∀ values → O.Satisfied reportRules values → B.ReportBounds (D.buildReport values)
  reportProperty (more status (more reason (more diagnosticValue (more detail (more sourceValue
    (more diagnosticsId (more selectedIds (more selected (more confirmed (more corrected
    (more pending (more unavailable (more deferredValues (more notification (more recorded empty)))))))))))))))
    (tt , tt , diagnosticBound , tt , sourceBound , tt , tt , selectedBound , confirmedBound , correctedBound ,
      pendingBound , unavailableBound , deferredBound , tt , recordedBound , tt) = record
    { diagnostic = diagnosticBound ; source = sourceBound ; selected = selectedBound ; confirmed = confirmedBound
    ; corrected = correctedBound ; pending = pendingBound ; unavailable = unavailableBound
    ; deferred = deferredBound ; recorded = recordedBound }

  report : ∀ raw value → D.report raw ≡ inj₂ value → B.ReportBounds value
  report = L.recordBound D.reportFields D.buildReport reportRules reportProperty

  confirmedRules : O.Rules D.confirmedFields
  confirmedRules = O.Rules.next (O.trivial _) $ O.Rules.next (L.required (toList "recorded_at") D.u64 (L.unsigned P.u64Maximum)) O.Rules.done

  confirmedProperty : ∀ values → O.Satisfied confirmedRules values → B.ConfirmedBounds (D.buildConfirmed values)
  confirmedProperty (more identity (more recorded empty)) (tt , bounded , tt) = bounded

  confirmed : ∀ raw value → D.confirmed raw ≡ inj₂ value → B.ConfirmedBounds value
  confirmed = L.recordBound D.confirmedFields D.buildConfirmed confirmedRules confirmedProperty

  incidentRules : O.Rules D.incidentFields
  incidentRules = O.Rules.next (L.required (toList "first") D.report report) $
    O.Rules.next (L.optional (toList "latest") D.report report) $
    O.Rules.next (L.defaulted (toList "confirmed_reviews") (Array.readArray D.confirmed) [] (L.array D.confirmed confirmed) All.[]) $
    O.Rules.next (L.optional (toList "recovered_at") D.u64 (L.unsigned P.u64Maximum)) O.Rules.done

  incidentProperty : ∀ values → O.Satisfied incidentRules values → B.IncidentBounds (D.buildIncident values)
  incidentProperty (more first (more latest (more confirmations (more recovered empty))))
    (firstBound , latestBound , confirmedBound , recoveredBound , tt) = record
    { first = firstBound ; latest = latestBound ; confirmed = confirmedBound ; recovered = recoveredBound }

  incident : ∀ raw value → D.incident raw ≡ inj₂ value → B.IncidentBounds value
  incident = L.recordBound D.incidentFields D.buildIncident incidentRules incidentProperty

  eventRules : O.Rules D.eventFields
  eventRules = O.Rules.next (L.required (toList "at") D.u64 (L.unsigned P.u64Maximum)) $
    O.Rules.next (O.trivial _) $ O.Rules.next (O.trivial _) $
    O.Rules.next (L.required (toList "model_remaining") D.size (L.unsigned sizeMaximum)) $
    O.Rules.next (L.required (toList "tool_remaining") D.size (L.unsigned sizeMaximum)) $
    O.Rules.next (O.trivial _) $ O.Rules.next (O.trivial _) $
    O.Rules.next (L.optional (toList "detail_bytes") D.size (L.unsigned sizeMaximum)) O.Rules.done

  eventProperty : ∀ values → O.Satisfied eventRules values → B.EventBounds (D.buildEvent values)
  eventProperty (more at (more identity (more kind (more model (more toolBudget (more tool (more detail (more bytes empty))))))))
    (atBound , tt , tt , modelBound , toolBound , tt , tt , bytesBound , tt) = record
    { at = atBound ; model = modelBound ; tool = toolBound ; bytes = bytesBound }

  event : ∀ raw value → D.event raw ≡ inj₂ value → B.EventBounds value
  event = L.recordBound D.eventFields D.buildEvent eventRules eventProperty

  traceRules : O.Rules D.traceFields
  traceRules = O.Rules.next (O.trivial _) $ O.Rules.next (L.required (toList "started_at") D.u64 (L.unsigned P.u64Maximum)) $
    O.Rules.next (L.optional (toList "finished_at") D.u64 (L.unsigned P.u64Maximum)) $
    O.Rules.next (O.trivial _) $ O.Rules.next (O.trivial _) $ O.Rules.next (O.trivial _) $
    O.Rules.next (L.required (toList "model_remaining") D.size (L.unsigned sizeMaximum)) $
    O.Rules.next (L.required (toList "tool_remaining") D.size (L.unsigned sizeMaximum)) $
    O.Rules.next (L.required (toList "events") (Array.readArray D.event) (L.array D.event event)) $
    O.Rules.next (L.defaulted (toList "events_omitted") D.size 0 (L.unsigned sizeMaximum) z≤n) O.Rules.done

  traceProperty : ∀ values → O.Satisfied traceRules values → B.TraceBounds (D.buildTrace values)
  traceProperty (more identity (more started (more finished (more status (more reason (more selected
    (more model (more tool (more events (more omitted empty))))))))))
    (tt , startedBound , finishedBound , tt , tt , tt , modelBound , toolBound , eventsBound , omittedBound , tt) = record
    { started = startedBound ; finished = finishedBound ; model = modelBound ; tool = toolBound
    ; events = eventsBound ; omitted = omittedBound }

  trace : ∀ raw value → D.trace raw ≡ inj₂ value → B.TraceBounds value
  trace = L.recordBound D.traceFields D.buildTrace traceRules traceProperty

  diagnosticsRules : O.Rules D.diagnosticsFields
  diagnosticsRules = O.Rules.next (L.defaulted (toList "attempts") (Array.readArray D.trace) [] (L.array D.trace trace) All.[]) O.Rules.done

  diagnosticsProperty : ∀ values → O.Satisfied diagnosticsRules values → B.DiagnosticsBounds (D.buildDiagnostics values)
  diagnosticsProperty (more attempts empty) (bounded , tt) = bounded

  diagnostics : ∀ raw value → D.diagnostics raw ≡ inj₂ value → B.DiagnosticsBounds value
  diagnostics = L.recordBound D.diagnosticsFields D.buildDiagnostics diagnosticsRules diagnosticsProperty
