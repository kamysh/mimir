{-# OPTIONS --safe #-}
-- Concrete field types, order, required fields and defaults for all persisted
-- judge records. Both map and positional-array visitors use these descriptors.
module Mimir.JudgeStateDecode where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ)
open import Data.Integer using (ℤ)
open import Data.String using (toList)
open import Data.Sum using (_⊎_)
open import Mimir.Text using (Text)
import Mimir.Validation as V
import Mimir.StructuredValue as JSON
import Mimir.RecordDecoding as Array
import Mimir.SerdeSequence as Sequence
import Mimir.JudgeStatePrimitives as P
import Mimir.JudgeStateWire as Wire
import Mimir.UUIDGroups as UUID
import Mimir.SourceFailure as Source

open Sequence using (Field; Values; empty; more)
module R = Wire.R

module Size (sizeMaximum : ℕ) where
  size : JSON.Value → V.Fault ⊎ ℕ
  size = P.uint sizeMaximum

  u64 : JSON.Value → V.Fault ⊎ ℕ
  u64 = P.uint P.u64Maximum

  sourceFields : List Field
  sourceFields =
    P.required (toList "stage") Text JSON.asString ∷
    P.required (toList "detail") Text JSON.asString ∷
    P.required (toList "total_bytes") ℕ size ∷
    P.required (toList "excerpt_start") ℕ size ∷
    P.required (toList "excerpt") Text JSON.asString ∷ []

  buildSource : Values sourceFields → Source.Failure
  buildSource (more stage (more detail (more total (more start (more excerpt empty))))) = Source.failure stage detail total start excerpt

  source : JSON.Value → V.Fault ⊎ Source.Failure
  source = P.recordDecoder sourceFields buildSource

  deferredFields : List Field
  deferredFields =
    P.required (toList "id") UUID.UUID P.uuid ∷
    P.required (toList "revision") ℤ P.signed ∷ []

  buildDeferred : Values deferredFields → R.Deferred
  buildDeferred (more identity (more revision empty)) = R.deferred identity revision

  deferred : JSON.Value → V.Fault ⊎ R.Deferred
  deferred = P.recordDecoder deferredFields buildDeferred

  diagnosticFields : List Field
  diagnosticFields =
    P.defaulted (toList "observed_at") ℕ u64 0 ∷
    P.required (toList "experience_id") UUID.UUID P.uuid ∷
    P.required (toList "tool") Text JSON.asString ∷
    P.required (toList "detail") Text JSON.asString ∷ []

  buildDiagnostic : Values diagnosticFields → R.FailureDiagnostic
  buildDiagnostic (more observed (more identity (more tool (more detail empty)))) = R.diagnosticValue observed identity tool detail

  diagnostic : JSON.Value → V.Fault ⊎ R.FailureDiagnostic
  diagnostic = P.recordDecoder diagnosticFields buildDiagnostic

  reportFields : List Field
  reportFields =
    P.required (toList "status") Text JSON.asString ∷
    P.optional (toList "block_reason") Text JSON.asString ∷
    P.optional (toList "diagnostic") R.FailureDiagnostic diagnostic ∷
    P.optional (toList "failure_detail") Text JSON.asString ∷
    P.optional (toList "failure_source") Source.Failure source ∷
    P.optional (toList "diagnostics_id") UUID.UUID P.uuid ∷
    P.defaulted (toList "selected_ids") (List UUID.UUID) (Array.readArray P.uuid) [] ∷
    P.required (toList "selected") ℕ size ∷
    P.required (toList "confirmed") ℕ size ∷
    P.required (toList "corrected") ℕ size ∷
    P.required (toList "pending") ℕ size ∷
    P.required (toList "unavailable") ℕ size ∷
    P.defaulted (toList "deferred_reviews") (List R.Deferred) (Array.readArray deferred) [] ∷
    P.defaulted (toList "notification") Text JSON.asString [] ∷
    P.required (toList "recorded_at") ℕ u64 ∷ []

  buildReport : Values reportFields → R.Report
  buildReport (more status (more reason (more diagnosticValue (more detail (more sourceValue
    (more diagnosticsId (more selectedIds (more selected (more confirmed (more corrected
    (more pending (more unavailable (more deferredValues (more notification (more recorded empty))))))))))))))) =
    R.reportValue status reason diagnosticValue detail sourceValue diagnosticsId selectedIds
      selected confirmed corrected pending unavailable deferredValues notification recorded

  report : JSON.Value → V.Fault ⊎ R.Report
  report = P.recordDecoder reportFields buildReport

  confirmedFields : List Field
  confirmedFields =
    P.required (toList "id") UUID.UUID P.uuid ∷
    P.required (toList "recorded_at") ℕ u64 ∷ []

  buildConfirmed : Values confirmedFields → R.Confirmed
  buildConfirmed (more identity (more recorded empty)) = R.confirmedValue identity recorded

  confirmed : JSON.Value → V.Fault ⊎ R.Confirmed
  confirmed = P.recordDecoder confirmedFields buildConfirmed

  incidentFields : List Field
  incidentFields =
    P.required (toList "first") R.Report report ∷
    P.optional (toList "latest") R.Report report ∷
    P.defaulted (toList "confirmed_reviews") (List R.Confirmed) (Array.readArray confirmed) [] ∷
    P.optional (toList "recovered_at") ℕ u64 ∷ []

  buildIncident : Values incidentFields → R.Incident
  buildIncident (more first (more latest (more confirmations (more recovered empty)))) = R.incident first latest confirmations recovered

  incident : JSON.Value → V.Fault ⊎ R.Incident
  incident = P.recordDecoder incidentFields buildIncident

  eventFields : List Field
  eventFields =
    P.required (toList "at") ℕ u64 ∷
    P.required (toList "experience_id") UUID.UUID P.uuid ∷
    P.required (toList "kind") Text JSON.asString ∷
    P.optional (toList "model_requests") ℕ size ∷
    P.optional (toList "tool_attempts") ℕ size ∷
    P.optional (toList "tool") Text JSON.asString ∷
    P.optional (toList "detail") Text JSON.asString ∷
    P.optional (toList "detail_bytes") ℕ size ∷ []

  buildEvent : Values eventFields → R.Event
  buildEvent (more at (more identity (more kind (more model (more toolBudget (more tool (more detail (more bytes empty)))))))) =
    R.eventValue at identity kind model toolBudget tool detail bytes

  event : JSON.Value → V.Fault ⊎ R.Event
  event = P.recordDecoder eventFields buildEvent

  traceFields : List Field
  traceFields =
    P.required (toList "id") UUID.UUID P.uuid ∷
    P.required (toList "started_at") ℕ u64 ∷
    P.optional (toList "finished_at") ℕ u64 ∷
    P.required (toList "status") Text JSON.asString ∷
    P.optional (toList "block_reason") Text JSON.asString ∷
    P.required (toList "selected_ids") (List UUID.UUID) (Array.readArray P.uuid) ∷
    P.optional (toList "model_requests") ℕ size ∷
    P.optional (toList "tool_attempts") ℕ size ∷
    P.required (toList "events") (List R.Event) (Array.readArray event) ∷
    P.defaulted (toList "events_omitted") ℕ size 0 ∷ []

  buildTrace : Values traceFields → R.Trace
  buildTrace (more identity (more started (more finished (more status (more reason (more selected
    (more model (more tool (more events (more omitted empty)))))))))) = R.traceValue identity started finished status reason selected model tool events omitted

  trace : JSON.Value → V.Fault ⊎ R.Trace
  trace = P.recordDecoder traceFields buildTrace

  diagnosticsFields : List Field
  diagnosticsFields = P.defaulted (toList "attempts") (List R.Trace) (Array.readArray trace) [] ∷ []

  buildDiagnostics : Values diagnosticsFields → R.Diagnostics
  buildDiagnostics (more attempts empty) = attempts

  diagnostics : JSON.Value → V.Fault ⊎ R.Diagnostics
  diagnostics = P.recordDecoder diagnosticsFields buildDiagnostics
