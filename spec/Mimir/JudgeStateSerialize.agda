{-# OPTIONS --safe #-}
-- Concrete compact JSON serialization for every persisted judge record.
-- All text carries Rust's scalar-domain witness. Numeric bounds are proved
-- separately; no float codec or external serializer oracle is used here.
module Mimir.JudgeStateSerialize where

open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Product using (_,_)
open import Data.String using (String; toList)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable.Core using (True; toWitness)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Function.Base using (_$_)
open import Mimir.Bits using (Byte)
import Mimir.UnicodeText as Unicode
import Mimir.StructuredValue as JSON
import Mimir.JsonCompactRecords as C
import Mimir.JsonRecordSupport as Support
import Mimir.JudgeStateWire as W
import Mimir.JudgeStateText as T
import Mimir.UUIDSchema as UUID
import Mimir.SourceFailure as Source
module R = W.R

entry : ∀ name → True (Unicode.valid? (toList name)) → ∀ {value} → C.Supported value → C.FieldSupported (toList name , value)
entry name valid supported = toWitness {a? = Unicode.valid? (toList name)} valid , supported

member : ∀ name → True (Unicode.valid? (toList name)) → ∀ {value} → C.Supported value → All C.FieldSupported (W.member (toList name) value)
member name valid supported = entry name valid supported All.∷ All.[]

uuid : ∀ value → C.Supported (UUID.encode value)
uuid value = C.string (UUID.valid value)

source : ∀ value → T.SourceText value → C.Supported (W.source value)
source value valid = C.object $
  entry "stage" tt (C.string (T.SourceText.stage valid)) All.∷
  entry "detail" tt (C.string (T.SourceText.detail valid)) All.∷
  entry "total_bytes" tt (C.unsigned (Source.Failure.totalBytes value)) All.∷
  entry "excerpt_start" tt (C.unsigned (Source.Failure.excerptStart value)) All.∷
  entry "excerpt" tt (C.string (T.SourceText.excerpt valid)) All.∷ All.[]

deferred : ∀ value → C.Supported (W.deferred value)
deferred value = C.object $
  entry "id" tt (uuid (R.Deferred.identity value)) All.∷
  entry "revision" tt (C.signed (R.Deferred.revision value)) All.∷ All.[]

diagnostic : ∀ value → T.DiagnosticText value → C.Supported (W.diagnostic value)
diagnostic value valid = C.object $
  entry "observed_at" tt (C.unsigned (R.FailureDiagnostic.observedAt value)) All.∷
  entry "experience_id" tt (uuid (R.FailureDiagnostic.experience value)) All.∷
  entry "tool" tt (C.string (T.DiagnosticText.tool valid)) All.∷
  entry "detail" tt (C.string (T.DiagnosticText.detail valid)) All.∷ All.[]

report : ∀ value → T.ReportText value → C.Supported (W.report value)
report value valid = C.object $
  ++⁺ (member "status" tt (C.string (T.ReportText.status valid))) $
  ++⁺ (Support.optional (toList "block_reason") tt JSON.string (λ value valid → C.string valid) (R.Report.blockReason value) (T.ReportText.reason valid)) $
  ++⁺ (Support.optional (toList "diagnostic") tt W.diagnostic diagnostic (R.Report.diagnostic value) (T.ReportText.diagnostic valid)) $
  ++⁺ (Support.optional (toList "failure_detail") tt JSON.string (λ value valid → C.string valid) (R.Report.failureDetail value) (T.ReportText.detail valid)) $
  ++⁺ (Support.optional (toList "failure_source") tt W.source source (R.Report.failureSource value) (T.ReportText.source valid)) $
  ++⁺ (Support.optionalUniform (toList "diagnostics_id") tt UUID.encode uuid (R.Report.diagnosticsId value)) $
  ++⁺ (Support.nonemptyUniform (toList "selected_ids") tt UUID.encode uuid (R.Report.selectedIds value)) $
  ++⁺ (entry "selected" tt (C.unsigned (R.Report.selected value)) All.∷
    entry "confirmed" tt (C.unsigned (R.Report.confirmed value)) All.∷
    entry "corrected" tt (C.unsigned (R.Report.corrected value)) All.∷
    entry "pending" tt (C.unsigned (R.Report.pending value)) All.∷
    entry "unavailable" tt (C.unsigned (R.Report.unavailable value)) All.∷ All.[]) $
  ++⁺ (Support.nonemptyUniform (toList "deferred_reviews") tt W.deferred deferred (R.Report.deferredReviews value)) $
  ++⁺ (Support.nonemptyText (toList "notification") tt (R.Report.notification value) (T.ReportText.notification valid)) $
  member "recorded_at" tt (C.unsigned (R.Report.recordedAt value))

confirmed : ∀ value → C.Supported (W.confirmed value)
confirmed value = C.object $
  entry "id" tt (uuid (R.Confirmed.identity value)) All.∷
  entry "recorded_at" tt (C.unsigned (R.Confirmed.recordedAt value)) All.∷ All.[]

incident : ∀ value → T.IncidentText value → C.Supported (W.incident value)
incident value valid = C.object $
  ++⁺ (member "first" tt (report (R.Incident.first value) (T.IncidentText.first valid))) $
  ++⁺ (Support.optional (toList "latest") tt W.report report (R.Incident.latest value) (T.IncidentText.latest valid)) $
  ++⁺ (Support.nonemptyUniform (toList "confirmed_reviews") tt W.confirmed confirmed (R.Incident.confirmedReviews value)) $
  Support.optionalUniform (toList "recovered_at") tt JSON.unsigned C.unsigned (R.Incident.recoveredAt value)

event : ∀ value → T.EventText value → C.Supported (W.event value)
event value valid = C.object $
  ++⁺ (entry "at" tt (C.unsigned (R.Event.at value)) All.∷
    entry "experience_id" tt (uuid (R.Event.experience value)) All.∷
    entry "kind" tt (C.string (T.EventText.kind valid)) All.∷ All.[]) $
  ++⁺ (Support.optionalUniform (toList "model_requests") tt JSON.unsigned C.unsigned (R.Event.modelRequests value)) $
  ++⁺ (Support.optionalUniform (toList "tool_attempts") tt JSON.unsigned C.unsigned (R.Event.toolAttempts value)) $
  ++⁺ (Support.optional (toList "tool") tt JSON.string (λ value valid → C.string valid) (R.Event.tool value) (T.EventText.tool valid)) $
  ++⁺ (Support.optional (toList "detail") tt JSON.string (λ value valid → C.string valid) (R.Event.detail value) (T.EventText.detail valid)) $
  Support.optionalUniform (toList "detail_bytes") tt JSON.unsigned C.unsigned (R.Event.detailBytes value)

trace : ∀ value → T.TraceText value → C.Supported (W.trace value)
trace value valid = C.object $
  ++⁺ (entry "id" tt (uuid (R.Trace.identity value)) All.∷
    entry "started_at" tt (C.unsigned (R.Trace.startedAt value)) All.∷ All.[]) $
  ++⁺ (Support.optionalUniform (toList "finished_at") tt JSON.unsigned C.unsigned (R.Trace.finishedAt value)) $
  ++⁺ (member "status" tt (C.string (T.TraceText.status valid))) $
  ++⁺ (Support.optional (toList "block_reason") tt JSON.string (λ value valid → C.string valid) (R.Trace.blockReason value) (T.TraceText.reason valid)) $
  ++⁺ (member "selected_ids" tt (C.array (Support.arrayUniform UUID.encode uuid (R.Trace.selectedIds value)))) $
  ++⁺ (Support.optionalUniform (toList "model_requests") tt JSON.unsigned C.unsigned (R.Trace.modelRequests value)) $
  ++⁺ (Support.optionalUniform (toList "tool_attempts") tt JSON.unsigned C.unsigned (R.Trace.toolAttempts value)) $
  entry "events" tt (C.array (Support.array W.event event (R.Trace.events value) (T.TraceText.events valid))) All.∷
  entry "events_omitted" tt (C.unsigned (R.Trace.eventsOmitted value)) All.∷ All.[]

diagnostics : ∀ values → T.DiagnosticsText values → C.Supported (W.diagnostics values)
diagnostics values valid = C.object (member "attempts" tt (C.array (Support.array W.trace trace values valid)))

traceBytes : ∀ value → T.TraceText value → List Byte
traceBytes value valid = C.bytes (W.trace value) (trace value valid)

traceSizeExact : ∀ value valid → length (traceBytes value valid) ≡ C.count (W.trace value) (trace value valid)
traceSizeExact value valid = C.exactCount (W.trace value) (trace value valid)

diagnosticsBytes : ∀ values → T.DiagnosticsText values → List Byte
diagnosticsBytes values valid = C.bytes (W.diagnostics values) (diagnostics values valid)

diagnosticsSizeExact : ∀ values valid → length (diagnosticsBytes values valid) ≡ C.count (W.diagnostics values) (diagnostics values valid)
diagnosticsSizeExact values valid = C.exactCount (W.diagnostics values) (diagnostics values valid)
