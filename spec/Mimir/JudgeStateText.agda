{-# OPTIONS --safe #-}
-- Rust String's Unicode-scalar domain for every textual judge-state field.
-- No content, length, status or control-character restrictions are added.
module Mimir.JudgeStateText where

open import Data.List.Relation.Unary.All using (All)
import Mimir.UnicodeText as Unicode
import Mimir.JudgeStateBounds as Bounds
import Mimir.JudgeStateWire as Wire
import Mimir.SourceFailure as Source
module R = Wire.R

record SourceText (value : Source.Failure) : Set where
  field
    stage : Unicode.Valid (Source.Failure.stage value)
    detail : Unicode.Valid (Source.Failure.detail value)
    excerpt : Unicode.Valid (Source.Failure.excerpt value)

record DiagnosticText (value : R.FailureDiagnostic) : Set where
  field
    tool : Unicode.Valid (R.FailureDiagnostic.tool value)
    detail : Unicode.Valid (R.FailureDiagnostic.detail value)

record ReportText (value : R.Report) : Set where
  field
    status : Unicode.Valid (R.Report.status value)
    reason : Bounds.Optional Unicode.Valid (R.Report.blockReason value)
    diagnostic : Bounds.Optional DiagnosticText (R.Report.diagnostic value)
    detail : Bounds.Optional Unicode.Valid (R.Report.failureDetail value)
    source : Bounds.Optional SourceText (R.Report.failureSource value)
    notification : Unicode.Valid (R.Report.notification value)

record IncidentText (value : R.Incident) : Set where
  field
    first : ReportText (R.Incident.first value)
    latest : Bounds.Optional ReportText (R.Incident.latest value)

record EventText (value : R.Event) : Set where
  field
    kind : Unicode.Valid (R.Event.kind value)
    tool : Bounds.Optional Unicode.Valid (R.Event.tool value)
    detail : Bounds.Optional Unicode.Valid (R.Event.detail value)

record TraceText (value : R.Trace) : Set where
  field
    status : Unicode.Valid (R.Trace.status value)
    reason : Bounds.Optional Unicode.Valid (R.Trace.blockReason value)
    events : All EventText (R.Trace.events value)

DiagnosticsText : R.Diagnostics → Set
DiagnosticsText = All TraceText
