{-# OPTIONS --safe #-}
-- The numeric domain of the native persisted structs, including nested
-- records. There are no extra semantic limits on loaded histories or counters.
module Mimir.JudgeStateBounds where

open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤_)
open import Data.Unit using (⊤)
import Mimir.JudgeStateWire as Wire
import Mimir.JudgeStatePrimitives as P
import Mimir.SourceFailure as Source
module R = Wire.R

Optional : ∀ {A : Set} → (A → Set) → Maybe A → Set
Optional predicate nothing = ⊤
Optional predicate (just value) = predicate value

module Size (sizeMaximum : ℕ) where
  record SourceBounds (value : Source.Failure) : Set where
    field
      total : Source.Failure.totalBytes value ≤ sizeMaximum
      start : Source.Failure.excerptStart value ≤ sizeMaximum

  DeferredBounds : R.Deferred → Set
  DeferredBounds value = P.I64.InRange (R.Deferred.revision value)

  DiagnosticBounds : R.FailureDiagnostic → Set
  DiagnosticBounds value = R.FailureDiagnostic.observedAt value ≤ P.u64Maximum

  record ReportBounds (value : R.Report) : Set where
    field
      diagnostic : Optional DiagnosticBounds (R.Report.diagnostic value)
      source : Optional SourceBounds (R.Report.failureSource value)
      selected : R.Report.selected value ≤ sizeMaximum
      confirmed : R.Report.confirmed value ≤ sizeMaximum
      corrected : R.Report.corrected value ≤ sizeMaximum
      pending : R.Report.pending value ≤ sizeMaximum
      unavailable : R.Report.unavailable value ≤ sizeMaximum
      deferred : All DeferredBounds (R.Report.deferredReviews value)
      recorded : R.Report.recordedAt value ≤ P.u64Maximum

  ConfirmedBounds : R.Confirmed → Set
  ConfirmedBounds value = R.Confirmed.recordedAt value ≤ P.u64Maximum

  record IncidentBounds (value : R.Incident) : Set where
    field
      first : ReportBounds (R.Incident.first value)
      latest : Optional ReportBounds (R.Incident.latest value)
      confirmed : All ConfirmedBounds (R.Incident.confirmedReviews value)
      recovered : Optional (_≤ P.u64Maximum) (R.Incident.recoveredAt value)

  record EventBounds (value : R.Event) : Set where
    field
      at : R.Event.at value ≤ P.u64Maximum
      model : R.Event.modelRemaining value ≤ sizeMaximum
      tool : R.Event.toolRemaining value ≤ sizeMaximum
      bytes : Optional (_≤ sizeMaximum) (R.Event.detailBytes value)

  record TraceBounds (value : R.Trace) : Set where
    field
      started : R.Trace.startedAt value ≤ P.u64Maximum
      finished : Optional (_≤ P.u64Maximum) (R.Trace.finishedAt value)
      model : R.Trace.modelRemaining value ≤ sizeMaximum
      tool : R.Trace.toolRemaining value ≤ sizeMaximum
      events : All EventBounds (R.Trace.events value)
      omitted : R.Trace.eventsOmitted value ≤ sizeMaximum

  DiagnosticsBounds : R.Diagnostics → Set
  DiagnosticsBounds = All TraceBounds
