{-# OPTIONS --safe #-}
-- Representation map for judge record identities. All other data is retained.
-- Native persistence uses UUIDs; application identities use the same unsigned
-- big-endian number produced by PublicInput.uuidNumber, with no inverse axiom.
module Mimir.JudgeStateMap where

import Data.List as List
import Data.Maybe as Maybe
import Mimir.JudgeStateRecords as Records
import Mimir.UUIDGroups as UUID
import Mimir.PublicInput as Input
open import Data.Nat using (ℕ)

module Map (From To : Set) (identity : From → To) where
  module S = Records.Over From
  module D = Records.Over To

  deferred : S.Deferred → D.Deferred
  deferred value = record
    { identity = identity (S.Deferred.identity value)
    ; revision = S.Deferred.revision value }

  diagnostic : S.FailureDiagnostic → D.FailureDiagnostic
  diagnostic value = record
    { observedAt = S.FailureDiagnostic.observedAt value
    ; experience = identity (S.FailureDiagnostic.experience value)
    ; tool = S.FailureDiagnostic.tool value
    ; detail = S.FailureDiagnostic.detail value }

  report : S.Report → D.Report
  report value = record
    { status = S.Report.status value
    ; blockReason = S.Report.blockReason value
    ; diagnostic = Maybe.map diagnostic (S.Report.diagnostic value)
    ; failureDetail = S.Report.failureDetail value
    ; failureSource = S.Report.failureSource value
    ; diagnosticsId = Maybe.map identity (S.Report.diagnosticsId value)
    ; selectedIds = List.map identity (S.Report.selectedIds value)
    ; selected = S.Report.selected value
    ; confirmed = S.Report.confirmed value
    ; corrected = S.Report.corrected value
    ; pending = S.Report.pending value
    ; unavailable = S.Report.unavailable value
    ; deferredReviews = List.map deferred (S.Report.deferredReviews value)
    ; notification = S.Report.notification value
    ; recordedAt = S.Report.recordedAt value }

  confirmed : S.Confirmed → D.Confirmed
  confirmed value = record
    { identity = identity (S.Confirmed.identity value)
    ; recordedAt = S.Confirmed.recordedAt value }

  incident : S.Incident → D.Incident
  incident value = record
    { first = report (S.Incident.first value)
    ; latest = Maybe.map report (S.Incident.latest value)
    ; confirmedReviews = List.map confirmed (S.Incident.confirmedReviews value)
    ; recoveredAt = S.Incident.recoveredAt value }

  event : S.Event → D.Event
  event value = record
    { at = S.Event.at value
    ; experience = identity (S.Event.experience value)
    ; kind = S.Event.kind value
    ; modelRemaining = S.Event.modelRemaining value
    ; toolRemaining = S.Event.toolRemaining value
    ; tool = S.Event.tool value
    ; detail = S.Event.detail value
    ; detailBytes = S.Event.detailBytes value }

  trace : S.Trace → D.Trace
  trace value = record
    { identity = identity (S.Trace.identity value)
    ; startedAt = S.Trace.startedAt value
    ; finishedAt = S.Trace.finishedAt value
    ; status = S.Trace.status value
    ; blockReason = S.Trace.blockReason value
    ; selectedIds = List.map identity (S.Trace.selectedIds value)
    ; modelRemaining = S.Trace.modelRemaining value
    ; toolRemaining = S.Trace.toolRemaining value
    ; events = List.map event (S.Trace.events value)
    ; eventsOmitted = S.Trace.eventsOmitted value }

module Native = Map UUID.UUID ℕ Input.uuidNumber
