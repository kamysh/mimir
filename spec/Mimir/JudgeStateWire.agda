{-# OPTIONS --safe #-}
-- Exact serde Serialize member order and omission rules for every judge-state
-- record. Unknown/duplicate fields and numeric admission belong to decoding.
module Mimir.JudgeStateWire where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Mimir.Text using (Text)
import Mimir.StructuredValue as JSON
import Mimir.JudgeStateRecords as State
import Mimir.SourceFailure as Source
import Mimir.UUIDGroups as UUID
import Mimir.UUIDSchema as UUIDCodecDependency
import Mimir.StandardLibrary as Library

module R = State.Over UUID.UUID
module Common where
  Fields = List (Text × JSON.Value)

  member : Text → JSON.Value → Fields
  member name value = (name , value) ∷ []

  optional : ∀ {A : Set} → Text → (A → JSON.Value) → Maybe A → Fields
  optional name encode nothing = []
  optional name encode (just value) = member name (encode value)

  nonempty : ∀ {A : Set} → Text → (A → JSON.Value) → List A → Fields
  nonempty name encode [] = []
  nonempty name encode (value ∷ values) = member name (JSON.array (map encode (value ∷ values)))

  nonemptyText : Text → Text → Fields
  nonemptyText name [] = []
  nonemptyText name (char ∷ chars) = member name (JSON.string (char ∷ chars))

  sourceFields : Source.Failure → Fields
  sourceFields value =
    (toList "stage" , JSON.string (Source.Failure.stage value)) ∷
    (toList "detail" , JSON.string (Source.Failure.detail value)) ∷
    (toList "total_bytes" , JSON.unsigned (Source.Failure.totalBytes value)) ∷
    (toList "excerpt_start" , JSON.unsigned (Source.Failure.excerptStart value)) ∷
    (toList "excerpt" , JSON.string (Source.Failure.excerpt value)) ∷ []

  source : Source.Failure → JSON.Value
  source value = JSON.object (sourceFields value)


open Common public

module With (library : Library.Contract) where
  module UUIDCodec = UUIDCodecDependency library
  open Common public

  deferred : R.Deferred → JSON.Value
  deferred value = JSON.object
    ((toList "id" , UUIDCodec.encode (R.Deferred.identity value)) ∷
     (toList "revision" , JSON.signed (R.Deferred.revision value)) ∷ [])

  diagnostic : R.FailureDiagnostic → JSON.Value
  diagnostic value = JSON.object
    ((toList "observed_at" , JSON.unsigned (R.FailureDiagnostic.observedAt value)) ∷
     (toList "experience_id" , UUIDCodec.encode (R.FailureDiagnostic.experience value)) ∷
     (toList "tool" , JSON.string (R.FailureDiagnostic.tool value)) ∷
     (toList "detail" , JSON.string (R.FailureDiagnostic.detail value)) ∷ [])

  reportFields : R.Report → Fields
  reportFields value = member (toList "status") (JSON.string (R.Report.status value)) ++
    optional (toList "block_reason") JSON.string (R.Report.blockReason value) ++
    optional (toList "diagnostic") diagnostic (R.Report.diagnostic value) ++
    optional (toList "failure_detail") JSON.string (R.Report.failureDetail value) ++
    optional (toList "failure_source") source (R.Report.failureSource value) ++
    optional (toList "diagnostics_id") UUIDCodec.encode (R.Report.diagnosticsId value) ++
    nonempty (toList "selected_ids") UUIDCodec.encode (R.Report.selectedIds value) ++
    ((toList "selected" , JSON.unsigned (R.Report.selected value)) ∷
     (toList "confirmed" , JSON.unsigned (R.Report.confirmed value)) ∷
     (toList "corrected" , JSON.unsigned (R.Report.corrected value)) ∷
     (toList "pending" , JSON.unsigned (R.Report.pending value)) ∷
     (toList "unavailable" , JSON.unsigned (R.Report.unavailable value)) ∷ []) ++
    nonempty (toList "deferred_reviews") deferred (R.Report.deferredReviews value) ++
    nonemptyText (toList "notification") (R.Report.notification value) ++
    member (toList "recorded_at") (JSON.unsigned (R.Report.recordedAt value))

  report : R.Report → JSON.Value
  report value = JSON.object (reportFields value)

  confirmed : R.Confirmed → JSON.Value
  confirmed value = JSON.object
    ((toList "id" , UUIDCodec.encode (R.Confirmed.identity value)) ∷
     (toList "recorded_at" , JSON.unsigned (R.Confirmed.recordedAt value)) ∷ [])

  incidentFields : R.Incident → Fields
  incidentFields value = member (toList "first") (report (R.Incident.first value)) ++
    optional (toList "latest") report (R.Incident.latest value) ++
    nonempty (toList "confirmed_reviews") confirmed (R.Incident.confirmedReviews value) ++
    optional (toList "recovered_at") JSON.unsigned (R.Incident.recoveredAt value)

  incident : R.Incident → JSON.Value
  incident value = JSON.object (incidentFields value)

  eventFields : R.Event → Fields
  eventFields value =
    ((toList "at" , JSON.unsigned (R.Event.at value)) ∷
     (toList "experience_id" , UUIDCodec.encode (R.Event.experience value)) ∷
     (toList "kind" , JSON.string (R.Event.kind value)) ∷ []) ++
    optional (toList "model_requests") JSON.unsigned (R.Event.modelRequests value) ++
    optional (toList "tool_attempts") JSON.unsigned (R.Event.toolAttempts value) ++
    optional (toList "tool") JSON.string (R.Event.tool value) ++
    optional (toList "detail") JSON.string (R.Event.detail value) ++
    optional (toList "detail_bytes") JSON.unsigned (R.Event.detailBytes value)

  event : R.Event → JSON.Value
  event value = JSON.object (eventFields value)

  traceFields : R.Trace → Fields
  traceFields value =
    ((toList "id" , UUIDCodec.encode (R.Trace.identity value)) ∷
     (toList "started_at" , JSON.unsigned (R.Trace.startedAt value)) ∷ []) ++
    optional (toList "finished_at") JSON.unsigned (R.Trace.finishedAt value) ++
    member (toList "status") (JSON.string (R.Trace.status value)) ++
    optional (toList "block_reason") JSON.string (R.Trace.blockReason value) ++
    member (toList "selected_ids") (JSON.array (map UUIDCodec.encode (R.Trace.selectedIds value))) ++
    optional (toList "model_requests") JSON.unsigned (R.Trace.modelRequests value) ++
    optional (toList "tool_attempts") JSON.unsigned (R.Trace.toolAttempts value) ++
    ((toList "events" , JSON.array (map event (R.Trace.events value))) ∷
     (toList "events_omitted" , JSON.unsigned (R.Trace.eventsOmitted value)) ∷ [])

  trace : R.Trace → JSON.Value
  trace value = JSON.object (traceFields value)

  diagnostics : R.Diagnostics → JSON.Value
  diagnostics values = JSON.object (member (toList "attempts") (JSON.array (map trace values)))

  optionalNothing : ∀ {A : Set} name (encode : A → JSON.Value) → optional name encode nothing ≡ []
  optionalNothing name encode = refl

  optionalJust : ∀ {A : Set} name (encode : A → JSON.Value) value → optional name encode (just value) ≡ member name (encode value)
  optionalJust name encode value = refl

  -- Some(empty) and None are distinct. Serde omits only None for these fields.
  presentEmptyText : ∀ name → optional name JSON.string (just []) ≡ member name (JSON.string [])
  presentEmptyText name = refl

  eventDetailSizeRetained : ∀ value bytes → R.Event.detailBytes value ≡ just bytes →
    optional (toList "detail_bytes") JSON.unsigned (R.Event.detailBytes value) ≡ member (toList "detail_bytes") (JSON.unsigned bytes)
  eventDetailSizeRetained value bytes same = cong (optional (toList "detail_bytes") JSON.unsigned) same
