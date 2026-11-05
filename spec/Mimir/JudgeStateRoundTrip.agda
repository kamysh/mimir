{-# OPTIONS --safe #-}
-- No persisted field is lost on a canonical object round trip. Numeric
-- premises are exactly the native field-width bounds, not history-size or
-- status restrictions. Nested records use their own round-trip proofs.
module Mimir.JudgeStateRoundTrip where

open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Data.Nat using (ℕ)
open import Data.String using (toList)
open import Data.Sum using (inj₂)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable.Core using (toWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import Function.Base using (_$_)
import Mimir.StructuredValue as JSON
import Mimir.JsonObjects as Objects
import Mimir.SerdeSequence as S
import Mimir.SerdeStruct as Struct
import Mimir.SerdeEmission as E
import Mimir.SerdeEmissionBuilders as Build
import Mimir.JudgeStatePrimitives as P
import Mimir.JudgeStateDecode as Decode
import Mimir.JudgeStateBounds as Bounds
import Mimir.JudgeStateWire as W
import Mimir.UUIDSchema as UUID
import Mimir.SourceFailure as Source
import Mimir.RecordDecoding as Array
module R = W.R
module Names = Objects.Names
open S using (empty; more)

finish : ∀ {A : Set} fields (build : S.Values fields → A) values input value →
  Names.Unique (Struct.names fields) → E.Emits fields values input → build values ≡ value →
  P.recordDecoder fields build (JSON.object input) ≡ inj₂ value
finish fields build values input value unique receipt exact =
  trans (cong (P.recordResult build) (E.roundTrip unique receipt)) (cong inj₂ exact)

module Size (sizeMaximum : ℕ) where
  module D = Decode.Size sizeMaximum
  module B = Bounds.Size sizeMaximum

  abstract
    sourceUnique : Names.Unique (Struct.names D.sourceFields)
    sourceUnique = toWitness {a? = Names.unique? (Struct.names D.sourceFields)} tt
    deferredUnique : Names.Unique (Struct.names D.deferredFields)
    deferredUnique = toWitness {a? = Names.unique? (Struct.names D.deferredFields)} tt
    diagnosticUnique : Names.Unique (Struct.names D.diagnosticFields)
    diagnosticUnique = toWitness {a? = Names.unique? (Struct.names D.diagnosticFields)} tt
    confirmedUnique : Names.Unique (Struct.names D.confirmedFields)
    confirmedUnique = toWitness {a? = Names.unique? (Struct.names D.confirmedFields)} tt
    reportUnique : Names.Unique (Struct.names D.reportFields)
    reportUnique = toWitness {a? = Names.unique? (Struct.names D.reportFields)} tt
    incidentUnique : Names.Unique (Struct.names D.incidentFields)
    incidentUnique = toWitness {a? = Names.unique? (Struct.names D.incidentFields)} tt
    eventUnique : Names.Unique (Struct.names D.eventFields)
    eventUnique = toWitness {a? = Names.unique? (Struct.names D.eventFields)} tt
    traceUnique : Names.Unique (Struct.names D.traceFields)
    traceUnique = toWitness {a? = Names.unique? (Struct.names D.traceFields)} tt
    diagnosticsUnique : Names.Unique (Struct.names D.diagnosticsFields)
    diagnosticsUnique = toWitness {a? = Names.unique? (Struct.names D.diagnosticsFields)} tt

  sourceValues : Source.Failure → S.Values D.sourceFields
  sourceValues value = more (Source.Failure.stage value) (more (Source.Failure.detail value)
    (more (Source.Failure.totalBytes value) (more (Source.Failure.excerptStart value) (more (Source.Failure.excerpt value) empty))))

  sourceEmission : ∀ value → B.SourceBounds value → E.Emits D.sourceFields (sourceValues value) (W.sourceFields value)
  sourceEmission value bounded = E.emitted refl (E.emitted refl
    (E.emitted (P.uintRoundTrip sizeMaximum (Source.Failure.totalBytes value) (B.SourceBounds.total bounded))
    (E.emitted (P.uintRoundTrip sizeMaximum (Source.Failure.excerptStart value) (B.SourceBounds.start bounded)) (E.emitted refl E.done))))

  source : ∀ value → B.SourceBounds value → D.source (W.source value) ≡ inj₂ value
  source value bounded = finish D.sourceFields D.buildSource (sourceValues value) (W.sourceFields value) value sourceUnique (sourceEmission value bounded) refl

  deferredValues : R.Deferred → S.Values D.deferredFields
  deferredValues value = more (R.Deferred.identity value) (more (R.Deferred.revision value) empty)

  deferredEmission : ∀ value → B.DeferredBounds value → E.Emits D.deferredFields (deferredValues value)
    ((toList "id" , UUID.encode (R.Deferred.identity value)) ∷ (toList "revision" , JSON.signed (R.Deferred.revision value)) ∷ [])
  deferredEmission value bounded = E.emitted (P.uuidRoundTrip (R.Deferred.identity value))
    (E.emitted (P.signedNumberRoundTrip (R.Deferred.revision value) bounded) E.done)

  deferred : ∀ value → B.DeferredBounds value → D.deferred (W.deferred value) ≡ inj₂ value
  deferred value bounded = finish D.deferredFields D.buildDeferred (deferredValues value) _ value deferredUnique (deferredEmission value bounded) refl

  diagnosticValues : R.FailureDiagnostic → S.Values D.diagnosticFields
  diagnosticValues value = more (R.FailureDiagnostic.observedAt value) (more (R.FailureDiagnostic.experience value)
    (more (R.FailureDiagnostic.tool value) (more (R.FailureDiagnostic.detail value) empty)))

  diagnosticEmission : ∀ value → B.DiagnosticBounds value → E.Emits D.diagnosticFields (diagnosticValues value)
    ((toList "observed_at" , JSON.unsigned (R.FailureDiagnostic.observedAt value)) ∷
     (toList "experience_id" , UUID.encode (R.FailureDiagnostic.experience value)) ∷
     (toList "tool" , JSON.string (R.FailureDiagnostic.tool value)) ∷ (toList "detail" , JSON.string (R.FailureDiagnostic.detail value)) ∷ [])
  diagnosticEmission value bounded = E.emitted (P.uintRoundTrip P.u64Maximum (R.FailureDiagnostic.observedAt value) bounded)
    (E.emitted (P.uuidRoundTrip (R.FailureDiagnostic.experience value)) (E.emitted refl (E.emitted refl E.done)))

  diagnostic : ∀ value → B.DiagnosticBounds value → D.diagnostic (W.diagnostic value) ≡ inj₂ value
  diagnostic value bounded = finish D.diagnosticFields D.buildDiagnostic (diagnosticValues value) _ value diagnosticUnique (diagnosticEmission value bounded) refl

  confirmedValues : R.Confirmed → S.Values D.confirmedFields
  confirmedValues value = more (R.Confirmed.identity value) (more (R.Confirmed.recordedAt value) empty)

  confirmedEmission : ∀ value → B.ConfirmedBounds value → E.Emits D.confirmedFields (confirmedValues value)
    ((toList "id" , UUID.encode (R.Confirmed.identity value)) ∷ (toList "recorded_at" , JSON.unsigned (R.Confirmed.recordedAt value)) ∷ [])
  confirmedEmission value bounded = E.emitted (P.uuidRoundTrip (R.Confirmed.identity value))
    (E.emitted (P.uintRoundTrip P.u64Maximum (R.Confirmed.recordedAt value) bounded) E.done)

  confirmed : ∀ value → B.ConfirmedBounds value → D.confirmed (W.confirmed value) ≡ inj₂ value
  confirmed value bounded = finish D.confirmedFields D.buildConfirmed (confirmedValues value) _ value confirmedUnique (confirmedEmission value bounded) refl

  reportValues : R.Report → S.Values D.reportFields
  reportValues value = more (R.Report.status value) $ more (R.Report.blockReason value) $
    more (R.Report.diagnostic value) $ more (R.Report.failureDetail value) $ more (R.Report.failureSource value) $
    more (R.Report.diagnosticsId value) $ more (R.Report.selectedIds value) $ more (R.Report.selected value) $
    more (R.Report.confirmed value) $ more (R.Report.corrected value) $ more (R.Report.pending value) $
    more (R.Report.unavailable value) $ more (R.Report.deferredReviews value) $ more (R.Report.notification value) $
    more (R.Report.recordedAt value) empty

  reportEmission : ∀ value → B.ReportBounds value → E.Emits D.reportFields (reportValues value) (W.reportFields value)
  reportEmission value bounded = E.emitted refl $
    Build.optionalUniform (toList "block_reason") JSON.string JSON.asString (λ value ()) (λ value → refl) (R.Report.blockReason value) $
    Build.optional (toList "diagnostic") W.diagnostic D.diagnostic (λ value ()) diagnostic (R.Report.diagnostic value) (B.ReportBounds.diagnostic bounded) $
    Build.optionalUniform (toList "failure_detail") JSON.string JSON.asString (λ value ()) (λ value → refl) (R.Report.failureDetail value) $
    Build.optional (toList "failure_source") W.source D.source (λ value ()) source (R.Report.failureSource value) (B.ReportBounds.source bounded) $
    Build.optionalUniform (toList "diagnostics_id") UUID.encode P.uuid (λ value ()) P.uuidRoundTrip (R.Report.diagnosticsId value) $
    Build.nonemptyUniform (toList "selected_ids") UUID.encode P.uuid P.uuidRoundTrip (R.Report.selectedIds value) $
    E.emitted (P.uintRoundTrip sizeMaximum (R.Report.selected value) (B.ReportBounds.selected bounded)) $
    E.emitted (P.uintRoundTrip sizeMaximum (R.Report.confirmed value) (B.ReportBounds.confirmed bounded)) $
    E.emitted (P.uintRoundTrip sizeMaximum (R.Report.corrected value) (B.ReportBounds.corrected bounded)) $
    E.emitted (P.uintRoundTrip sizeMaximum (R.Report.pending value) (B.ReportBounds.pending bounded)) $
    E.emitted (P.uintRoundTrip sizeMaximum (R.Report.unavailable value) (B.ReportBounds.unavailable bounded)) $
    Build.nonempty (toList "deferred_reviews") W.deferred D.deferred deferred (R.Report.deferredReviews value) (B.ReportBounds.deferred bounded) $
    Build.nonemptyText (toList "notification") (R.Report.notification value) $
    E.emitted (P.uintRoundTrip P.u64Maximum (R.Report.recordedAt value) (B.ReportBounds.recorded bounded)) E.done

  report : ∀ value → B.ReportBounds value → D.report (W.report value) ≡ inj₂ value
  report value bounded = finish D.reportFields D.buildReport (reportValues value) (W.reportFields value) value reportUnique (reportEmission value bounded) refl

  incidentValues : R.Incident → S.Values D.incidentFields
  incidentValues value = more (R.Incident.first value) $ more (R.Incident.latest value) $
    more (R.Incident.confirmedReviews value) $ more (R.Incident.recoveredAt value) empty

  incidentEmission : ∀ value → B.IncidentBounds value → E.Emits D.incidentFields (incidentValues value) (W.incidentFields value)
  incidentEmission value bounded = E.emitted (report (R.Incident.first value) (B.IncidentBounds.first bounded)) $
    Build.optional (toList "latest") W.report D.report (λ value ()) report (R.Incident.latest value) (B.IncidentBounds.latest bounded) $
    Build.nonempty (toList "confirmed_reviews") W.confirmed D.confirmed confirmed (R.Incident.confirmedReviews value) (B.IncidentBounds.confirmed bounded) $
    Build.optionalLast (toList "recovered_at") JSON.unsigned D.u64 (λ value ()) (P.uintRoundTrip P.u64Maximum)
      (R.Incident.recoveredAt value) (B.IncidentBounds.recovered bounded)

  incident : ∀ value → B.IncidentBounds value → D.incident (W.incident value) ≡ inj₂ value
  incident value bounded = finish D.incidentFields D.buildIncident (incidentValues value) (W.incidentFields value) value incidentUnique (incidentEmission value bounded) refl

  eventValues : R.Event → S.Values D.eventFields
  eventValues value = more (R.Event.at value) $ more (R.Event.experience value) $ more (R.Event.kind value) $
    more (R.Event.modelRequests value) $ more (R.Event.toolAttempts value) $ more (R.Event.tool value) $
    more (R.Event.detail value) $ more (R.Event.detailBytes value) empty

  eventEmission : ∀ value → B.EventBounds value → E.Emits D.eventFields (eventValues value) (W.eventFields value)
  eventEmission value bounded = E.emitted (P.uintRoundTrip P.u64Maximum (R.Event.at value) (B.EventBounds.at bounded)) $
    E.emitted (P.uuidRoundTrip (R.Event.experience value)) $ E.emitted refl $
    Build.optional (toList "model_requests") JSON.unsigned D.size (λ value ()) (P.uintRoundTrip sizeMaximum)
      (R.Event.modelRequests value) (B.EventBounds.model bounded) $
    Build.optional (toList "tool_attempts") JSON.unsigned D.size (λ value ()) (P.uintRoundTrip sizeMaximum)
      (R.Event.toolAttempts value) (B.EventBounds.tool bounded) $
    Build.optionalUniform (toList "tool") JSON.string JSON.asString (λ value ()) (λ value → refl) (R.Event.tool value) $
    Build.optionalUniform (toList "detail") JSON.string JSON.asString (λ value ()) (λ value → refl) (R.Event.detail value) $
    Build.optionalLast (toList "detail_bytes") JSON.unsigned D.size (λ value ()) (P.uintRoundTrip sizeMaximum)
      (R.Event.detailBytes value) (B.EventBounds.bytes bounded)

  event : ∀ value → B.EventBounds value → D.event (W.event value) ≡ inj₂ value
  event value bounded = finish D.eventFields D.buildEvent (eventValues value) (W.eventFields value) value eventUnique (eventEmission value bounded) refl

  traceValues : R.Trace → S.Values D.traceFields
  traceValues value = more (R.Trace.identity value) $ more (R.Trace.startedAt value) $ more (R.Trace.finishedAt value) $
    more (R.Trace.status value) $ more (R.Trace.blockReason value) $ more (R.Trace.selectedIds value) $
    more (R.Trace.modelRequests value) $ more (R.Trace.toolAttempts value) $ more (R.Trace.events value) $
    more (R.Trace.eventsOmitted value) empty

  traceEmission : ∀ value → B.TraceBounds value → E.Emits D.traceFields (traceValues value) (W.traceFields value)
  traceEmission value bounded = E.emitted (P.uuidRoundTrip (R.Trace.identity value)) $
    E.emitted (P.uintRoundTrip P.u64Maximum (R.Trace.startedAt value) (B.TraceBounds.started bounded)) $
    Build.optional (toList "finished_at") JSON.unsigned D.u64 (λ value ()) (P.uintRoundTrip P.u64Maximum)
      (R.Trace.finishedAt value) (B.TraceBounds.finished bounded) $
    E.emitted refl $
    Build.optionalUniform (toList "block_reason") JSON.string JSON.asString (λ value ()) (λ value → refl) (R.Trace.blockReason value) $
    E.emitted (Array.elementsRoundTrip UUID.encode P.uuid P.uuidRoundTrip 0 (R.Trace.selectedIds value)) $
    Build.optional (toList "model_requests") JSON.unsigned D.size (λ value ()) (P.uintRoundTrip sizeMaximum)
      (R.Trace.modelRequests value) (B.TraceBounds.model bounded) $
    Build.optional (toList "tool_attempts") JSON.unsigned D.size (λ value ()) (P.uintRoundTrip sizeMaximum)
      (R.Trace.toolAttempts value) (B.TraceBounds.tool bounded) $
    E.emitted (Build.array W.event D.event event (R.Trace.events value) (B.TraceBounds.events bounded)) $
    E.emitted (P.uintRoundTrip sizeMaximum (R.Trace.eventsOmitted value) (B.TraceBounds.omitted bounded)) E.done

  trace : ∀ value → B.TraceBounds value → D.trace (W.trace value) ≡ inj₂ value
  trace value bounded = finish D.traceFields D.buildTrace (traceValues value) (W.traceFields value) value traceUnique (traceEmission value bounded) refl

  diagnostics : ∀ values → B.DiagnosticsBounds values → D.diagnostics (W.diagnostics values) ≡ inj₂ values
  diagnostics values bounded = finish D.diagnosticsFields D.buildDiagnostics (more values empty)
    ((toList "attempts" , JSON.array (map W.trace values)) ∷ []) values diagnosticsUnique
    (E.emitted (Build.array W.trace D.trace trace values bounded) E.done) refl
