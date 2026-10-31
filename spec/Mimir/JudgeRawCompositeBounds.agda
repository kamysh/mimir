{-# OPTIONS --safe #-}
-- Numeric bounds for all nested judge records, from the actual raw readers.
import Mimir.FloatConversion
module Mimir.JudgeRawCompositeBounds (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Fin using (zero; suc)
open import Data.Nat using (ℕ; _≤_; z≤n)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Unit using (⊤; tt)
import Mimir.JudgeRawLeafBounds as LeafDependency
private
  module Leaf = LeafDependency floatConversion
open import Data.List.Relation.Unary.All using (All; [])
import Mimir.SerdeSlots as Slots
import Mimir.SerdeSlotInvariant as I
import Mimir.SerdeSuccess as S
import Mimir.SerdeFlow as Flow
import Mimir.JudgeRawInvariant as InvariantDependency
private
  module Invariant = InvariantDependency floatConversion
import Mimir.JudgeStateRaw as RawDependency
private
  module Raw = RawDependency floatConversion
import Mimir.JudgeStateBounds as Bounds
import Mimir.JudgeStatePrimitives as P
import Mimir.SignedMachine as Machine

module Parser (checks : Machine.OverflowChecks) (sizeMaximum : ℕ) where
  private
    module R = Raw.Parser checks sizeMaximum
  private
    module D = R.D
  private
    module B = Bounds.Size sizeMaximum
  private
    module Inv = Invariant.Parser checks sizeMaximum

  private
    module L = Leaf.Parser checks sizeMaximum

  reportProperties : I.Predicates D.reportFields
  reportProperties zero value = ⊤
  reportProperties (suc zero) value = ⊤
  reportProperties (suc (suc zero)) value = Bounds.Optional B.DiagnosticBounds value
  reportProperties (suc (suc (suc zero))) value = ⊤
  reportProperties (suc (suc (suc (suc zero)))) value = Bounds.Optional B.SourceBounds value
  reportProperties (suc (suc (suc (suc (suc zero))))) value = ⊤
  reportProperties (suc (suc (suc (suc (suc (suc zero)))))) value = ⊤
  reportProperties (suc (suc (suc (suc (suc (suc (suc zero))))))) value = value ≤ sizeMaximum
  reportProperties (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) value = value ≤ sizeMaximum
  reportProperties (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) value = value ≤ sizeMaximum
  reportProperties (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) value = value ≤ sizeMaximum
  reportProperties (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) value = value ≤ sizeMaximum
  reportProperties (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) value = All B.DeferredBounds value
  reportProperties (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))) value = ⊤
  reportProperties (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))) value = value ≤ P.u64Maximum
  reportProperties (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc ())))))))))))))))

  reportDefaults : I.Defaults D.reportFields reportProperties
  reportDefaults (suc zero) value refl = tt
  reportDefaults (suc (suc zero)) value refl = tt
  reportDefaults (suc (suc (suc zero))) value refl = tt
  reportDefaults (suc (suc (suc (suc zero)))) value refl = tt
  reportDefaults (suc (suc (suc (suc (suc zero))))) value refl = tt
  reportDefaults (suc (suc (suc (suc (suc (suc zero)))))) value refl = tt
  reportDefaults (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) value refl = []
  reportDefaults (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))) value refl = tt
  reportDefaults (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc ()))))))))))))))) value observed

  reportReaders : ∀ allowance index input → S.Ensures (reportProperties index)
    (Flow.Productive.result (Slots.readerAt D.reportFields index (R.reportReaders allowance) input))
  reportReaders allowance zero input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.reportFields zero (R.reportReaders allowance)
      input))
  reportReaders allowance (suc zero) input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.reportFields (suc zero)
      (R.reportReaders allowance) input))
  reportReaders allowance (suc (suc zero)) input = Inv.optional (R.diagnostic allowance) B.DiagnosticBounds
    (L.diagnostic allowance) input
  reportReaders allowance (suc (suc (suc zero))) input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.reportFields (suc (suc (suc zero)))
      (R.reportReaders allowance) input))
  reportReaders allowance (suc (suc (suc (suc zero)))) input = Inv.optional (R.source allowance) B.SourceBounds
    (L.source allowance) input
  reportReaders allowance (suc (suc (suc (suc (suc zero))))) input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.reportFields (suc (suc (suc (suc (suc zero)))))
      (R.reportReaders allowance) input))
  reportReaders allowance (suc (suc (suc (suc (suc (suc zero)))))) input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.reportFields
      (suc (suc (suc (suc (suc (suc zero))))))
      (R.reportReaders allowance) input))
  reportReaders allowance (suc (suc (suc (suc (suc (suc (suc zero))))))) input = Inv.uint sizeMaximum input
  reportReaders allowance (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) input = Inv.uint sizeMaximum input
  reportReaders allowance (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) input = Inv.uint sizeMaximum input
  reportReaders allowance (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) input = Inv.uint sizeMaximum input
  reportReaders allowance (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) input = Inv.uint sizeMaximum input
  reportReaders allowance (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) input = Inv.vector R.deferred B.DeferredBounds L.deferred allowance input
  reportReaders allowance (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))) input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.reportFields
      (suc
       (suc
        (suc
         (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))
      (R.reportReaders allowance) input))
  reportReaders allowance (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))) input = Inv.uint P.u64Maximum input
  reportReaders allowance (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc ()))))))))))))))) input

  reportBuild : ∀ values → I.Valid D.reportFields reportProperties values →
    B.ReportBounds (D.buildReport (Slots.toSequence D.reportFields values))
  reportBuild values valid = record
    { diagnostic = valid (suc (suc zero))
    ; source = valid (suc (suc (suc (suc zero))))
    ; selected = valid (suc (suc (suc (suc (suc (suc (suc zero)))))))
    ; confirmed =
        valid (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
    ; corrected =
        valid (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
    ; pending =
        valid
        (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
    ; unavailable =
        valid
        (suc
         (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
    ; deferred =
        valid
        (suc
         (suc
          (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))
    ; recorded =
        valid
        (suc
         (suc
          (suc
           (suc
            (suc
             (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))
    }

  report : ∀ allowance input → S.Ensures B.ReportBounds (Flow.Productive.result (R.report allowance input))
  report allowance input = Inv.recordValue D.reportFields D.buildReport R.reportReaders
    reportProperties B.ReportBounds reportReaders reportDefaults
    reportBuild allowance input

  incidentProperties : I.Predicates D.incidentFields
  incidentProperties zero value = B.ReportBounds value
  incidentProperties (suc zero) value = Bounds.Optional B.ReportBounds value
  incidentProperties (suc (suc zero)) value = All B.ConfirmedBounds value
  incidentProperties (suc (suc (suc zero))) value = Bounds.Optional (_≤ P.u64Maximum) value
  incidentProperties (suc (suc (suc (suc ()))))

  incidentDefaults : I.Defaults D.incidentFields incidentProperties
  incidentDefaults (suc zero) value refl = tt
  incidentDefaults (suc (suc zero)) value refl = []
  incidentDefaults (suc (suc (suc zero))) value refl = tt
  incidentDefaults (suc (suc (suc (suc ())))) value observed

  incidentReaders : ∀ allowance index input → S.Ensures (incidentProperties index)
    (Flow.Productive.result (Slots.readerAt D.incidentFields index (R.incidentReaders allowance) input))
  incidentReaders allowance zero input = report allowance input
  incidentReaders allowance (suc zero) input = Inv.optional (R.report allowance) B.ReportBounds (report allowance)
    input
  incidentReaders allowance (suc (suc zero)) input = Inv.vector R.confirmed B.ConfirmedBounds L.confirmed allowance
    input
  incidentReaders allowance (suc (suc (suc zero))) input = Inv.optional R.u64 (_≤ P.u64Maximum) (Inv.uint P.u64Maximum) input
  incidentReaders allowance (suc (suc (suc (suc ())))) input

  incidentBuild : ∀ values → I.Valid D.incidentFields incidentProperties values →
    B.IncidentBounds (D.buildIncident (Slots.toSequence D.incidentFields values))
  incidentBuild values valid = record
    { first = valid zero
    ; latest = valid (suc zero)
    ; confirmed = valid (suc (suc zero))
    ; recovered = valid (suc (suc (suc zero)))
    }

  incident : ∀ allowance input → S.Ensures B.IncidentBounds (Flow.Productive.result (R.incident allowance input))
  incident allowance input = Inv.recordValue D.incidentFields D.buildIncident R.incidentReaders
    incidentProperties B.IncidentBounds incidentReaders
    incidentDefaults incidentBuild allowance input

  eventProperties : I.Predicates D.eventFields
  eventProperties zero value = value ≤ P.u64Maximum
  eventProperties (suc zero) value = ⊤
  eventProperties (suc (suc zero)) value = ⊤
  eventProperties (suc (suc (suc zero))) value = value ≤ sizeMaximum
  eventProperties (suc (suc (suc (suc zero)))) value = value ≤ sizeMaximum
  eventProperties (suc (suc (suc (suc (suc zero))))) value = ⊤
  eventProperties (suc (suc (suc (suc (suc (suc zero)))))) value = ⊤
  eventProperties (suc (suc (suc (suc (suc (suc (suc zero))))))) value = Bounds.Optional (_≤ sizeMaximum) value
  eventProperties (suc (suc (suc (suc (suc (suc (suc (suc ()))))))))

  eventDefaults : I.Defaults D.eventFields eventProperties
  eventDefaults (suc (suc (suc (suc (suc zero))))) value refl = tt
  eventDefaults (suc (suc (suc (suc (suc (suc zero)))))) value refl = tt
  eventDefaults (suc (suc (suc (suc (suc (suc (suc zero))))))) value refl = tt
  eventDefaults (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) value observed

  eventReaders : ∀ allowance index input → S.Ensures (eventProperties index)
    (Flow.Productive.result (Slots.readerAt D.eventFields index (R.eventReaders allowance) input))
  eventReaders allowance zero input = Inv.uint P.u64Maximum input
  eventReaders allowance (suc zero) input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.eventFields (suc zero) (R.eventReaders allowance)
      input))
  eventReaders allowance (suc (suc zero)) input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.eventFields (suc (suc zero))
      (R.eventReaders allowance) input))
  eventReaders allowance (suc (suc (suc zero))) input = Inv.uint sizeMaximum input
  eventReaders allowance (suc (suc (suc (suc zero)))) input = Inv.uint sizeMaximum input
  eventReaders allowance (suc (suc (suc (suc (suc zero))))) input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.eventFields (suc (suc (suc (suc (suc zero)))))
      (R.eventReaders allowance) input))
  eventReaders allowance (suc (suc (suc (suc (suc (suc zero)))))) input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.eventFields
      (suc (suc (suc (suc (suc (suc zero)))))) (R.eventReaders allowance)
      input))
  eventReaders allowance (suc (suc (suc (suc (suc (suc (suc zero))))))) input = Inv.optional R.size (_≤ sizeMaximum) (Inv.uint sizeMaximum) input
  eventReaders allowance (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) input

  eventBuild : ∀ values → I.Valid D.eventFields eventProperties values →
    B.EventBounds (D.buildEvent (Slots.toSequence D.eventFields values))
  eventBuild values valid = record
    { at = valid zero
    ; model = valid (suc (suc (suc zero)))
    ; tool = valid (suc (suc (suc (suc zero))))
    ; bytes = valid (suc (suc (suc (suc (suc (suc (suc zero)))))))
    }

  event : ∀ allowance input → S.Ensures B.EventBounds (Flow.Productive.result (R.event allowance input))
  event allowance input = Inv.recordValue D.eventFields D.buildEvent R.eventReaders
    eventProperties B.EventBounds eventReaders eventDefaults eventBuild
    allowance input

  traceProperties : I.Predicates D.traceFields
  traceProperties zero value = ⊤
  traceProperties (suc zero) value = value ≤ P.u64Maximum
  traceProperties (suc (suc zero)) value = Bounds.Optional (_≤ P.u64Maximum) value
  traceProperties (suc (suc (suc zero))) value = ⊤
  traceProperties (suc (suc (suc (suc zero)))) value = ⊤
  traceProperties (suc (suc (suc (suc (suc zero))))) value = ⊤
  traceProperties (suc (suc (suc (suc (suc (suc zero)))))) value = value ≤ sizeMaximum
  traceProperties (suc (suc (suc (suc (suc (suc (suc zero))))))) value = value ≤ sizeMaximum
  traceProperties (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) value = All B.EventBounds value
  traceProperties (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) value = value ≤ sizeMaximum
  traceProperties (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc ()))))))))))

  traceDefaults : I.Defaults D.traceFields traceProperties
  traceDefaults (suc (suc zero)) value refl = tt
  traceDefaults (suc (suc (suc (suc zero)))) value refl = tt
  traceDefaults (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) value refl = z≤n
  traceDefaults (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc ())))))))))) value observed

  traceReaders : ∀ allowance index input → S.Ensures (traceProperties index)
    (Flow.Productive.result (Slots.readerAt D.traceFields index (R.traceReaders allowance) input))
  traceReaders allowance zero input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.traceFields zero (R.traceReaders allowance)
      input))
  traceReaders allowance (suc zero) input = Inv.uint P.u64Maximum input
  traceReaders allowance (suc (suc zero)) input = Inv.optional R.u64 (_≤ P.u64Maximum) (Inv.uint P.u64Maximum) input
  traceReaders allowance (suc (suc (suc zero))) input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.traceFields (suc (suc (suc zero)))
      (R.traceReaders allowance) input))
  traceReaders allowance (suc (suc (suc (suc zero)))) input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.traceFields (suc (suc (suc (suc zero))))
      (R.traceReaders allowance) input))
  traceReaders allowance (suc (suc (suc (suc (suc zero))))) input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.traceFields (suc (suc (suc (suc (suc zero)))))
      (R.traceReaders allowance) input))
  traceReaders allowance (suc (suc (suc (suc (suc (suc zero)))))) input = Inv.uint sizeMaximum input
  traceReaders allowance (suc (suc (suc (suc (suc (suc (suc zero))))))) input = Inv.uint sizeMaximum input
  traceReaders allowance (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) input = Inv.vector R.event B.EventBounds event allowance input
  traceReaders allowance (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) input = Inv.uint sizeMaximum input
  traceReaders allowance (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc ())))))))))) input

  traceBuild : ∀ values → I.Valid D.traceFields traceProperties values →
    B.TraceBounds (D.buildTrace (Slots.toSequence D.traceFields values))
  traceBuild values valid = record
    { started = valid (suc zero)
    ; finished = valid (suc (suc zero))
    ; model = valid (suc (suc (suc (suc (suc (suc zero))))))
    ; tool = valid (suc (suc (suc (suc (suc (suc (suc zero)))))))
    ; events =
        valid (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
    ; omitted =
        valid (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
    }

  trace : ∀ allowance input → S.Ensures B.TraceBounds (Flow.Productive.result (R.trace allowance input))
  trace allowance input = Inv.recordValue D.traceFields D.buildTrace R.traceReaders
    traceProperties B.TraceBounds traceReaders traceDefaults traceBuild
    allowance input

  diagnosticsProperties : I.Predicates D.diagnosticsFields
  diagnosticsProperties zero value = All B.TraceBounds value
  diagnosticsProperties (suc ())

  diagnosticsDefaults : I.Defaults D.diagnosticsFields diagnosticsProperties
  diagnosticsDefaults zero value refl = []
  diagnosticsDefaults (suc ()) value observed

  diagnosticsReaders : ∀ allowance index input → S.Ensures (diagnosticsProperties index)
    (Flow.Productive.result (Slots.readerAt D.diagnosticsFields index (R.diagnosticsReaders allowance) input))
  diagnosticsReaders allowance zero input = Inv.vector R.trace B.TraceBounds trace allowance input
  diagnosticsReaders allowance (suc ()) input

  diagnosticsBuild : ∀ values → I.Valid D.diagnosticsFields diagnosticsProperties values →
    B.DiagnosticsBounds (D.buildDiagnostics (Slots.toSequence D.diagnosticsFields values))
  diagnosticsBuild values valid = valid zero

  diagnostics : ∀ allowance input → S.Ensures B.DiagnosticsBounds (Flow.Productive.result (R.diagnostics allowance input))
  diagnostics allowance input = Inv.recordValue D.diagnosticsFields D.buildDiagnostics
    R.diagnosticsReaders diagnosticsProperties B.DiagnosticsBounds
    diagnosticsReaders diagnosticsDefaults diagnosticsBuild allowance
    input
