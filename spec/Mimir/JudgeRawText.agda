{-# OPTIONS --safe #-}
-- Unicode-scalar validity for every textual field of persisted judge records.
import Mimir.FloatConversion
module Mimir.JudgeRawText (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Fin using (zero; suc)
open import Data.Nat using (ℕ)
open import Data.List.Relation.Unary.All using (All; [])
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (refl)
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
import Mimir.JudgeStateText as T
import Mimir.UnicodeText as U
import Mimir.SignedMachine as Machine

module Parser (checks : Machine.OverflowChecks) (sizeMaximum : ℕ) where
  private
    module R = Raw.Parser checks sizeMaximum
    module D = R.D
    module Inv = Invariant.Parser checks sizeMaximum

  sourceProperties : I.Predicates D.sourceFields
  sourceProperties zero value = U.Valid value
  sourceProperties (suc zero) value = U.Valid value
  sourceProperties (suc (suc zero)) value = ⊤
  sourceProperties (suc (suc (suc zero))) value = ⊤
  sourceProperties (suc (suc (suc (suc zero)))) value = U.Valid value
  sourceProperties (suc (suc (suc (suc (suc ())))))

  sourceDefaults : I.Defaults D.sourceFields sourceProperties
  sourceDefaults (suc (suc (suc (suc (suc ()))))) value observed

  sourceReaders : ∀ allowance index input → S.Ensures (sourceProperties index)
    (Flow.Productive.result (Slots.readerAt D.sourceFields index (R.sourceReaders allowance) input))
  sourceReaders allowance zero input = Inv.text input
  sourceReaders allowance (suc zero) input = Inv.text input
  sourceReaders allowance (suc (suc zero)) input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.sourceFields (suc (suc zero))
      (R.sourceReaders allowance) input))
  sourceReaders allowance (suc (suc (suc zero))) input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.sourceFields (suc (suc (suc zero)))
      (R.sourceReaders allowance) input))
  sourceReaders allowance (suc (suc (suc (suc zero)))) input = Inv.text input
  sourceReaders allowance (suc (suc (suc (suc (suc ()))))) input

  sourceBuild : ∀ values → I.Valid D.sourceFields sourceProperties values →
    T.SourceText (D.buildSource (Slots.toSequence D.sourceFields values))
  sourceBuild values valid = record
    { stage = valid zero
    ; detail = valid (suc zero)
    ; excerpt = valid (suc (suc (suc (suc zero))))
    }

  source : ∀ allowance input → S.Ensures T.SourceText (Flow.Productive.result (R.source allowance input))
  source allowance input = Inv.recordValue D.sourceFields D.buildSource R.sourceReaders
    sourceProperties T.SourceText sourceReaders sourceDefaults
    sourceBuild allowance input

  diagnosticProperties : I.Predicates D.diagnosticFields
  diagnosticProperties zero value = ⊤
  diagnosticProperties (suc zero) value = ⊤
  diagnosticProperties (suc (suc zero)) value = U.Valid value
  diagnosticProperties (suc (suc (suc zero))) value = U.Valid value
  diagnosticProperties (suc (suc (suc (suc ()))))

  diagnosticDefaults : I.Defaults D.diagnosticFields diagnosticProperties
  diagnosticDefaults zero value refl = tt
  diagnosticDefaults (suc (suc (suc (suc ())))) value observed

  diagnosticReaders : ∀ allowance index input → S.Ensures (diagnosticProperties index)
    (Flow.Productive.result (Slots.readerAt D.diagnosticFields index (R.diagnosticReaders allowance) input))
  diagnosticReaders allowance zero input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.diagnosticFields zero
      (R.diagnosticReaders allowance) input))
  diagnosticReaders allowance (suc zero) input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.diagnosticFields (suc zero)
      (R.diagnosticReaders allowance) input))
  diagnosticReaders allowance (suc (suc zero)) input = Inv.text input
  diagnosticReaders allowance (suc (suc (suc zero))) input = Inv.text input
  diagnosticReaders allowance (suc (suc (suc (suc ())))) input

  diagnosticBuild : ∀ values → I.Valid D.diagnosticFields diagnosticProperties values →
    T.DiagnosticText (D.buildDiagnostic (Slots.toSequence D.diagnosticFields values))
  diagnosticBuild values valid = record
    { tool = valid (suc (suc zero))
    ; detail = valid (suc (suc (suc zero)))
    }

  diagnostic : ∀ allowance input → S.Ensures T.DiagnosticText (Flow.Productive.result (R.diagnostic allowance input))
  diagnostic allowance input = Inv.recordValue D.diagnosticFields D.buildDiagnostic
    R.diagnosticReaders diagnosticProperties T.DiagnosticText
    diagnosticReaders diagnosticDefaults diagnosticBuild allowance
    input

  reportProperties : I.Predicates D.reportFields
  reportProperties zero value = U.Valid value
  reportProperties (suc zero) value = Bounds.Optional U.Valid value
  reportProperties (suc (suc zero)) value = Bounds.Optional T.DiagnosticText value
  reportProperties (suc (suc (suc zero))) value = Bounds.Optional U.Valid value
  reportProperties (suc (suc (suc (suc zero)))) value = Bounds.Optional T.SourceText value
  reportProperties (suc (suc (suc (suc (suc zero))))) value = ⊤
  reportProperties (suc (suc (suc (suc (suc (suc zero)))))) value = ⊤
  reportProperties (suc (suc (suc (suc (suc (suc (suc zero))))))) value = ⊤
  reportProperties (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) value = ⊤
  reportProperties (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) value = ⊤
  reportProperties (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) value = ⊤
  reportProperties (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) value = ⊤
  reportProperties (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) value = ⊤
  reportProperties (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))) value = U.Valid value
  reportProperties (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))) value = ⊤
  reportProperties (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc ())))))))))))))))

  reportDefaults : I.Defaults D.reportFields reportProperties
  reportDefaults (suc zero) value refl = tt
  reportDefaults (suc (suc zero)) value refl = tt
  reportDefaults (suc (suc (suc zero))) value refl = tt
  reportDefaults (suc (suc (suc (suc zero)))) value refl = tt
  reportDefaults (suc (suc (suc (suc (suc zero))))) value refl = tt
  reportDefaults (suc (suc (suc (suc (suc (suc zero)))))) value refl = tt
  reportDefaults (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) value refl = tt
  reportDefaults (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))) value refl = []
  reportDefaults (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc ()))))))))))))))) value observed

  reportReaders : ∀ allowance index input → S.Ensures (reportProperties index)
    (Flow.Productive.result (Slots.readerAt D.reportFields index (R.reportReaders allowance) input))
  reportReaders allowance zero input = Inv.text input
  reportReaders allowance (suc zero) input = Inv.optional R.A.readText U.Valid Inv.text input
  reportReaders allowance (suc (suc zero)) input = Inv.optional (R.diagnostic allowance) T.DiagnosticText
    (diagnostic allowance) input
  reportReaders allowance (suc (suc (suc zero))) input = Inv.optional R.A.readText U.Valid Inv.text input
  reportReaders allowance (suc (suc (suc (suc zero)))) input = Inv.optional (R.source allowance) T.SourceText (source allowance)
    input
  reportReaders allowance (suc (suc (suc (suc (suc zero))))) input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.reportFields (suc (suc (suc (suc (suc zero)))))
      (R.reportReaders allowance) input))
  reportReaders allowance (suc (suc (suc (suc (suc (suc zero)))))) input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.reportFields
      (suc (suc (suc (suc (suc (suc zero))))))
      (R.reportReaders allowance) input))
  reportReaders allowance (suc (suc (suc (suc (suc (suc (suc zero))))))) input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.reportFields
      (suc (suc (suc (suc (suc (suc (suc zero)))))))
      (R.reportReaders allowance) input))
  reportReaders allowance (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.reportFields
      (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
      (R.reportReaders allowance) input))
  reportReaders allowance (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.reportFields
      (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
      (R.reportReaders allowance) input))
  reportReaders allowance (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))) input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.reportFields
      (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))
      (R.reportReaders allowance) input))
  reportReaders allowance (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))) input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.reportFields
      (suc
       (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))
      (R.reportReaders allowance) input))
  reportReaders allowance (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))) input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.reportFields
      (suc
       (suc
        (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))
      (R.reportReaders allowance) input))
  reportReaders allowance (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))) input = Inv.text input
  reportReaders allowance (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))) input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.reportFields
      (suc
       (suc
        (suc
         (suc
          (suc
           (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))))))))
      (R.reportReaders allowance) input))
  reportReaders allowance (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc ()))))))))))))))) input

  reportBuild : ∀ values → I.Valid D.reportFields reportProperties values →
    T.ReportText (D.buildReport (Slots.toSequence D.reportFields values))
  reportBuild values valid = record
    { status = valid zero
    ; reason = valid (suc zero)
    ; diagnostic = valid (suc (suc zero))
    ; detail = valid (suc (suc (suc zero)))
    ; source = valid (suc (suc (suc (suc zero))))
    ; notification =
        valid
        (suc
         (suc
          (suc
           (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))
    }

  report : ∀ allowance input → S.Ensures T.ReportText (Flow.Productive.result (R.report allowance input))
  report allowance input = Inv.recordValue D.reportFields D.buildReport R.reportReaders
    reportProperties T.ReportText reportReaders reportDefaults
    reportBuild allowance input

  incidentProperties : I.Predicates D.incidentFields
  incidentProperties zero value = T.ReportText value
  incidentProperties (suc zero) value = Bounds.Optional T.ReportText value
  incidentProperties (suc (suc zero)) value = ⊤
  incidentProperties (suc (suc (suc zero))) value = ⊤
  incidentProperties (suc (suc (suc (suc ()))))

  incidentDefaults : I.Defaults D.incidentFields incidentProperties
  incidentDefaults (suc zero) value refl = tt
  incidentDefaults (suc (suc zero)) value refl = tt
  incidentDefaults (suc (suc (suc zero))) value refl = tt
  incidentDefaults (suc (suc (suc (suc ())))) value observed

  incidentReaders : ∀ allowance index input → S.Ensures (incidentProperties index)
    (Flow.Productive.result (Slots.readerAt D.incidentFields index (R.incidentReaders allowance) input))
  incidentReaders allowance zero input = report allowance input
  incidentReaders allowance (suc zero) input = Inv.optional (R.report allowance) T.ReportText (report allowance)
    input
  incidentReaders allowance (suc (suc zero)) input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.incidentFields (suc (suc zero))
      (R.incidentReaders allowance) input))
  incidentReaders allowance (suc (suc (suc zero))) input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.incidentFields (suc (suc (suc zero)))
      (R.incidentReaders allowance) input))
  incidentReaders allowance (suc (suc (suc (suc ())))) input

  incidentBuild : ∀ values → I.Valid D.incidentFields incidentProperties values →
    T.IncidentText (D.buildIncident (Slots.toSequence D.incidentFields values))
  incidentBuild values valid = record { first = valid zero ; latest = valid (suc zero) }

  incident : ∀ allowance input → S.Ensures T.IncidentText (Flow.Productive.result (R.incident allowance input))
  incident allowance input = Inv.recordValue D.incidentFields D.buildIncident R.incidentReaders
    incidentProperties T.IncidentText incidentReaders incidentDefaults
    incidentBuild allowance input

  eventProperties : I.Predicates D.eventFields
  eventProperties zero value = ⊤
  eventProperties (suc zero) value = ⊤
  eventProperties (suc (suc zero)) value = U.Valid value
  eventProperties (suc (suc (suc zero))) value = ⊤
  eventProperties (suc (suc (suc (suc zero)))) value = ⊤
  eventProperties (suc (suc (suc (suc (suc zero))))) value = Bounds.Optional U.Valid value
  eventProperties (suc (suc (suc (suc (suc (suc zero)))))) value = Bounds.Optional U.Valid value
  eventProperties (suc (suc (suc (suc (suc (suc (suc zero))))))) value = ⊤
  eventProperties (suc (suc (suc (suc (suc (suc (suc (suc ()))))))))

  eventDefaults : I.Defaults D.eventFields eventProperties
  eventDefaults (suc (suc (suc (suc (suc zero))))) value refl = tt
  eventDefaults (suc (suc (suc (suc zero)))) value refl = tt
  eventDefaults (suc (suc (suc zero))) value refl = tt
  eventDefaults (suc (suc (suc (suc (suc (suc zero)))))) value refl = tt
  eventDefaults (suc (suc (suc (suc (suc (suc (suc zero))))))) value refl = tt
  eventDefaults (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) value observed

  eventReaders : ∀ allowance index input → S.Ensures (eventProperties index)
    (Flow.Productive.result (Slots.readerAt D.eventFields index (R.eventReaders allowance) input))
  eventReaders allowance zero input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.eventFields zero (R.eventReaders allowance)
      input))
  eventReaders allowance (suc zero) input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.eventFields (suc zero) (R.eventReaders allowance)
      input))
  eventReaders allowance (suc (suc zero)) input = Inv.text input
  eventReaders allowance (suc (suc (suc zero))) input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.eventFields (suc (suc (suc zero)))
      (R.eventReaders allowance) input))
  eventReaders allowance (suc (suc (suc (suc zero)))) input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.eventFields (suc (suc (suc (suc zero))))
      (R.eventReaders allowance) input))
  eventReaders allowance (suc (suc (suc (suc (suc zero))))) input = Inv.optional R.A.readText U.Valid Inv.text input
  eventReaders allowance (suc (suc (suc (suc (suc (suc zero)))))) input = Inv.optional R.A.readText U.Valid Inv.text input
  eventReaders allowance (suc (suc (suc (suc (suc (suc (suc zero))))))) input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.eventFields
      (suc (suc (suc (suc (suc (suc (suc zero)))))))
      (R.eventReaders allowance) input))
  eventReaders allowance (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) input

  eventBuild : ∀ values → I.Valid D.eventFields eventProperties values →
    T.EventText (D.buildEvent (Slots.toSequence D.eventFields values))
  eventBuild values valid = record
    { kind = valid (suc (suc zero))
    ; tool = valid (suc (suc (suc (suc (suc zero)))))
    ; detail = valid (suc (suc (suc (suc (suc (suc zero))))))
    }

  event : ∀ allowance input → S.Ensures T.EventText (Flow.Productive.result (R.event allowance input))
  event allowance input = Inv.recordValue D.eventFields D.buildEvent R.eventReaders
    eventProperties T.EventText eventReaders eventDefaults eventBuild
    allowance input

  traceProperties : I.Predicates D.traceFields
  traceProperties zero value = ⊤
  traceProperties (suc zero) value = ⊤
  traceProperties (suc (suc zero)) value = ⊤
  traceProperties (suc (suc (suc zero))) value = U.Valid value
  traceProperties (suc (suc (suc (suc zero)))) value = Bounds.Optional U.Valid value
  traceProperties (suc (suc (suc (suc (suc zero))))) value = ⊤
  traceProperties (suc (suc (suc (suc (suc (suc zero)))))) value = ⊤
  traceProperties (suc (suc (suc (suc (suc (suc (suc zero))))))) value = ⊤
  traceProperties (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) value = All T.EventText value
  traceProperties (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) value = ⊤
  traceProperties (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc ()))))))))))

  traceDefaults : I.Defaults D.traceFields traceProperties
  traceDefaults (suc (suc zero)) value refl = tt
  traceDefaults (suc (suc (suc (suc (suc (suc (suc zero))))))) value refl = tt
  traceDefaults (suc (suc (suc (suc (suc (suc zero)))))) value refl = tt
  traceDefaults (suc (suc (suc (suc zero)))) value refl = tt
  traceDefaults (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) value refl = tt
  traceDefaults (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc ())))))))))) value observed

  traceReaders : ∀ allowance index input → S.Ensures (traceProperties index)
    (Flow.Productive.result (Slots.readerAt D.traceFields index (R.traceReaders allowance) input))
  traceReaders allowance zero input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.traceFields zero (R.traceReaders allowance)
      input))
  traceReaders allowance (suc zero) input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.traceFields (suc zero) (R.traceReaders allowance)
      input))
  traceReaders allowance (suc (suc zero)) input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.traceFields (suc (suc zero))
      (R.traceReaders allowance) input))
  traceReaders allowance (suc (suc (suc zero))) input = Inv.text input
  traceReaders allowance (suc (suc (suc (suc zero)))) input = Inv.optional R.A.readText U.Valid Inv.text input
  traceReaders allowance (suc (suc (suc (suc (suc zero))))) input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.traceFields (suc (suc (suc (suc (suc zero)))))
      (R.traceReaders allowance) input))
  traceReaders allowance (suc (suc (suc (suc (suc (suc zero)))))) input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.traceFields
      (suc (suc (suc (suc (suc (suc zero)))))) (R.traceReaders allowance)
      input))
  traceReaders allowance (suc (suc (suc (suc (suc (suc (suc zero))))))) input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.traceFields
      (suc (suc (suc (suc (suc (suc (suc zero)))))))
      (R.traceReaders allowance) input))
  traceReaders allowance (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) input = Inv.vector R.event T.EventText event allowance input
  traceReaders allowance (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) input = S.trivial
    (Flow.Productive.result
     (Slots.readerAt D.traceFields
      (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))
      (R.traceReaders allowance) input))
  traceReaders allowance (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc ())))))))))) input

  traceBuild : ∀ values → I.Valid D.traceFields traceProperties values →
    T.TraceText (D.buildTrace (Slots.toSequence D.traceFields values))
  traceBuild values valid = record
    { status = valid (suc (suc (suc zero)))
    ; reason = valid (suc (suc (suc (suc zero))))
    ; events =
        valid (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
    }

  trace : ∀ allowance input → S.Ensures T.TraceText (Flow.Productive.result (R.trace allowance input))
  trace allowance input = Inv.recordValue D.traceFields D.buildTrace R.traceReaders
    traceProperties T.TraceText traceReaders traceDefaults traceBuild
    allowance input

  diagnosticsProperties : I.Predicates D.diagnosticsFields
  diagnosticsProperties zero value = All T.TraceText value
  diagnosticsProperties (suc ())

  diagnosticsDefaults : I.Defaults D.diagnosticsFields diagnosticsProperties
  diagnosticsDefaults zero value refl = []
  diagnosticsDefaults (suc ()) value observed

  diagnosticsReaders : ∀ allowance index input → S.Ensures (diagnosticsProperties index)
    (Flow.Productive.result (Slots.readerAt D.diagnosticsFields index (R.diagnosticsReaders allowance) input))
  diagnosticsReaders allowance zero input = Inv.vector R.trace T.TraceText trace allowance input
  diagnosticsReaders allowance (suc ()) input

  diagnosticsBuild : ∀ values → I.Valid D.diagnosticsFields diagnosticsProperties values →
    T.DiagnosticsText (D.buildDiagnostics (Slots.toSequence D.diagnosticsFields values))
  diagnosticsBuild values valid = valid zero

  diagnostics : ∀ allowance input → S.Ensures T.DiagnosticsText (Flow.Productive.result (R.diagnostics allowance input))
  diagnostics allowance input = Inv.recordValue D.diagnosticsFields D.buildDiagnostics
    R.diagnosticsReaders diagnosticsProperties T.DiagnosticsText
    diagnosticsReaders diagnosticsDefaults diagnosticsBuild allowance
    input
