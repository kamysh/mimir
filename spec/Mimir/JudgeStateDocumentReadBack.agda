{-# OPTIONS --safe #-}
-- Every canonical persisted judge file is read back at the native depth allowance.
import Mimir.FloatConversion
module Mimir.JudgeStateDocumentReadBack (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.List using ([]; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.Nat using (ℕ; _≤_)
open import Relation.Binary.PropositionalEquality using (subst)
import Mimir.JudgePersistence as Names
import Mimir.JudgeStateDocument as DocumentDependency
private
  module Document = DocumentDependency floatConversion
import Mimir.JudgeStateWire as Wire
import Mimir.JudgeStateSerialize as Serialize
import Mimir.JudgeStateBounds as Bounds
import Mimir.JudgeStateText as TextBounds
import Mimir.JudgeStatePrimitives as Primitive
import Mimir.JudgeReportReadBack as ReportDependency
private
  module Report = ReportDependency floatConversion
import Mimir.JudgeIncidentReadBack as IncidentDependency
private
  module Incident = IncidentDependency floatConversion
import Mimir.JudgeDiagnosticsReadBack as DiagnosticsDependency
private
  module Diagnostics = DiagnosticsDependency floatConversion
import Mimir.SerdeReadBack as Back
import Mimir.SerdeDocumentReadBack as CompleteDependency
private
  module Complete = CompleteDependency floatConversion
import Mimir.JsonCompactRecords as Compact
import Mimir.StructuredValue as JSON
import Mimir.SignedMachine as Machine

Valid : (name : Names.Name) → Document.Value name → Set
Valid Names.status = TextBounds.ReportText
Valid Names.failure = TextBounds.IncidentText
Valid Names.diagnostics = TextBounds.DiagnosticsText

encode : (name : Names.Name) → Document.Value name → JSON.Value
encode Names.status = Wire.report
encode Names.failure = Wire.incident
encode Names.diagnostics = Wire.diagnostics

supported : ∀ name value → Valid name value → Compact.Supported (encode name value)
supported Names.status = Serialize.report
supported Names.failure = Serialize.incident
supported Names.diagnostics = Serialize.diagnostics

module Parser (checks : Machine.OverflowChecks) (sizeMaximum : ℕ)
  (nativeWidth : sizeMaximum ≤ Primitive.u64Maximum) where
  private
    module B = Bounds.Size sizeMaximum
    module D = Document.Parser checks sizeMaximum
    module Reports = Report.Parser checks sizeMaximum nativeWidth
    module Incidents = Incident.Parser checks sizeMaximum nativeWidth
    module DiagnosticFiles = Diagnostics.Parser checks sizeMaximum nativeWidth

  Bounded : (name : Names.Name) → Document.Value name → Set
  Bounded Names.status = B.ReportBounds
  Bounded Names.failure = B.IncidentBounds
  Bounded Names.diagnostics = B.DiagnosticsBounds

  recordReadBack : ∀ name value (valid : Valid name value) → Bounded name value → ∀ suffix →
    Back.Returns (D.recordReader name 127)
      (Compact.bytes (encode name value) (supported name value valid) ++ suffix) value suffix
  recordReadBack Names.status value valid bounded suffix = Reports.roundTrip 124 value valid bounded suffix
  recordReadBack Names.failure value valid bounded suffix = Incidents.roundTrip 123 value valid bounded suffix
  recordReadBack Names.diagnostics value valid bounded suffix = DiagnosticFiles.roundTrip 122 value valid bounded suffix

  roundTrip : ∀ name value (valid : Valid name value) → Bounded name value →
    Back.Returns (D.read name) (Compact.bytes (encode name value) (supported name value valid)) value []
  roundTrip name value valid bounded = Complete.Parser.exhausted checks (D.recordReader name 127)
    (Compact.bytes (encode name value) (supported name value valid))
    value
    (subst
     (λ input → Back.Returns (D.recordReader name 127) input value [])
     (++-identityʳ
      (Compact.bytes (encode name value) (supported name value valid)))
     (recordReadBack name value valid bounded []))
