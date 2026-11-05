{-# OPTIONS --safe #-}
-- Reports restore nested failure evidence, omitted fields, empty-list defaults and counters.
import Mimir.FloatConversion
module Mimir.JudgeReportReadBack (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.List using ([]; _∷_; _++_; map; drop)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; _≤_; suc)
open import Data.Product using (_,_; proj₂)
open import Data.String using (toList)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary.Decidable.Core using (toWitness)
open import Function.Base using (_$_)
import Mimir.SignedMachine as Machine
import Mimir.JudgeStateRaw as RawDependency
private
  module Raw = RawDependency floatConversion
import Mimir.JudgeStateDecode as Decode
import Mimir.JudgeStateWire as Wire
import Mimir.JudgeStateSerialize as Serialize
import Mimir.JudgeStateBounds as Bounds
import Mimir.JudgeStateText as TextBounds
import Mimir.JudgeStatePrimitives as Primitive
import Mimir.JudgeDeferredReadBack as DeferredReadDependency
private
  module DeferredRead = DeferredReadDependency floatConversion
import Mimir.JudgeDiagnosticReadBack as DiagnosticReadDependency
private
  module DiagnosticRead = DiagnosticReadDependency floatConversion
import Mimir.JudgeSourceReadBack as SourceReadDependency
private
  module SourceRead = SourceReadDependency floatConversion
import Mimir.JudgeEventReadBack as EventReadDependency
private
  module EventRead = EventReadDependency floatConversion
import Mimir.JudgeTraceReadBack as TraceReadDependency
private
  module TraceRead = TraceReadDependency floatConversion
import Mimir.JudgeUUIDReadBack as UUIDReadDependency
private
  module UUIDRead = UUIDReadDependency floatConversion
import Mimir.JudgeUUIDVectorReadBack as UUIDVectorDependency
private
  module UUIDVector = UUIDVectorDependency floatConversion
import Mimir.JudgeTextReadBack as TextReadDependency
private
  module TextRead = TextReadDependency floatConversion
import Mimir.UUIDSchema as UUID
import Mimir.SerdeRecord as TypedRecordDependency
private
  module TypedRecord = TypedRecordDependency floatConversion
import Mimir.SerdeStruct as Struct
import Mimir.SerdeSlots as Slots
import Mimir.SerdeReadBack as Back
import Mimir.SerdeReadBackComposition as ComposeDependency
private
  module Compose = ComposeDependency floatConversion
import Mimir.SerdeRawEmission as EDependency
private
  module E = EDependency floatConversion
import Mimir.SerdeRawEmissionBuilders as BuildDependency
private
  module Build = BuildDependency floatConversion
import Mimir.SerdeOption as OptionDependency
private
  module Option = OptionDependency floatConversion
import Mimir.SerdeOptionCodecReadBack as OptionReadDependency
private
  module OptionRead = OptionReadDependency floatConversion
import Mimir.SerdeObjectVectorReadBack as VectorDependency
private
  module Vector = VectorDependency floatConversion
import Mimir.JsonObjectReadBack as Encoding
import Mimir.JsonObjects as Objects
import Mimir.JsonCompactRecords as Compact
import Mimir.JsonRecordSupport as Support
import Mimir.StructuredValue as JSON
import Mimir.JudgeReportReferenceReadBack as ReferenceDependency
private
  module Reference = ReferenceDependency floatConversion
module R = Wire.R

supported : ∀ value → TextBounds.ReportText value → All Compact.FieldSupported (Wire.reportFields value)
supported value valid = EventRead.objectFields (Serialize.report value valid)

module Parser (checks : Machine.OverflowChecks) (sizeMaximum : ℕ)
  (nativeWidth : sizeMaximum ≤ Primitive.u64Maximum) where
  private
    module D = Decode.Size sizeMaximum
    module B = Bounds.Size sizeMaximum
    module P = Raw.Parser checks sizeMaximum
    module Sources = SourceRead.Parser checks sizeMaximum nativeWidth
    module Diagnostics = DiagnosticRead.Parser checks sizeMaximum
    module Events = EventRead.Parser checks sizeMaximum nativeWidth
    module Traces = TraceRead.Parser checks sizeMaximum nativeWidth
    module Deferred = DeferredRead.Parser checks sizeMaximum
    module Array = Vector.Uniform R.Deferred Wire.deferred Serialize.deferred

  open Reference.Parser checks sizeMaximum nativeWidth public

  detailFields : R.Report → Wire.Fields
  detailFields value = Wire.optional (toList "failure_detail") JSON.string (R.Report.failureDetail value) ++ referenceFields value

  detailSupport : ∀ value → TextBounds.ReportText value → All Compact.FieldSupported (detailFields value)
  detailSupport value valid = ++⁺
    (Support.optional (toList "failure_detail") tt JSON.string (λ text valid → Compact.string valid)
      (R.Report.failureDetail value) (TextBounds.ReportText.detail valid))
    (referenceSupport value valid)

  opaque
    detailEmission : ∀ allowance value (valid : TextBounds.ReportText value) → B.ReportBounds value →
      E.Emits (drop 3 D.reportFields)
        (proj₂ (proj₂ (proj₂ (P.reportReaders (suc (suc allowance)))))) (proj₂ (proj₂ (proj₂ (values value))))
        (detailFields value) (detailSupport value valid)
    detailEmission allowance value valid bounded = Build.optional (toList "failure_detail") tt JSON.string
      JSON.asString (Option.read P.A.readText)
      (λ text valid → Compact.string valid) Events.optionalText
      (R.Report.failureDetail value) (TextBounds.ReportText.detail valid)
      (references allowance value valid bounded)

  diagnosticFields : R.Report → Wire.Fields
  diagnosticFields value = Wire.optional (toList "diagnostic") Wire.diagnostic (R.Report.diagnostic value) ++ detailFields value

  diagnosticSupport : ∀ value → TextBounds.ReportText value → All Compact.FieldSupported (diagnosticFields value)
  diagnosticSupport value valid = ++⁺
    (Support.optional (toList "diagnostic") tt Wire.diagnostic Serialize.diagnostic
      (R.Report.diagnostic value) (TextBounds.ReportText.diagnostic valid))
    (detailSupport value valid)

  opaque
    diagnosticEmission : ∀ allowance value (valid : TextBounds.ReportText value) → B.ReportBounds value →
      E.Emits (drop 2 D.reportFields)
        (proj₂ (proj₂ (P.reportReaders (suc (suc allowance))))) (proj₂ (proj₂ (values value)))
        (diagnosticFields value) (diagnosticSupport value valid)
    diagnosticEmission allowance value valid bounded = Build.optionalChecked
      {A = R.FailureDiagnostic} {writePredicate = TextBounds.DiagnosticText} {readPredicate = B.DiagnosticBounds}
      (toList "diagnostic") tt Wire.diagnostic
      D.diagnostic (Option.read (P.diagnostic (suc (suc allowance))))
      Serialize.diagnostic (optionalDiagnostic allowance)
      (R.Report.diagnostic value)
      (TextBounds.ReportText.diagnostic valid)
      (B.ReportBounds.diagnostic bounded)
      {fields = drop 3 D.reportFields}
      {readers = proj₂ (proj₂ (proj₂ (P.reportReaders (suc (suc allowance)))))}
      {values = proj₂ (proj₂ (proj₂ (values value)))}
      {input = detailFields value} {inputValid = detailSupport value valid}
      (detailEmission allowance value valid bounded)

  reasonFields : R.Report → Wire.Fields
  reasonFields value = Wire.optional (toList "block_reason") JSON.string (R.Report.blockReason value) ++ diagnosticFields value

  reasonSupport : ∀ value → TextBounds.ReportText value → All Compact.FieldSupported (reasonFields value)
  reasonSupport value valid = ++⁺
    (Support.optional (toList "block_reason") tt JSON.string (λ text valid → Compact.string valid)
      (R.Report.blockReason value) (TextBounds.ReportText.reason valid))
    (diagnosticSupport value valid)

  opaque
    reasonEmission : ∀ allowance value (valid : TextBounds.ReportText value) → B.ReportBounds value →
      E.Emits (drop 1 D.reportFields)
        (proj₂ (P.reportReaders (suc (suc allowance)))) (proj₂ (values value))
        (reasonFields value) (reasonSupport value valid)
    reasonEmission allowance value valid bounded = Build.optional (toList "block_reason") tt JSON.string JSON.asString
      (Option.read P.A.readText) (λ text valid → Compact.string valid)
      Events.optionalText (R.Report.blockReason value)
      (TextBounds.ReportText.reason valid)
      (diagnosticEmission allowance value valid bounded)

  opaque
    written : ∀ allowance value (valid : TextBounds.ReportText value) → B.ReportBounds value →
      E.Emits D.reportFields (P.reportReaders (suc (suc allowance))) (values value)
        (Wire.reportFields value) (supported value valid)
    written allowance value valid bounded = E.emitted
      (λ suffix delimiter → TextRead.Parser.roundTrip checks (R.Report.status value)
        (TextBounds.ReportText.status valid) suffix)
      (reasonEmission allowance value valid bounded)

  opaque
    roundTrip : ∀ allowance value (valid : TextBounds.ReportText value) → B.ReportBounds value → ∀ suffix →
      Back.Returns (P.report (suc (suc (suc allowance))))
        (Compact.bytes (Wire.report value) (Serialize.report value valid) ++ suffix) value suffix
    roundTrip allowance value valid bounded suffix = Compose.mapProductive
      (λ parsed → D.buildReport (Slots.toSequence D.reportFields parsed))
      (TypedRecord.Parser.read checks D.reportFields P.reportReaders
       Raw.recordExpected (suc (suc (suc allowance)))
       (Compact.bytes (Wire.report value) (Serialize.report value valid)
        ++ suffix))
      (E.Parser.roundTrip checks D.reportFields P.reportReaders
       Raw.recordExpected (suc (suc allowance)) (values value)
       (Wire.reportFields value) (supported value valid)
       (toWitness
        {a? = Objects.Names.unique? (Struct.names D.reportFields)} tt)
       (written allowance value valid bounded) suffix)
