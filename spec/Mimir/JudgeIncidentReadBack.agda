{-# OPTIONS --safe #-}
-- Incident records retain first/latest reports, confirmation history and recovery time.
import Mimir.FloatConversion
module Mimir.JudgeIncidentReadBack (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.List using (_++_; map)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; _≤_; suc)
open import Data.Product using (_,_)
open import Data.String using (toList)
open import Data.Unit using (tt)
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
import Mimir.JudgeConfirmedReadBack as ConfirmedReadDependency
private
  module ConfirmedRead = ConfirmedReadDependency floatConversion
import Mimir.JudgeReportReadBack as ReportReadDependency
private
  module ReportRead = ReportReadDependency floatConversion
import Mimir.JudgeEventReadBack as EventReadDependency
private
  module EventRead = EventReadDependency floatConversion
import Mimir.JudgeTraceReadBack as TraceReadDependency
private
  module TraceRead = TraceReadDependency floatConversion
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
module R = Wire.R

supported : ∀ value → TextBounds.IncidentText value → All Compact.FieldSupported (Wire.incidentFields value)
supported value valid = EventRead.objectFields (Serialize.incident value valid)

module Parser (checks : Machine.OverflowChecks) (sizeMaximum : ℕ)
  (nativeWidth : sizeMaximum ≤ Primitive.u64Maximum) where
  private
    module D = Decode.Size sizeMaximum
    module B = Bounds.Size sizeMaximum
    module P = Raw.Parser checks sizeMaximum
    module Reports = ReportRead.Parser checks sizeMaximum nativeWidth
    module Traces = TraceRead.Parser checks sizeMaximum nativeWidth
    module Confirmed = ConfirmedRead.Parser checks sizeMaximum
    module Array = Vector.Uniform R.Confirmed Wire.confirmed Serialize.confirmed

  values : R.Incident → Slots.Values D.incidentFields
  values value = R.Incident.first value , R.Incident.latest value ,
    R.Incident.confirmedReviews value , R.Incident.recoveredAt value , tt

  optionalReport : ∀ allowance value (valid : TextBounds.ReportText value) → B.ReportBounds value →
    ∀ suffix → Encoding.Delimited suffix →
    Back.Returns (Option.read (P.report (suc (suc (suc allowance)))))
      (Compact.bytes (Wire.report value) (Serialize.report value valid) ++ suffix) (just value) suffix
  optionalReport allowance value valid bounded suffix delimiter = OptionRead.object (P.report (suc (suc (suc allowance))))
    (Wire.reportFields value) (ReportRead.supported value valid) value
    suffix (Reports.roundTrip allowance value valid bounded suffix)

  confirmedVector : ∀ allowance values → All B.ConfirmedBounds values → ∀ suffix →
    Back.Returns (P.vector P.confirmed (suc (suc (suc allowance))))
      (Compact.bytes (JSON.array (map Wire.confirmed values))
        (Compact.array (Support.arrayUniform Wire.confirmed Serialize.confirmed values)) ++ suffix) values suffix
  confirmedVector allowance values bounded suffix = Array.Parser.roundTrip checks P.confirmed Raw.arrayExpected
    (suc (suc allowance)) B.ConfirmedBounds
    (λ value →
       Vector.leading (ConfirmedRead.pairs value)
       (ConfirmedRead.supported value))
    (Confirmed.roundTrip (suc allowance)) values bounded suffix

  written : ∀ allowance value (valid : TextBounds.IncidentText value) → B.IncidentBounds value →
    E.Emits D.incidentFields (P.incidentReaders (suc (suc (suc allowance)))) (values value)
      (Wire.incidentFields value) (supported value valid)
  written allowance value valid bounded = E.emitted
    (λ suffix delimiter →
       Reports.roundTrip allowance (R.Incident.first value)
       (TextBounds.IncidentText.first valid)
       (B.IncidentBounds.first bounded) suffix)
    $
    Build.optionalChecked (toList "latest") tt Wire.report D.report
    (Option.read (P.report (suc (suc (suc allowance)))))
    Serialize.report (optionalReport allowance)
    (R.Incident.latest value) (TextBounds.IncidentText.latest valid)
    (B.IncidentBounds.latest bounded)
    $
    Build.nonempty (toList "confirmed_reviews") tt Wire.confirmed
    D.confirmed (P.vector P.confirmed (suc (suc (suc allowance))))
    Serialize.confirmed
    (λ values₁ accepted suffix delimiter →
       confirmedVector allowance values₁ accepted suffix)
    (R.Incident.confirmedReviews value)
    (B.IncidentBounds.confirmed bounded)
    $
    Build.optionalBoundedLast (toList "recovered_at") tt JSON.unsigned
    D.u64 (Option.read P.u64) Compact.unsigned Traces.optionalTimestamp
    (R.Incident.recoveredAt value) (B.IncidentBounds.recovered bounded)

  roundTrip : ∀ allowance value (valid : TextBounds.IncidentText value) → B.IncidentBounds value → ∀ suffix →
    Back.Returns (P.incident (suc (suc (suc (suc allowance)))))
      (Compact.bytes (Wire.incident value) (Serialize.incident value valid) ++ suffix) value suffix
  roundTrip allowance value valid bounded suffix = Compose.mapProductive
    (λ parsed →
       D.buildIncident (Slots.toSequence D.incidentFields parsed))
    (TypedRecord.Parser.read checks D.incidentFields P.incidentReaders
     Raw.recordExpected (suc (suc (suc (suc allowance))))
     (Compact.bytes (Wire.incident value)
      (Serialize.incident value valid)
      ++ suffix))
    (E.Parser.roundTrip checks D.incidentFields P.incidentReaders
     Raw.recordExpected (suc (suc (suc allowance))) (values value)
     (Wire.incidentFields value) (supported value valid)
     (toWitness
      {a? = Objects.Names.unique? (Struct.names D.incidentFields)} tt)
     (written allowance value valid bounded) suffix)
