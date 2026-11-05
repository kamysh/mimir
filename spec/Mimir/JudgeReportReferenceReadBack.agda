{-# OPTIONS --safe #-}
-- Reference and counter portions of the report read-back proof. Split from
-- JudgeReportReadBack to keep elaboration within the agreed 2 GiB heap cap.
import Mimir.FloatConversion
module Mimir.JudgeReportReferenceReadBack (floatConversion : Mimir.FloatConversion.Contract) where

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

  values : R.Report → Slots.Values D.reportFields
  values value = R.Report.status value , R.Report.blockReason value , R.Report.diagnostic value ,
    R.Report.failureDetail value , R.Report.failureSource value , R.Report.diagnosticsId value ,
    R.Report.selectedIds value , R.Report.selected value , R.Report.confirmed value ,
    R.Report.corrected value , R.Report.pending value , R.Report.unavailable value ,
    R.Report.deferredReviews value , R.Report.notification value , R.Report.recordedAt value , tt

  opaque
    optionalDiagnostic : ∀ allowance value (valid : TextBounds.DiagnosticText value) → B.DiagnosticBounds value →
      ∀ suffix → Encoding.Delimited suffix →
      Back.Returns (Option.read (P.diagnostic (suc (suc allowance))))
        (Compact.bytes (Wire.diagnostic value) (Serialize.diagnostic value valid) ++ suffix) (just value) suffix
    optionalDiagnostic allowance value valid bounded suffix delimiter = OptionRead.object (P.diagnostic (suc (suc allowance)))
      (DiagnosticRead.pairs value) (DiagnosticRead.supported value valid)
      value suffix
      (Diagnostics.roundTrip (suc allowance) value valid bounded suffix)

  opaque
    optionalSource : ∀ allowance value (valid : TextBounds.SourceText value) → B.SourceBounds value →
      ∀ suffix → Encoding.Delimited suffix →
      Back.Returns (Option.read (P.source (suc (suc allowance))))
        (Compact.bytes (Wire.source value) (Serialize.source value valid) ++ suffix) (just value) suffix
    optionalSource allowance value valid bounded suffix delimiter = OptionRead.object (P.source (suc (suc allowance)))
      (Wire.sourceFields value) (SourceRead.supported value valid) value
      suffix
      (Sources.roundTrip (suc allowance) value valid bounded suffix)

  opaque
    optionalUUID : ∀ value suffix → Encoding.Delimited suffix →
      Back.Returns (Option.read P.A.readUUID)
        (Compact.bytes (UUID.encode value) (Serialize.uuid value) ++ suffix) (just value) suffix
    optionalUUID value suffix delimiter = OptionRead.string P.A.readUUID (UUID.text value) (UUID.valid value)
      value suffix (UUIDRead.Parser.roundTrip checks value suffix)

  opaque
    deferredVector : ∀ allowance values → All B.DeferredBounds values → ∀ suffix →
      Back.Returns (P.vector P.deferred (suc (suc allowance)))
        (Compact.bytes (JSON.array (map Wire.deferred values))
          (Compact.array (Support.arrayUniform Wire.deferred Serialize.deferred values)) ++ suffix) values suffix
    deferredVector allowance values bounded suffix = Array.Parser.roundTrip checks P.deferred Raw.arrayExpected
      (suc allowance) B.DeferredBounds
      (λ value →
         Vector.leading (DeferredRead.pairs value)
         (DeferredRead.supported value))
      (Deferred.roundTrip allowance) values bounded suffix

  endingFields : R.Report → Wire.Fields
  endingFields value = Wire.nonempty (toList "deferred_reviews") Wire.deferred (R.Report.deferredReviews value) ++
    Wire.nonemptyText (toList "notification") (R.Report.notification value) ++
    Wire.member (toList "recorded_at") (JSON.unsigned (R.Report.recordedAt value))

  endingSupport : ∀ value → TextBounds.ReportText value → All Compact.FieldSupported (endingFields value)
  endingSupport value valid =
    ++⁺ (Support.nonemptyUniform (toList "deferred_reviews") tt Wire.deferred Serialize.deferred (R.Report.deferredReviews value)) $
    ++⁺ (Support.nonemptyText (toList "notification") tt (R.Report.notification value) (TextBounds.ReportText.notification valid)) $
    Serialize.member "recorded_at" tt (Compact.unsigned (R.Report.recordedAt value))

  opaque
    ending : ∀ allowance value (valid : TextBounds.ReportText value) → B.ReportBounds value →
      E.Emits (drop 12 D.reportFields)
        (P.vector P.deferred (suc (suc allowance)) , P.A.readText , P.u64 , tt)
        (R.Report.deferredReviews value , R.Report.notification value , R.Report.recordedAt value , tt)
        (endingFields value) (endingSupport value valid)
    ending allowance value valid bounded = Build.nonempty (toList "deferred_reviews") tt Wire.deferred
      D.deferred (P.vector P.deferred (suc (suc allowance)))
      Serialize.deferred
      (λ values₁ accepted suffix delimiter →
         deferredVector allowance values₁ accepted suffix)
      (R.Report.deferredReviews value) (B.ReportBounds.deferred bounded)
      $
      Build.nonemptyText (toList "notification") tt P.A.readText
      (λ text valid suffix delimiter →
         TextRead.Parser.roundTrip checks text valid suffix)
      (R.Report.notification value)
      (TextBounds.ReportText.notification valid)
      $
      E.emitted
      (Traces.timestamp (R.Report.recordedAt value)
       (B.ReportBounds.recorded bounded))
      E.done

  counterFields : R.Report → Wire.Fields
  counterFields value =
    (toList "selected" , JSON.unsigned (R.Report.selected value)) ∷
    (toList "confirmed" , JSON.unsigned (R.Report.confirmed value)) ∷
    (toList "corrected" , JSON.unsigned (R.Report.corrected value)) ∷
    (toList "pending" , JSON.unsigned (R.Report.pending value)) ∷
    (toList "unavailable" , JSON.unsigned (R.Report.unavailable value)) ∷ []

  counterSupport : ∀ value → All Compact.FieldSupported (counterFields value)
  counterSupport value =
    Serialize.entry "selected" tt (Compact.unsigned (R.Report.selected value)) All.∷
    Serialize.entry "confirmed" tt (Compact.unsigned (R.Report.confirmed value)) All.∷
    Serialize.entry "corrected" tt (Compact.unsigned (R.Report.corrected value)) All.∷
    Serialize.entry "pending" tt (Compact.unsigned (R.Report.pending value)) All.∷
    Serialize.entry "unavailable" tt (Compact.unsigned (R.Report.unavailable value)) All.∷ All.[]

  opaque
    counters : ∀ allowance value (valid : TextBounds.ReportText value) → B.ReportBounds value →
      E.Emits (drop 7 D.reportFields)
        (P.size , P.size , P.size , P.size , P.size ,
         P.vector P.deferred (suc (suc allowance)) , P.A.readText , P.u64 , tt)
        (R.Report.selected value , R.Report.confirmed value , R.Report.corrected value ,
         R.Report.pending value , R.Report.unavailable value , R.Report.deferredReviews value ,
         R.Report.notification value , R.Report.recordedAt value , tt)
        (counterFields value ++ endingFields value) (++⁺ (counterSupport value) (endingSupport value valid))
    counters allowance value valid bounded = E.emitted
      (Sources.size (R.Report.selected value)
       (B.ReportBounds.selected bounded))
      $
      E.emitted
      (Sources.size (R.Report.confirmed value)
       (B.ReportBounds.confirmed bounded))
      $
      E.emitted
      (Sources.size (R.Report.corrected value)
       (B.ReportBounds.corrected bounded))
      $
      E.emitted
      (Sources.size (R.Report.pending value)
       (B.ReportBounds.pending bounded))
      $
      E.emitted
      (Sources.size (R.Report.unavailable value)
       (B.ReportBounds.unavailable bounded))
      $ ending allowance value valid bounded

  referenceFields : R.Report → Wire.Fields
  referenceFields value =
    Wire.optional (toList "failure_source") Wire.source (R.Report.failureSource value) ++
    Wire.optional (toList "diagnostics_id") UUID.encode (R.Report.diagnosticsId value) ++
    Wire.nonempty (toList "selected_ids") UUID.encode (R.Report.selectedIds value) ++
    counterFields value ++ endingFields value

  referenceSupport : ∀ value → TextBounds.ReportText value → All Compact.FieldSupported (referenceFields value)
  referenceSupport value valid =
    ++⁺ (Support.optional (toList "failure_source") tt Wire.source Serialize.source
      (R.Report.failureSource value) (TextBounds.ReportText.source valid)) $
    ++⁺ (Support.optionalUniform (toList "diagnostics_id") tt UUID.encode Serialize.uuid
      (R.Report.diagnosticsId value)) $
    ++⁺ (Support.nonemptyUniform (toList "selected_ids") tt UUID.encode Serialize.uuid
      (R.Report.selectedIds value)) $
    ++⁺ (counterSupport value) (endingSupport value valid)

  opaque
    references : ∀ allowance value (valid : TextBounds.ReportText value) → B.ReportBounds value →
      E.Emits (drop 4 D.reportFields)
        (Option.read (P.source (suc (suc allowance))) , Option.read P.A.readUUID ,
         P.uuidVector (suc (suc allowance)) , P.size , P.size , P.size , P.size , P.size ,
         P.vector P.deferred (suc (suc allowance)) , P.A.readText , P.u64 , tt)
        (R.Report.failureSource value , R.Report.diagnosticsId value , R.Report.selectedIds value ,
         R.Report.selected value , R.Report.confirmed value , R.Report.corrected value ,
         R.Report.pending value , R.Report.unavailable value , R.Report.deferredReviews value ,
         R.Report.notification value , R.Report.recordedAt value , tt)
        (referenceFields value) (referenceSupport value valid)
    references allowance value valid bounded = Build.optionalChecked {writePredicate = TextBounds.SourceText}
      {readPredicate = B.SourceBounds} (toList "failure_source") tt
      Wire.source D.source (Option.read (P.source (suc (suc allowance))))
      Serialize.source (optionalSource allowance)
      (R.Report.failureSource value) (TextBounds.ReportText.source valid)
      (B.ReportBounds.source bounded) {fields = drop 5 D.reportFields}
      {readers =
       Option.read P.A.readUUID ,
       P.uuidVector (suc (suc allowance)) ,
       P.size ,
       P.size ,
       P.size ,
       P.size ,
       P.size ,
       P.vector P.deferred (suc (suc allowance)) ,
       P.A.readText , P.u64 , tt}
      {values =
       R.Report.diagnosticsId value ,
       R.Report.selectedIds value ,
       R.Report.selected value ,
       R.Report.confirmed value ,
       R.Report.corrected value ,
       R.Report.pending value ,
       R.Report.unavailable value ,
       R.Report.deferredReviews value ,
       R.Report.notification value , R.Report.recordedAt value , tt}
      {input =
       Wire.optional (toList "diagnostics_id") UUID.encode
       (R.Report.diagnosticsId value)
       ++
       Wire.nonempty (toList "selected_ids") UUID.encode
       (R.Report.selectedIds value)
       ++ counterFields value ++ endingFields value}
      {inputValid =
       ++⁺
       (Support.optionalUniform (toList "diagnostics_id") tt UUID.encode
        Serialize.uuid (R.Report.diagnosticsId value))
       (++⁺
        (Support.nonemptyUniform (toList "selected_ids") tt UUID.encode
         Serialize.uuid (R.Report.selectedIds value))
        (++⁺ (counterSupport value) (endingSupport value valid)))}
      (Build.optionalUniform (toList "diagnostics_id") tt UUID.encode
       Primitive.uuid (Option.read P.A.readUUID) Serialize.uuid
       optionalUUID (R.Report.diagnosticsId value)
       {fields = drop 6 D.reportFields}
       {readers =
        P.uuidVector (suc (suc allowance)) ,
        P.size ,
        P.size ,
        P.size ,
        P.size ,
        P.size ,
        P.vector P.deferred (suc (suc allowance)) ,
        P.A.readText , P.u64 , tt}
       {values =
        R.Report.selectedIds value ,
        R.Report.selected value ,
        R.Report.confirmed value ,
        R.Report.corrected value ,
        R.Report.pending value ,
        R.Report.unavailable value ,
        R.Report.deferredReviews value ,
        R.Report.notification value , R.Report.recordedAt value , tt}
       {input =
        Wire.nonempty (toList "selected_ids") UUID.encode
        (R.Report.selectedIds value)
        ++ counterFields value ++ endingFields value}
       {inputValid =
        ++⁺
        (Support.nonemptyUniform (toList "selected_ids") tt UUID.encode
         Serialize.uuid (R.Report.selectedIds value))
        (++⁺ (counterSupport value) (endingSupport value valid))}
       (Build.nonempty {predicate = λ _ → ⊤} (toList "selected_ids") tt
        UUID.encode Primitive.uuid (P.uuidVector (suc (suc allowance)))
        Serialize.uuid
        (λ ids accepted suffix delimiter →
           UUIDVector.Parser.roundTrip checks sizeMaximum (suc allowance) ids
           suffix)
        (R.Report.selectedIds value) tt {fields = drop 7 D.reportFields}
        {readers =
         P.size ,
         P.size ,
         P.size ,
         P.size ,
         P.size ,
         P.vector P.deferred (suc (suc allowance)) ,
         P.A.readText , P.u64 , tt}
        {rest =
         R.Report.selected value ,
         R.Report.confirmed value ,
         R.Report.corrected value ,
         R.Report.pending value ,
         R.Report.unavailable value ,
         R.Report.deferredReviews value ,
         R.Report.notification value , R.Report.recordedAt value , tt}
        {input = counterFields value ++ endingFields value}
        {inputValid =
         ++⁺ (counterSupport value) (endingSupport value valid)}
        (counters allowance value valid bounded)))

