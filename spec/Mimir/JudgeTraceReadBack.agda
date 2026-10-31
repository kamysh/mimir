{-# OPTIONS --safe #-}
-- Trace read-back preserves nested event arrays, counters and omitted optionals.
import Mimir.FloatConversion
module Mimir.JudgeTraceReadBack (floatConversion : Mimir.FloatConversion.Contract) where

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
import Mimir.JudgeDeferredReadBack as DelimitersDependency
private
  module Delimiters = DelimitersDependency floatConversion
import Mimir.JudgeSourceReadBack as SourceReadDependency
private
  module SourceRead = SourceReadDependency floatConversion
import Mimir.JudgeEventReadBack as EventReadDependency
private
  module EventRead = EventReadDependency floatConversion
import Mimir.JudgeUUIDReadBack as UUIDReadDependency
private
  module UUIDRead = UUIDReadDependency floatConversion
import Mimir.JudgeUUIDVectorReadBack as UUIDVectorDependency
private
  module UUIDVector = UUIDVectorDependency floatConversion
import Mimir.JudgeTextReadBack as TextReadDependency
private
  module TextRead = TextReadDependency floatConversion
import Mimir.JudgeUnsignedReadBack as UnsignedReadDependency
private
  module UnsignedRead = UnsignedReadDependency floatConversion
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
import Mimir.SerdeNumberStart as StartDependency
private
  module Start = StartDependency floatConversion
import Mimir.SerdeObjectVectorReadBack as VectorDependency
private
  module Vector = VectorDependency floatConversion
import Mimir.JsonObjectReadBack as Encoding
import Mimir.JsonObjects as Objects
import Mimir.JsonCompactRecords as Compact
import Mimir.JsonRecordSupport as Support
import Mimir.StructuredValue as JSON
module R = Wire.R

supported : ∀ value → TextBounds.TraceText value → All Compact.FieldSupported (Wire.traceFields value)
supported value valid = EventRead.objectFields (Serialize.trace value valid)

module Parser (checks : Machine.OverflowChecks) (sizeMaximum : ℕ)
  (nativeWidth : sizeMaximum ≤ Primitive.u64Maximum) where
  private
    module D = Decode.Size sizeMaximum
    module B = Bounds.Size sizeMaximum
    module P = Raw.Parser checks sizeMaximum
    module Sizes = SourceRead.Parser checks sizeMaximum nativeWidth
    module Events = EventRead.Parser checks sizeMaximum nativeWidth
    module Array = Vector.Encoding R.Event TextBounds.EventText Wire.eventFields EventRead.supported

  values : R.Trace → Slots.Values D.traceFields
  values value = R.Trace.identity value , R.Trace.startedAt value , R.Trace.finishedAt value ,
    R.Trace.status value , R.Trace.blockReason value , R.Trace.selectedIds value ,
    R.Trace.modelRemaining value , R.Trace.toolRemaining value , R.Trace.events value ,
    R.Trace.eventsOmitted value , tt

  timestamp : ∀ number → number ≤ Primitive.u64Maximum → ∀ suffix → Encoding.Delimited suffix →
    Back.Returns P.u64 (Compact.bytes (JSON.unsigned number) (Compact.unsigned number) ++ suffix) number suffix
  timestamp number bounded suffix delimiter = UnsignedRead.Parser.roundTrip checks Primitive.u64Maximum number
    bounded bounded suffix (Delimiters.numberStopped suffix delimiter)

  optionalTimestamp : ∀ number → number ≤ Primitive.u64Maximum → ∀ suffix → Encoding.Delimited suffix →
    Back.Returns (Option.read P.u64)
      (Compact.bytes (JSON.unsigned number) (Compact.unsigned number) ++ suffix) (just number) suffix
  optionalTimestamp number bounded suffix delimiter = OptionRead.number P.u64
    (Compact.bytes (JSON.unsigned number) (Compact.unsigned number) ++
     suffix)
    number suffix (Start.append (Start.unsigned number) suffix)
    (timestamp number bounded suffix delimiter)

  eventVector : ∀ allowance values valid → All B.EventBounds values → ∀ suffix →
    Back.Returns (P.vector P.event (suc (suc allowance)))
      (Compact.bytes (JSON.array (map Wire.event values))
        (Compact.array (Support.array Wire.event Serialize.event values valid)) ++ suffix) values suffix
  eventVector allowance values valid bounded suffix = Array.Parser.roundTrip checks P.event Raw.arrayExpected
    (suc allowance) B.EventBounds (Events.roundTrip allowance) values
    valid bounded suffix

  written : ∀ allowance value (valid : TextBounds.TraceText value) → B.TraceBounds value →
    E.Emits D.traceFields (P.traceReaders (suc (suc allowance))) (values value)
      (Wire.traceFields value) (supported value valid)
  written allowance value valid bounded = E.emitted
    (λ suffix delimiter →
       UUIDRead.Parser.roundTrip checks (R.Trace.identity value) suffix)
    $
    E.emitted
    (timestamp (R.Trace.startedAt value)
     (B.TraceBounds.started bounded))
    $
    Build.optionalBounded (toList "finished_at") tt JSON.unsigned D.u64
    (Option.read P.u64) Compact.unsigned optionalTimestamp
    (R.Trace.finishedAt value) (B.TraceBounds.finished bounded)
    $
    E.emitted
    (λ suffix delimiter →
       TextRead.Parser.roundTrip checks (R.Trace.status value)
       (TextBounds.TraceText.status valid) suffix)
    $
    Build.optional (toList "block_reason") tt JSON.string JSON.asString
    (Option.read P.A.readText) (λ text valid → Compact.string valid)
    Events.optionalText (R.Trace.blockReason value)
    (TextBounds.TraceText.reason valid)
    $
    E.emitted
    (λ suffix delimiter →
       UUIDVector.Parser.roundTrip checks sizeMaximum (suc allowance)
       (R.Trace.selectedIds value) suffix)
    $
    E.emitted
    (Sizes.size (R.Trace.modelRemaining value)
     (B.TraceBounds.model bounded))
    $
    E.emitted
    (Sizes.size (R.Trace.toolRemaining value)
     (B.TraceBounds.tool bounded))
    $
    E.emitted
    (λ suffix delimiter →
       eventVector allowance (R.Trace.events value)
       (TextBounds.TraceText.events valid) (B.TraceBounds.events bounded)
       suffix)
    $
    E.emitted
    (Sizes.size (R.Trace.eventsOmitted value)
     (B.TraceBounds.omitted bounded))
    E.done

  roundTrip : ∀ allowance value (valid : TextBounds.TraceText value) → B.TraceBounds value → ∀ suffix →
    Back.Returns (P.trace (suc (suc (suc allowance))))
      (Compact.bytes (Wire.trace value) (Serialize.trace value valid) ++ suffix) value suffix
  roundTrip allowance value valid bounded suffix = Compose.mapProductive
    (λ parsed → D.buildTrace (Slots.toSequence D.traceFields parsed))
    (TypedRecord.Parser.read checks D.traceFields P.traceReaders
     Raw.recordExpected (suc (suc (suc allowance)))
     (Compact.bytes (Wire.trace value) (Serialize.trace value valid) ++
      suffix))
    (E.Parser.roundTrip checks D.traceFields P.traceReaders
     Raw.recordExpected (suc (suc allowance)) (values value)
     (Wire.traceFields value) (supported value valid)
     (toWitness
      {a? = Objects.Names.unique? (Struct.names D.traceFields)} tt)
     (written allowance value valid bounded) suffix)
