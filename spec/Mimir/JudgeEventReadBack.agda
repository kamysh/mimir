{-# OPTIONS --safe #-}
-- Every native event survives compact serialization, including omitted optionals.
import Mimir.FloatConversion
module Mimir.JudgeEventReadBack (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.List using (_∷_; _++_)
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
import Mimir.JudgeUUIDReadBack as UUIDReadDependency
private
  module UUIDRead = UUIDReadDependency floatConversion
import Mimir.JudgeTextReadBack as TextReadDependency
private
  module TextRead = TextReadDependency floatConversion
import Mimir.JudgeUnsignedReadBack as UnsignedReadDependency
private
  module UnsignedRead = UnsignedReadDependency floatConversion
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
import Mimir.JsonObjectReadBack as Encoding
import Mimir.JsonObjects as Objects
import Mimir.JsonCompactRecords as Compact
import Mimir.StructuredValue as JSON
import Mimir.UnicodeText as Unicode
module R = Wire.R

objectFields : ∀ {pairs} → Compact.Supported (JSON.object pairs) → All Compact.FieldSupported pairs
objectFields (Compact.object supported) = supported

supported : ∀ value → TextBounds.EventText value → All Compact.FieldSupported (Wire.eventFields value)
supported value valid = objectFields (Serialize.event value valid)

module Parser (checks : Machine.OverflowChecks) (sizeMaximum : ℕ)
  (nativeWidth : sizeMaximum ≤ Primitive.u64Maximum) where
  private
    module D = Decode.Size sizeMaximum
    module B = Bounds.Size sizeMaximum
    module P = Raw.Parser checks sizeMaximum
    module Sizes = SourceRead.Parser checks sizeMaximum nativeWidth

  values : R.Event → Slots.Values D.eventFields
  values value = R.Event.at value , R.Event.experience value , R.Event.kind value ,
    R.Event.modelRemaining value , R.Event.toolRemaining value , R.Event.tool value ,
    R.Event.detail value , R.Event.detailBytes value , tt

  optionalText : ∀ text (valid : Unicode.Valid text) suffix → Encoding.Delimited suffix →
    Back.Returns (Option.read P.A.readText)
      (Compact.bytes (JSON.string text) (Compact.string valid) ++ suffix) (just text) suffix
  optionalText text valid suffix delimiter = OptionRead.string P.A.readText text valid text suffix
    (TextRead.Parser.roundTrip checks text valid suffix)

  optionalSize : ∀ number → number ≤ sizeMaximum → ∀ suffix → Encoding.Delimited suffix →
    Back.Returns (Option.read P.size)
      (Compact.bytes (JSON.unsigned number) (Compact.unsigned number) ++ suffix) (just number) suffix
  optionalSize number bounded suffix delimiter = OptionRead.number P.size
    (Compact.bytes (JSON.unsigned number) (Compact.unsigned number) ++
     suffix)
    number suffix (Start.append (Start.unsigned number) suffix)
    (Sizes.size number bounded suffix delimiter)

  written : ∀ allowance value (valid : TextBounds.EventText value) → B.EventBounds value →
    E.Emits D.eventFields (P.eventReaders allowance) (values value)
      (Wire.eventFields value) (supported value valid)
  written allowance value valid bounded = E.emitted
    (λ checks₁ fields →
       UnsignedRead.Parser.roundTrip checks Primitive.u64Maximum
       (R.Event.at value) (B.EventBounds.at bounded)
       (B.EventBounds.at bounded) checks₁
       (Delimiters.numberStopped checks₁ fields))
    $
    E.emitted
    (λ readers expected →
       UUIDRead.Parser.roundTrip checks (R.Event.experience value)
       readers)
    $
    E.emitted
    (λ allowance₁ values₁ →
       TextRead.Parser.roundTrip checks (R.Event.kind value)
       (TextBounds.EventText.kind valid) allowance₁)
    $
    E.emitted
    (Sizes.size (R.Event.modelRemaining value)
     (B.EventBounds.model bounded))
    $
    E.emitted
    (Sizes.size (R.Event.toolRemaining value)
     (B.EventBounds.tool bounded))
    $
    Build.optional (toList "tool") tt JSON.string JSON.asString
    (Option.read P.A.readText) (λ pairs valid₁ → Compact.string valid₁)
    optionalText (R.Event.tool value) (TextBounds.EventText.tool valid)
    $
    Build.optional (toList "detail") tt JSON.string JSON.asString
    (Option.read P.A.readText) (λ suffix₁ valid → Compact.string valid)
    optionalText (R.Event.detail value)
    (TextBounds.EventText.detail valid)
    $
    Build.optionalBoundedLast (toList "detail_bytes") tt JSON.unsigned
    D.size (Option.read P.size) Compact.unsigned optionalSize
    (R.Event.detailBytes value) (B.EventBounds.bytes bounded)

  roundTrip : ∀ allowance value (valid : TextBounds.EventText value) → B.EventBounds value → ∀ suffix →
    Back.Returns (P.event (suc allowance))
      (Compact.bytes (Wire.event value) (Serialize.event value valid) ++ suffix) value suffix
  roundTrip allowance value valid bounded suffix = Compose.mapProductive
    (λ parsed → D.buildEvent (Slots.toSequence D.eventFields parsed))
    (TypedRecord.Parser.read checks D.eventFields P.eventReaders
     Raw.recordExpected (suc allowance)
     (Compact.bytes (Wire.event value) (Serialize.event value valid) ++
      suffix))
    (E.Parser.roundTrip checks D.eventFields P.eventReaders
     Raw.recordExpected allowance (values value)
     (Wire.eventFields value) (supported value valid)
     (toWitness
      {a? = Objects.Names.unique? (Struct.names D.eventFields)} tt)
     (written allowance value valid bounded) suffix)
