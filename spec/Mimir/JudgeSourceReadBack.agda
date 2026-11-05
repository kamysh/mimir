{-# OPTIONS --safe #-}
-- Native source-failure records preserve all text and byte-offset fields.
import Mimir.FloatConversion
module Mimir.JudgeSourceReadBack (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Bool using (true; false)
open import Data.Fin using (zero; suc)
open import Data.List using ([]; _++_)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; _≤_)
import Data.Nat as Nat
open import Data.Nat.Properties using (≤-trans)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)
import Mimir.SignedMachine as Machine
import Mimir.SourceFailure as Source
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
import Mimir.JudgeTextReadBack as TextReadDependency
private
  module TextRead = TextReadDependency floatConversion
import Mimir.JudgeUnsignedReadBack as UnsignedReadDependency
private
  module UnsignedRead = UnsignedReadDependency floatConversion
import Mimir.SerdeRecord as TypedRecordDependency
private
  module TypedRecord = TypedRecordDependency floatConversion
import Mimir.SerdeSlots as Slots
import Mimir.SerdeReadBack as Back
import Mimir.SerdeReadBackComposition as ComposeDependency
private
  module Compose = ComposeDependency floatConversion
import Mimir.SerdeObjectReadBack as ObjectDependency
private
  module Object = ObjectDependency floatConversion
import Mimir.JsonObjectReadBack as Encoding
import Mimir.JsonCompactRecords as Compact
import Mimir.StructuredValue as JSON

supported : ∀ value → TextBounds.SourceText value → All Compact.FieldSupported (Wire.sourceFields value)
supported value valid =
  Serialize.entry "stage" tt (Compact.string (TextBounds.SourceText.stage valid)) All.∷
  Serialize.entry "detail" tt (Compact.string (TextBounds.SourceText.detail valid)) All.∷
  Serialize.entry "total_bytes" tt (Compact.unsigned (Source.Failure.totalBytes value)) All.∷
  Serialize.entry "excerpt_start" tt (Compact.unsigned (Source.Failure.excerptStart value)) All.∷
  Serialize.entry "excerpt" tt (Compact.string (TextBounds.SourceText.excerpt valid)) All.∷ All.[]

module Parser (checks : Machine.OverflowChecks) (sizeMaximum : ℕ)
  (nativeWidth : sizeMaximum ≤ Primitive.u64Maximum) where
  private
    module D = Decode.Size sizeMaximum
    module B = Bounds.Size sizeMaximum
    module P = Raw.Parser checks sizeMaximum

  stored : Source.Failure → Slots.Slots D.sourceFields
  stored value = just (Source.Failure.stage value) , just (Source.Failure.detail value) ,
    just (Source.Failure.totalBytes value) , just (Source.Failure.excerptStart value) ,
    just (Source.Failure.excerpt value) , tt

  values : Source.Failure → Slots.Values D.sourceFields
  values value = Source.Failure.stage value , Source.Failure.detail value ,
    Source.Failure.totalBytes value , Source.Failure.excerptStart value , Source.Failure.excerpt value , tt

  size : ∀ number → number ≤ sizeMaximum → ∀ suffix → Encoding.Delimited suffix →
    Back.Returns P.size (Compact.bytes (JSON.unsigned number) (Compact.unsigned number) ++ suffix) number suffix
  size number bounded suffix delimiter = UnsignedRead.Parser.roundTrip checks sizeMaximum number bounded
    (≤-trans bounded nativeWidth) suffix
    (Delimiters.numberStopped suffix delimiter)

  written : ∀ allowance value (valid : TextBounds.SourceText value) → B.SourceBounds value →
    Object.Record.Written D.sourceFields (P.sourceReaders allowance) true
      (Slots.empty D.sourceFields) (Wire.sourceFields value) (supported value valid) (stored value)
  written allowance value valid bounded = Object.Record.emitted zero (Source.Failure.stage value) refl refl
    (λ suffix delimiter →
       TextRead.Parser.roundTrip checks (Source.Failure.stage value)
       (TextBounds.SourceText.stage valid) suffix)
    (Object.Record.emitted (suc zero) (Source.Failure.detail value)
     refl refl
     (λ suffix delimiter →
        TextRead.Parser.roundTrip checks (Source.Failure.detail value)
        (TextBounds.SourceText.detail valid) suffix)
     (Object.Record.emitted (suc (suc zero))
      (Source.Failure.totalBytes value) refl refl
      (size (Source.Failure.totalBytes value)
       (B.SourceBounds.total bounded))
      (Object.Record.emitted (suc (suc (suc zero)))
       (Source.Failure.excerptStart value) refl refl
       (size (Source.Failure.excerptStart value)
        (B.SourceBounds.start bounded))
       (Object.Record.emitted (suc (suc (suc (suc zero))))
        (Source.Failure.excerpt value) refl refl
        (λ suffix delimiter →
           TextRead.Parser.roundTrip checks (Source.Failure.excerpt value)
           (TextBounds.SourceText.excerpt valid) suffix)
        (Object.Record.done false (stored value))))))

  resolved : ∀ value → Slots.Resolved D.sourceFields (stored value) (values value)
  resolved value = Slots.supplied
    (Slots.supplied
     (Slots.supplied
      (Slots.supplied (Slots.supplied Slots.resolvedEmpty))))

  roundTrip : ∀ allowance value (valid : TextBounds.SourceText value) → B.SourceBounds value → ∀ suffix →
    Back.Returns (P.source (Nat.suc allowance))
      (Compact.bytes (Wire.source value) (Serialize.source value valid) ++ suffix) value suffix
  roundTrip allowance value valid bounded suffix = Compose.mapProductive
    (λ parsed → D.buildSource (Slots.toSequence D.sourceFields parsed))
    (TypedRecord.Parser.read checks D.sourceFields P.sourceReaders
     Raw.recordExpected (Nat.suc allowance)
     (Compact.bytes (Wire.source value) (Serialize.source value valid)
      ++ suffix))
    (Object.Parser.roundTrip checks D.sourceFields P.sourceReaders
     Raw.recordExpected allowance (Wire.sourceFields value)
     (supported value valid) (stored value) (values value) suffix
     (written allowance value valid bounded) (resolved value))
