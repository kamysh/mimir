{-# OPTIONS --safe #-}
-- Every natively bounded confirmed-review record round-trips through raw bytes.
import Mimir.FloatConversion
module Mimir.JudgeConfirmedReadBack (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Bool using (true; false)
open import Data.Fin using (zero; suc)
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (just)
open import Data.Nat using (ℕ)
import Data.Nat as Nat
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import Data.String using (toList)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)
import Mimir.SignedMachine as Machine
import Mimir.JudgeStateRaw as RawDependency
private
  module Raw = RawDependency floatConversion
import Mimir.JudgeStateDecode as Decode
import Mimir.JudgeStateWire as Wire
import Mimir.JudgeStateSerialize as Serialize
import Mimir.JudgeStateBounds as Bounds
import Mimir.JudgeStatePrimitives as Primitive
import Mimir.JudgeDeferredReadBack as DelimitersDependency
private
  module Delimiters = DelimitersDependency floatConversion
import Mimir.JudgeUUIDReadBack as UUIDReadDependency
private
  module UUIDRead = UUIDReadDependency floatConversion
import Mimir.JudgeUnsignedReadBack as UnsignedReadDependency
private
  module UnsignedRead = UnsignedReadDependency floatConversion
import Mimir.UUIDSchema as UUID
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
module R = Wire.R

pairs : R.Confirmed → Wire.Fields
pairs value = (toList "id" , UUID.encode (R.Confirmed.identity value)) ∷
  (toList "recorded_at" , JSON.unsigned (R.Confirmed.recordedAt value)) ∷ []

supported : ∀ value → All Compact.FieldSupported (pairs value)
supported value = Serialize.entry "id" tt (Serialize.uuid (R.Confirmed.identity value)) All.∷
  Serialize.entry "recorded_at" tt (Compact.unsigned (R.Confirmed.recordedAt value)) All.∷ All.[]

module Parser (checks : Machine.OverflowChecks) (sizeMaximum : ℕ) where
  private
    module D = Decode.Size sizeMaximum
    module B = Bounds.Size sizeMaximum
    module P = Raw.Parser checks sizeMaximum

  stored : R.Confirmed → Slots.Slots D.confirmedFields
  stored value = just (R.Confirmed.identity value) , just (R.Confirmed.recordedAt value) , tt

  values : R.Confirmed → Slots.Values D.confirmedFields
  values value = R.Confirmed.identity value , R.Confirmed.recordedAt value , tt

  timestamp : ∀ value → B.ConfirmedBounds value → ∀ suffix → Encoding.Delimited suffix →
    Back.Returns P.u64
      (Compact.bytes (JSON.unsigned (R.Confirmed.recordedAt value))
        (Compact.unsigned (R.Confirmed.recordedAt value)) ++ suffix) (R.Confirmed.recordedAt value) suffix
  timestamp value bounded suffix delimiter = UnsignedRead.Parser.roundTrip checks Primitive.u64Maximum
    (R.Confirmed.recordedAt value) bounded bounded suffix
    (Delimiters.numberStopped suffix delimiter)

  written : ∀ allowance value → B.ConfirmedBounds value →
    Object.Record.Written D.confirmedFields (P.confirmedReaders allowance) true
      (Slots.empty D.confirmedFields) (pairs value) (supported value) (stored value)
  written allowance value bounded = Object.Record.emitted zero (R.Confirmed.identity value) refl refl
    (λ suffix delimiter →
       UUIDRead.Parser.roundTrip checks (R.Confirmed.identity value)
       suffix)
    (Object.Record.emitted (suc zero) (R.Confirmed.recordedAt value)
     refl refl (timestamp value bounded)
     (Object.Record.done false (stored value)))

  resolved : ∀ value → Slots.Resolved D.confirmedFields (stored value) (values value)
  resolved value = Slots.supplied (Slots.supplied Slots.resolvedEmpty)

  roundTrip : ∀ allowance value → B.ConfirmedBounds value → ∀ suffix →
    Back.Returns (P.confirmed (Nat.suc allowance))
      (Compact.bytes (Wire.confirmed value) (Serialize.confirmed value) ++ suffix) value suffix
  roundTrip allowance value bounded suffix = Compose.mapProductive
    (λ parsed →
       D.buildConfirmed (Slots.toSequence D.confirmedFields parsed))
    (TypedRecord.Parser.read checks D.confirmedFields
     P.confirmedReaders Raw.recordExpected (Nat.suc allowance)
     (Compact.bytes (Wire.confirmed value) (Serialize.confirmed value)
      ++ suffix))
    (Object.Parser.roundTrip checks D.confirmedFields
     P.confirmedReaders Raw.recordExpected allowance (pairs value)
     (supported value) (stored value) (values value) suffix
     (written allowance value bounded) (resolved value))
