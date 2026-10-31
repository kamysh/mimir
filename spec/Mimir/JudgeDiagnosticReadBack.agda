{-# OPTIONS --safe #-}
-- Diagnostic records preserve timestamps, experience identities and valid text.
import Mimir.FloatConversion
module Mimir.JudgeDiagnosticReadBack (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Bool using (true; false)
open import Data.Fin using (zero; suc)
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (just)
open import Data.Nat using (ℕ)
import Data.Nat as Nat
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
import Mimir.JudgeStateText as TextBounds
import Mimir.JudgeStatePrimitives as Primitive
import Mimir.JudgeDeferredReadBack as DelimitersDependency
private
  module Delimiters = DelimitersDependency floatConversion
import Mimir.JudgeUUIDReadBack as UUIDReadDependency
private
  module UUIDRead = UUIDReadDependency floatConversion
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

pairs : R.FailureDiagnostic → Wire.Fields
pairs value = (toList "observed_at" , JSON.unsigned (R.FailureDiagnostic.observedAt value)) ∷
  (toList "experience_id" , UUID.encode (R.FailureDiagnostic.experience value)) ∷
  (toList "tool" , JSON.string (R.FailureDiagnostic.tool value)) ∷
  (toList "detail" , JSON.string (R.FailureDiagnostic.detail value)) ∷ []

supported : ∀ value → TextBounds.DiagnosticText value → All Compact.FieldSupported (pairs value)
supported value valid =
  Serialize.entry "observed_at" tt (Compact.unsigned (R.FailureDiagnostic.observedAt value)) All.∷
  Serialize.entry "experience_id" tt (Serialize.uuid (R.FailureDiagnostic.experience value)) All.∷
  Serialize.entry "tool" tt (Compact.string (TextBounds.DiagnosticText.tool valid)) All.∷
  Serialize.entry "detail" tt (Compact.string (TextBounds.DiagnosticText.detail valid)) All.∷ All.[]

module Parser (checks : Machine.OverflowChecks) (sizeMaximum : ℕ) where
  private
    module D = Decode.Size sizeMaximum
    module B = Bounds.Size sizeMaximum
    module P = Raw.Parser checks sizeMaximum

  stored : R.FailureDiagnostic → Slots.Slots D.diagnosticFields
  stored value = just (R.FailureDiagnostic.observedAt value) , just (R.FailureDiagnostic.experience value) ,
    just (R.FailureDiagnostic.tool value) , just (R.FailureDiagnostic.detail value) , tt

  values : R.FailureDiagnostic → Slots.Values D.diagnosticFields
  values value = R.FailureDiagnostic.observedAt value , R.FailureDiagnostic.experience value ,
    R.FailureDiagnostic.tool value , R.FailureDiagnostic.detail value , tt

  timestamp : ∀ value → B.DiagnosticBounds value → ∀ suffix → Encoding.Delimited suffix →
    Back.Returns P.u64
      (Compact.bytes (JSON.unsigned (R.FailureDiagnostic.observedAt value))
        (Compact.unsigned (R.FailureDiagnostic.observedAt value)) ++ suffix) (R.FailureDiagnostic.observedAt value) suffix
  timestamp value bounded suffix delimiter = UnsignedRead.Parser.roundTrip checks Primitive.u64Maximum
    (R.FailureDiagnostic.observedAt value) bounded bounded suffix
    (Delimiters.numberStopped suffix delimiter)

  written : ∀ allowance value (valid : TextBounds.DiagnosticText value) → B.DiagnosticBounds value →
    Object.Record.Written D.diagnosticFields (P.diagnosticReaders allowance) true
      (Slots.empty D.diagnosticFields) (pairs value) (supported value valid) (stored value)
  written allowance value valid bounded = Object.Record.emitted zero (R.FailureDiagnostic.observedAt value)
    refl refl (timestamp value bounded)
    (Object.Record.emitted (suc zero)
     (R.FailureDiagnostic.experience value) refl refl
     (λ suffix delimiter →
        UUIDRead.Parser.roundTrip checks
        (R.FailureDiagnostic.experience value) suffix)
     (Object.Record.emitted (suc (suc zero))
      (R.FailureDiagnostic.tool value) refl refl
      (λ suffix delimiter →
         TextRead.Parser.roundTrip checks (R.FailureDiagnostic.tool value)
         (TextBounds.DiagnosticText.tool valid) suffix)
      (Object.Record.emitted (suc (suc (suc zero)))
       (R.FailureDiagnostic.detail value) refl refl
       (λ suffix delimiter →
          TextRead.Parser.roundTrip checks (R.FailureDiagnostic.detail value)
          (TextBounds.DiagnosticText.detail valid) suffix)
       (Object.Record.done false (stored value)))))

  resolved : ∀ value → Slots.Resolved D.diagnosticFields (stored value) (values value)
  resolved value = Slots.supplied
    (Slots.supplied
     (Slots.supplied (Slots.supplied Slots.resolvedEmpty)))

  roundTrip : ∀ allowance value (valid : TextBounds.DiagnosticText value) → B.DiagnosticBounds value → ∀ suffix →
    Back.Returns (P.diagnostic (Nat.suc allowance))
      (Compact.bytes (Wire.diagnostic value) (Serialize.diagnostic value valid) ++ suffix) value suffix
  roundTrip allowance value valid bounded suffix = Compose.mapProductive
    (λ parsed →
       D.buildDiagnostic (Slots.toSequence D.diagnosticFields parsed))
    (TypedRecord.Parser.read checks D.diagnosticFields
     P.diagnosticReaders Raw.recordExpected (Nat.suc allowance)
     (Compact.bytes (Wire.diagnostic value)
      (Serialize.diagnostic value valid)
      ++ suffix))
    (Object.Parser.roundTrip checks D.diagnosticFields
     P.diagnosticReaders Raw.recordExpected allowance (pairs value)
     (supported value valid) (stored value) (values value) suffix
     (written allowance value valid bounded) (resolved value))
