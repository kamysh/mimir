{-# OPTIONS --safe #-}
-- Every natively bounded deferred-review record round-trips through raw bytes.
import Mimir.FloatConversion
module Mimir.JudgeDeferredReadBack (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Bool using (true; false)
open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_; _++_)
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
import Mimir.JudgeStateAtoms as AtomsDependency
private
  module Atoms = AtomsDependency floatConversion
import Mimir.JudgeUUIDReadBack as UUIDReadDependency
private
  module UUIDRead = UUIDReadDependency floatConversion
import Mimir.JudgeSignedReadBack as SignedReadDependency
private
  module SignedRead = SignedReadDependency floatConversion
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
import Mimir.SerdeIntegerReadBack as IntegerDependency
private
  module Integer = IntegerDependency floatConversion
import Mimir.ByteText as Bytes
import Mimir.DecimalLexer as Lexer
module R = Wire.R

numberStopped : ∀ suffix → Encoding.Delimited suffix → Integer.Stopped (Bytes.text suffix)
numberStopped ._ (Encoding.comma suffix) = Lexer.notDecoded ',' refl , (λ ()) , (λ ()) , (λ ())
numberStopped ._ (Encoding.close suffix) = Lexer.notDecoded '}' refl , (λ ()) , (λ ()) , (λ ())

pairs : R.Deferred → Wire.Fields
pairs value = (toList "id" , UUID.encode (R.Deferred.identity value)) ∷
  (toList "revision" , JSON.signed (R.Deferred.revision value)) ∷ []

supported : ∀ value → All Compact.FieldSupported (pairs value)
supported value = Serialize.entry "id" tt (Serialize.uuid (R.Deferred.identity value)) All.∷
  Serialize.entry "revision" tt (Compact.signed (R.Deferred.revision value)) All.∷ All.[]

module Parser (checks : Machine.OverflowChecks) (sizeMaximum : ℕ) where
  private
    module D = Decode.Size sizeMaximum
    module B = Bounds.Size sizeMaximum
    module P = Raw.Parser checks sizeMaximum
    module A = Atoms.Parser checks

  stored : R.Deferred → Slots.Slots D.deferredFields
  stored value = just (R.Deferred.identity value) , just (R.Deferred.revision value) , tt

  values : R.Deferred → Slots.Values D.deferredFields
  values value = R.Deferred.identity value , R.Deferred.revision value , tt

  signed : ∀ value → B.DeferredBounds value → ∀ suffix → Encoding.Delimited suffix →
    Back.Returns A.readSigned
      (Compact.bytes (JSON.signed (R.Deferred.revision value))
        (Compact.signed (R.Deferred.revision value)) ++ suffix) (R.Deferred.revision value) suffix
  signed value bounded suffix delimiter = SignedRead.Parser.roundTrip checks (R.Deferred.revision value)
    bounded suffix (numberStopped suffix delimiter)

  written : ∀ allowance value → B.DeferredBounds value →
    Object.Record.Written D.deferredFields (P.deferredReaders allowance) true
      (Slots.empty D.deferredFields) (pairs value) (supported value) (stored value)
  written allowance value bounded = Object.Record.emitted zero (R.Deferred.identity value) refl refl
    (λ suffix delimiter →
       UUIDRead.Parser.roundTrip checks (R.Deferred.identity value)
       suffix)
    (Object.Record.emitted (suc zero) (R.Deferred.revision value) refl
     refl (signed value bounded)
     (Object.Record.done false (stored value)))

  resolved : ∀ value → Slots.Resolved D.deferredFields (stored value) (values value)
  resolved value = Slots.supplied (Slots.supplied Slots.resolvedEmpty)

  roundTrip : ∀ allowance value → B.DeferredBounds value → ∀ suffix →
    Back.Returns (P.deferred (Nat.suc allowance))
      (Compact.bytes (Wire.deferred value) (Serialize.deferred value) ++ suffix) value suffix
  roundTrip allowance value bounded suffix = Compose.mapProductive
    (λ parsed →
       D.buildDeferred (Slots.toSequence D.deferredFields parsed))
    (TypedRecord.Parser.read checks D.deferredFields P.deferredReaders
     Raw.recordExpected (Nat.suc allowance)
     (Compact.bytes (Wire.deferred value) (Serialize.deferred value) ++
      suffix))
    (Object.Parser.roundTrip checks D.deferredFields P.deferredReaders
     Raw.recordExpected allowance (pairs value) (supported value)
     (stored value) (values value) suffix
     (written allowance value bounded) (resolved value))
