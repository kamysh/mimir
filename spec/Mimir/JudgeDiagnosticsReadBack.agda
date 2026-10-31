{-# OPTIONS --safe #-}
-- The persisted diagnostics document preserves every trace and nested event.
import Mimir.FloatConversion
module Mimir.JudgeDiagnosticsReadBack (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.List using (_++_; map)
open import Data.List.Relation.Unary.All using (All)
open import Data.Nat using (ℕ; _≤_; suc)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Data.String using (toList)
open import Relation.Nullary.Decidable.Core using (toWitness)
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
import Mimir.SerdeObjectVectorReadBack as VectorDependency
private
  module Vector = VectorDependency floatConversion
import Mimir.JsonObjects as Objects
import Mimir.JsonCompactRecords as Compact
import Mimir.JsonRecordSupport as Support
import Mimir.StructuredValue as JSON
module R = Wire.R

module Parser (checks : Machine.OverflowChecks) (sizeMaximum : ℕ)
  (nativeWidth : sizeMaximum ≤ Primitive.u64Maximum) where
  private
    module D = Decode.Size sizeMaximum
    module B = Bounds.Size sizeMaximum
    module P = Raw.Parser checks sizeMaximum
    module Traces = TraceRead.Parser checks sizeMaximum nativeWidth
    module Array = Vector.Encoding R.Trace TextBounds.TraceText Wire.traceFields TraceRead.supported

  traceVector : ∀ allowance values valid → B.DiagnosticsBounds values → ∀ suffix →
    Back.Returns (P.vector P.trace (suc (suc (suc (suc allowance)))))
      (Compact.bytes (JSON.array (map Wire.trace values))
        (Compact.array (Support.array Wire.trace Serialize.trace values valid)) ++ suffix) values suffix
  traceVector allowance values valid bounded suffix = Array.Parser.roundTrip checks P.trace Raw.arrayExpected
    (suc (suc (suc allowance))) B.TraceBounds
    (Traces.roundTrip allowance) values valid bounded suffix

  roundTrip : ∀ allowance values (valid : TextBounds.DiagnosticsText values) → B.DiagnosticsBounds values → ∀ suffix →
    Back.Returns (P.diagnostics (suc (suc (suc (suc (suc allowance))))))
      (Compact.bytes (Wire.diagnostics values) (Serialize.diagnostics values valid) ++ suffix) values suffix
  roundTrip allowance values valid bounded suffix = Compose.mapProductive
    (λ parsed →
       D.buildDiagnostics (Slots.toSequence D.diagnosticsFields parsed))
    (TypedRecord.Parser.read checks D.diagnosticsFields
     P.diagnosticsReaders Raw.recordExpected
     (suc (suc (suc (suc (suc allowance)))))
     (Compact.bytes (Wire.diagnostics values)
      (Serialize.diagnostics values valid)
      ++ suffix))
    (E.Parser.roundTrip checks D.diagnosticsFields P.diagnosticsReaders
     Raw.recordExpected (suc (suc (suc (suc allowance)))) (values , tt)
     (Wire.member (toList "attempts")
      (JSON.array (map Wire.trace values)))
     (Serialize.member "attempts" tt
      (Compact.array
       (Support.array Wire.trace Serialize.trace values valid)))
     (toWitness
      {a? = Objects.Names.unique? (Struct.names D.diagnosticsFields)} tt)
     (E.emitted
      (λ suffix delimiter →
         traceVector allowance values valid bounded suffix)
      E.done)
     suffix)
