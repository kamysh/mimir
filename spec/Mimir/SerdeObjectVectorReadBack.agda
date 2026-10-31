{-# OPTIONS --safe #-}
-- Nested object vectors use the same concrete serializer and raw child reader.
import Mimir.FloatConversion
module Mimir.SerdeObjectVectorReadBack (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Fin using (#_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
open import Data.Nat using (ℕ; suc)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
import Mimir.StructuredValue as JSON
import Mimir.JsonCompactRecords as Compact
import Mimir.JsonRecordSupport as Support
import Mimir.JudgeStateWire as Wire
import Mimir.SerdeFlow as Flow
import Mimir.SerdeReadBack as Back
import Mimir.SerdeVector as RawDependency
private
  module Raw = RawDependency floatConversion
import Mimir.SerdeVectorReadBack as VectorDependency
private
  module Vector = VectorDependency floatConversion
import Mimir.SerdeValidatedVectorReadBack as CheckedDependency
private
  module Checked = CheckedDependency floatConversion
import Mimir.SignedMachine as Machine
import Mimir.Validation as V

leading : ∀ fields valid → Vector.Leading (Compact.bytes (JSON.object fields) (Compact.object valid))
leading [] All.[] = Vector.leading (# 123) _ refl (λ ()) (λ ())
leading (entry ∷ fields) (valid All.∷ rest) = Vector.leading (# 123) _ refl (λ ()) (λ ())

module Encoding (Value : Set) (validity : Value → Set) (fields : Value → Wire.Fields)
  (supported : ∀ value → validity value → All Compact.FieldSupported (fields value)) where
  private
    encode : Value → JSON.Value
    encode value = JSON.object (fields value)
    support : ∀ value → validity value → Compact.Supported (encode value)
    support value valid = Compact.object (supported value valid)
    module E = Checked.Encoding Value validity encode support

  module Parser (checks : Machine.OverflowChecks) (child : ℕ → Flow.Parser Value)
    (expected : V.Fault) (allowance : ℕ) (admitted : Value → Set)
    (readElement : ∀ value valid → admitted value → ∀ suffix →
      Back.Returns (child allowance) (Compact.bytes (encode value) (support value valid) ++ suffix) value suffix) where

    roundTrip : ∀ values valid → All admitted values → ∀ suffix →
      Back.Returns (Raw.Parser.read checks Value child expected (suc allowance))
        (Compact.bytes (JSON.array (map encode values))
          (Compact.array (Support.array encode support values valid)) ++ suffix) values suffix
    roundTrip values valid accepted suffix = E.Parser.roundTrip checks child expected allowance admitted
      (λ value valid → leading (fields value) (supported value valid))
      (λ value valid accepted suffix delimiter →
         readElement value valid accepted suffix)
      values valid accepted suffix

module Uniform (Value : Set) (encode : Value → JSON.Value)
  (supported : ∀ value → Compact.Supported (encode value)) where
  private
    module E = Checked.Encoding Value (λ _ → ⊤) encode (λ value _ → supported value)

  valid : ∀ (values : List Value) → All (λ _ → ⊤) values
  valid [] = All.[]
  valid (value ∷ values) = tt All.∷ valid values

  supportSame : ∀ values →
    Support.array encode (λ value (_ : ⊤) → supported value) values (valid values) ≡
    Support.arrayUniform encode supported values
  supportSame [] = refl
  supportSame (value ∷ values) = cong (supported value All.∷_) (supportSame values)

  module Parser (checks : Machine.OverflowChecks) (child : ℕ → Flow.Parser Value)
    (expected : V.Fault) (allowance : ℕ) (admitted : Value → Set)
    (starts : ∀ value → Vector.Leading (Compact.bytes (encode value) (supported value)))
    (readElement : ∀ value → admitted value → ∀ suffix →
      Back.Returns (child allowance) (Compact.bytes (encode value) (supported value) ++ suffix) value suffix) where

    roundTrip : ∀ values → All admitted values → ∀ suffix →
      Back.Returns (Raw.Parser.read checks Value child expected (suc allowance))
        (Compact.bytes (JSON.array (map encode values))
          (Compact.array (Support.arrayUniform encode supported values)) ++ suffix) values suffix
    roundTrip values accepted suffix = subst
      (λ proof →
         Back.Returns
         (Raw.Parser.read checks Value child expected (suc allowance))
         (Compact.bytes (JSON.array (map encode values))
          (Compact.array proof)
          ++ suffix)
         values suffix)
      (supportSame values)
      (E.Parser.roundTrip checks child expected allowance admitted
       (λ value _ → starts value)
       (λ value _ accepted suffix delimiter →
          readElement value accepted suffix)
       values (valid values) accepted suffix)
