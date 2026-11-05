{-# OPTIONS --safe #-}
-- Raw scalar field visitors for persisted judge records. Their unsigned and
-- signed validation reuses the established schema range checks.
import Mimir.FloatConversion
module Mimir.JudgeStateAtoms (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.List using ([])
open import Data.Nat using (ℕ; _≤_)
open import Data.Integer using (ℤ; +_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Mimir.Text using (Text)
import Mimir.SerdeScalar as ScalarDependency
private
  module Scalar = ScalarDependency floatConversion
import Mimir.NumericTokens as Numeric
import Mimir.SerdeFlow as Flow
import Mimir.SignedMachine as Machine
import Mimir.Unsigned as Unsigned
import Mimir.StructuredValue as JSON
import Mimir.JudgeStatePrimitives as P
import Mimir.UUIDGroups as UUID
import Mimir.Validation as V

integerExpected : V.Fault
integerExpected = V.fault [] V.malformedInput "expected an integer"

stringExpected : V.Fault
stringExpected = V.fault [] V.malformedInput "expected a string"

uint : ℕ → Scalar.Scalar → V.Fault ⊎ ℕ
uint maximum (Scalar.number (Numeric.unsigned64 value)) = P.uint maximum (JSON.unsigned (Unsigned.UInt.number value))
uint maximum (Scalar.number (Numeric.signed64 value)) = P.uint maximum (JSON.signed (Numeric.I64.Integer.number value))
uint maximum other = inj₁ integerExpected

signed : Scalar.Scalar → V.Fault ⊎ ℤ
signed (Scalar.number (Numeric.unsigned64 value)) = P.signedNumber (+ Unsigned.UInt.number value)
signed (Scalar.number (Numeric.signed64 value)) = P.signedNumber (Numeric.I64.Integer.number value)
signed other = inj₁ integerExpected

text : Scalar.Scalar → V.Fault ⊎ Text
text (Scalar.string value) = inj₂ value
text other = inj₁ stringExpected

uuid : Scalar.Scalar → V.Fault ⊎ UUID.UUID
uuid (Scalar.string value) = P.uuid (JSON.string value)
uuid other = inj₁ stringExpected

uintBounded : ∀ maximum scalar value → uint maximum scalar ≡ inj₂ value → value ≤ maximum
uintBounded maximum (Scalar.number (Numeric.unsigned64 number)) value observed = JSON.integerInRange (P.uintSound maximum (JSON.unsigned (Unsigned.UInt.number number)) value observed)
uintBounded maximum (Scalar.number (Numeric.signed64 number)) value observed = JSON.integerInRange (P.uintSound maximum (JSON.signed (Numeric.I64.Integer.number number)) value observed)

signedBounded : ∀ scalar value → signed scalar ≡ inj₂ value → P.I64.InRange value
signedBounded (Scalar.number (Numeric.unsigned64 number)) value observed = subst P.I64.InRange (proj₁ (P.signedNumberSound (+ Unsigned.UInt.number number) value observed)) (proj₂ (P.signedNumberSound (+ Unsigned.UInt.number number) value observed))
signedBounded (Scalar.number (Numeric.signed64 number)) value observed = subst P.I64.InRange (proj₁ (P.signedNumberSound (Numeric.I64.Integer.number number) value observed)) (proj₂ (P.signedNumberSound (Numeric.I64.Integer.number number) value observed))

textExact : ∀ scalar value → text scalar ≡ inj₂ value → scalar ≡ Scalar.string value
textExact (Scalar.string textValue) value refl = refl

module Parser (checks : Machine.OverflowChecks) where
  module S = Scalar.Parser checks

  readUint : ℕ → Flow.Parser ℕ
  readUint maximum = S.read (uint maximum) integerExpected

  readSigned : Flow.Parser ℤ
  readSigned = S.read signed integerExpected

  readText : Flow.Parser Text
  readText = S.read text stringExpected

  readUUID : Flow.Parser UUID.UUID
  readUUID = S.read uuid stringExpected

  uintReadBounded : ∀ maximum input value position →
    Flow.Productive.result (readUint maximum input) ≡ Flow.ordinary (Flow.F.success value position) → value ≤ maximum
  uintReadBounded maximum input value position observed with S.readSound (uint maximum) integerExpected input value position observed
  ... | scalar , admitted = uintBounded maximum scalar value admitted

  signedReadBounded : ∀ input value position →
    Flow.Productive.result (readSigned input) ≡ Flow.ordinary (Flow.F.success value position) → P.I64.InRange value
  signedReadBounded input value position observed with S.readSound signed integerExpected input value position observed
  ... | scalar , admitted = signedBounded scalar value admitted
