{-# OPTIONS --safe #-}
-- Compose the general parser laws with the judge raw-reader adapters.
import Mimir.FloatConversion
module Mimir.JudgeRawInvariant (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.List using (List)
open import Data.Maybe using (nothing; just)
import Data.Maybe.Relation.Unary.All as MaybeAll
open import Data.List.Relation.Unary.All using (All)
open import Data.Nat using (ℕ; _≤_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.SerdeSequence as Sequence
import Mimir.SerdeSlots as Slots
import Mimir.SerdeSlotInvariant as I
import Mimir.SerdeRecordInvariant as RecordDependency
private
  module Record = RecordDependency floatConversion
import Mimir.SerdeRecord as ReaderDependency
private
  module Reader = ReaderDependency floatConversion
import Mimir.SerdeVectorInvariant as VectorDependency
private
  module Vector = VectorDependency floatConversion
import Mimir.SerdeOptionInvariant as OptionDependency
private
  module Option = OptionDependency floatConversion
import Mimir.SerdeOption as OptionalDependency
private
  module Optional = OptionalDependency floatConversion
import Mimir.SerdeSuccess as S
import Mimir.SerdeSuccessTransfer as Transfer
import Mimir.SerdeScalar as ScalarDependency
private
  module Scalar = ScalarDependency floatConversion
import Mimir.SerdeScalarUnicode as ScalarUnicodeDependency
private
  module ScalarUnicode = ScalarUnicodeDependency floatConversion
import Mimir.SerdeFlow as Flow
import Mimir.JudgeStateAtoms as AtomsDependency
private
  module Atoms = AtomsDependency floatConversion
import Mimir.UnicodeText as Unicode
import Mimir.JudgeStateRaw as RawDependency
private
  module Raw = RawDependency floatConversion
import Mimir.JudgeStateBounds as Bounds
import Mimir.JudgeStatePrimitives as P
import Mimir.SignedMachine as Machine

optionalValue : ∀ {Value : Set} {property : Value → Set} {value} →
  MaybeAll.All property value → Bounds.Optional property value
optionalValue (MaybeAll.just valid) = valid
optionalValue MaybeAll.nothing = tt

textValue : ∀ scalar → ScalarUnicode.Valid scalar → ∀ value →
  Atoms.text scalar ≡ inj₂ value → Unicode.Valid value
textValue (Scalar.string text) valid value refl = valid

module Parser (checks : Machine.OverflowChecks) (sizeMaximum : ℕ) where
  private
    module R = Raw.Parser checks sizeMaximum

  uint : ∀ maximum input → S.Ensures (_≤ maximum) (Flow.Productive.result (R.A.readUint maximum input))
  uint maximum input = Transfer.fromSuccess (_≤ maximum)
    (Flow.Productive.result (R.A.readUint maximum input)) (R.A.uintReadBounded maximum input)

  signed : ∀ input → S.Ensures P.I64.InRange (Flow.Productive.result (R.A.readSigned input))
  signed input = Transfer.fromSuccess P.I64.InRange
    (Flow.Productive.result (R.A.readSigned input)) (R.A.signedReadBounded input)

  text : ∀ input → S.Ensures Unicode.Valid (Flow.Productive.result (R.A.readText input))
  text input = Transfer.implies
    (ScalarUnicode.ParserFor.Admitted checks Atoms.text) Unicode.Valid
    (λ checks₁ ((scalar , valid , observed)) →
       textValue scalar valid checks₁ observed)
    (Flow.Productive.result (R.A.readText input))
    (ScalarUnicode.ParserFor.read checks Atoms.text
     Atoms.stringExpected input)

  recordValue : ∀ {Value} fields (build : Sequence.Values fields → Value) readers
    (properties : I.Predicates fields) (property : Value → Set) →
    (∀ allowance index input → S.Ensures (properties index)
      (Flow.Productive.result (Slots.readerAt fields index (readers allowance) input))) →
    I.Defaults fields properties →
    (∀ values → I.Valid fields properties values → property (build (Slots.toSequence fields values))) →
    ∀ allowance input → S.Ensures property (Flow.Productive.result (R.readRecord fields build readers allowance input))
  recordValue fields build readers properties property readersValid defaults buildValid allowance input =
    S.map (I.Valid fields properties) property (λ values → build (Slots.toSequence fields values)) buildValid
      (Flow.Productive.result (Reader.Parser.read checks fields readers Raw.recordExpected allowance input))
      (Record.Schema.read checks fields readers Raw.recordExpected properties readersValid defaults allowance input)

  vector : ∀ {Value} (child : ℕ → Flow.Parser Value) (property : Value → Set) →
    (∀ allowance input → S.Ensures property (Flow.Productive.result (child allowance input))) →
    ∀ allowance input → S.Ensures (All property) (Flow.Productive.result (R.vector child allowance input))
  vector child property valid allowance input = Vector.Schema.read checks _ child Raw.arrayExpected property valid allowance input

  optional : ∀ {Value} (child : Flow.Parser Value) (property : Value → Set) →
    (∀ input → S.Ensures property (Flow.Productive.result (child input))) →
    ∀ input → S.Ensures (Bounds.Optional property) (Flow.Productive.result (Optional.read child input))
  optional child property valid input = Transfer.implies (MaybeAll.All property) (Bounds.Optional property)
    (λ value → optionalValue) (Flow.Productive.result (Optional.read child input))
    (Option.Child.read _ child property valid input)
