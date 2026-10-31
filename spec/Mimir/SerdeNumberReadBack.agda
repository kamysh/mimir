{-# OPTIONS --safe #-}
-- Successful numeric conversion survives typed scalar dispatch and validation.
import Mimir.FloatConversion
module Mimir.SerdeNumberReadBack (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.List using (_∷_)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Bits using (Byte)
import Mimir.NumericTokens as Numeric
import Mimir.SerdeNumericWire as ReaderDependency
private
  module Reader = ReaderDependency floatConversion
import Mimir.SequenceReadBack as Sequence
import Mimir.SerdeReadBack as Back
import Mimir.SerdeReadBackComposition as ComposeDependency
private
  module Compose = ComposeDependency floatConversion
import Mimir.SerdeNumberStart as StartDependency
private
  module Start = StartDependency floatConversion
import Mimir.SerdeFlow as Flow
import Mimir.SerdeScalar as ScalarDependency
private
  module Scalar = ScalarDependency floatConversion
import Mimir.JsonAtoms as AtomsDependency
private
  module Atoms = AtomsDependency floatConversion
import Mimir.JsonTreeParser as TokensDependency
private
  module Tokens = TokensDependency floatConversion
import Mimir.JsonWhitespace as White
import Mimir.SignedMachine as Machine
import Mimir.Validation as V

private
  module B = Sequence.Over Byte Numeric.Code

converted : ∀ {input} {result : Reader.Bridge.B.Result Numeric.Number input} {value suffix} →
  B.Returned result value suffix → Back.Returned (Flow.fromJson (Atoms.numericResult result)) value suffix
converted B.returned = Back.returned _ refl refl

module Parser (checks : Machine.OverflowChecks) where
  dispatch : ∀ failure byte rest number suffix → Tokens.classify byte ≡ Tokens.numberToken →
    Back.Returned (Flow.fromJson (Atoms.numericResult (Reader.Parser.read checks (byte ∷ rest)))) number suffix →
    Back.Returns (Scalar.Parser.dispatch checks failure) (byte ∷ rest) (Scalar.number number) suffix
  dispatch failure byte rest number suffix classified receipt rewrite classified = Compose.map Scalar.number receipt

  checkedNumber : ∀ {Value} (check : Scalar.Scalar → V.Fault ⊎ Value) failure byte rest number suffix value →
    Tokens.classify byte ≡ Tokens.numberToken → White.Stopped (byte ∷ rest) →
    Back.Returned (Flow.fromJson (Atoms.numericResult (Reader.Parser.read checks (byte ∷ rest)))) number suffix →
    check (Scalar.number number) ≡ inj₂ value →
    Back.Returns (Scalar.Parser.read checks check failure) (byte ∷ rest) value suffix
  checkedNumber check failure byte rest number suffix value classified stopped receipt admitted = Compose.validate check
    (Scalar.Parser.raw checks failure (byte ∷ rest))
    (Compose.noWhitespace (Scalar.Parser.dispatch checks failure) byte
     rest stopped
     (dispatch failure byte rest number suffix classified receipt))
    admitted

  checked : ∀ {Value} (check : Scalar.Scalar → V.Fault ⊎ Value) failure input number suffix value →
    Start.Starts input → B.Returned (Reader.Parser.read checks input) number suffix →
    check (Scalar.number number) ≡ inj₂ value → Back.Returns (Scalar.Parser.read checks check failure) input value suffix
  checked check failure input number suffix value (Start.starts first rest refl classified) receipt admitted = checkedNumber check failure first rest number suffix value
    classified (Start.notSpace first classified) (converted receipt)
    admitted
