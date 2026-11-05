{-# OPTIONS --safe #-}
-- Every string returned by scalar token parsing consists of Unicode scalars.
import Mimir.FloatConversion
module Mimir.SerdeScalarUnicode (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Bool using (true; false)
open import Data.Fin using (#_)
open import Data.List using ([]; _∷_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Mimir.SerdeScalar as ScalarDependency
private
  module Scalar = ScalarDependency floatConversion
import Mimir.SerdeFlow as Flow
import Mimir.SerdeSuccess as S
import Mimir.SerdeParserInvariant as ParserDependency
private
  module Parser = ParserDependency floatConversion
import Mimir.SerdeOptionInvariant as OptionDependency
private
  module Option = OptionDependency floatConversion
import Mimir.SerdeValidateInvariant as Validation
import Mimir.JsonAtoms as AtomsDependency
private
  module Atoms = AtomsDependency floatConversion
import Mimir.JsonTreeParser as TokensDependency
private
  module Tokens = TokensDependency floatConversion
import Mimir.JsonString as String
import Mimir.DecodedText as Decoded
import Mimir.UnicodeText as Unicode
import Mimir.SignedMachine as Machine
import Mimir.Validation as V

Valid : Scalar.Scalar → Set
Valid Scalar.unit = ⊤
Valid (Scalar.boolean value) = ⊤
Valid (Scalar.number value) = ⊤
Valid (Scalar.string value) = Unicode.Valid value

module ParserFor (checks : Machine.OverflowChecks) where
  private
    module R = Scalar.Parser checks

  dispatch : ∀ failure input → S.Ensures Valid
    (Flow.Productive.result (R.dispatch failure input))
  dispatch failure [] = tt
  dispatch failure input@(byte ∷ rest) with Tokens.classify byte
  ... | Tokens.nullToken = Option.literal Valid Scalar.unit tt byte
    (# 117 ∷ # 108 ∷ # 108 ∷ []) rest
  ... | Tokens.trueToken = Option.literal Valid (Scalar.boolean true) tt byte
    (# 114 ∷ # 117 ∷ # 101 ∷ []) rest
  ... | Tokens.falseToken = Option.literal Valid (Scalar.boolean false) tt byte
    (# 97 ∷ # 108 ∷ # 115 ∷ # 101 ∷ []) rest
  ... | Tokens.numberToken = S.map (λ _ → ⊤) Valid Scalar.number (λ value _ → tt)
    (Flow.Productive.result
     (Flow.fromJsonProductive
      (Atoms.Numbers.number checks (byte ∷ rest))))
    (S.trivial
     (Flow.Productive.result
      (Flow.fromJsonProductive
       (Atoms.Numbers.number checks (byte ∷ rest)))))
  ... | Tokens.stringToken = S.map (λ _ → ⊤) Valid
    (λ value → Scalar.string (Decoded.text (String.values value)))
    (λ value _ → Decoded.valid (String.values value))
    (Flow.Productive.result
     (Flow.fromJsonProductive (Atoms.string (byte ∷ rest))))
    (S.trivial
     (Flow.Productive.result
      (Flow.fromJsonProductive (Atoms.string (byte ∷ rest)))))
  ... | Tokens.arrayToken = tt
  ... | Tokens.objectToken = tt
  ... | Tokens.invalidToken = tt

  raw : ∀ failure input → S.Ensures Valid
    (Flow.Productive.result (R.raw failure input))
  raw failure input = Parser.whitespace Valid (R.dispatch failure) (dispatch failure)
    input

  Admitted : ∀ {Value} → (Scalar.Scalar → V.Fault ⊎ Value) → Value → Set
  Admitted check value = Σ Scalar.Scalar (λ scalar → Valid scalar × check scalar ≡ inj₂ value)

  read : ∀ {Value} (check : Scalar.Scalar → V.Fault ⊎ Value) failure input →
    S.Ensures (Admitted check) (Flow.Productive.result (R.read check failure input))
  read check failure input = Validation.validate Valid (Admitted check) check
    (λ scalar valid value selected → scalar , valid , selected)
    (R.raw failure input) (raw failure input)
