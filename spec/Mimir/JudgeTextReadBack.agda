{-# OPTIONS --safe #-}
-- Canonical text serialization is accepted unchanged by the raw field reader.
import Mimir.FloatConversion
module Mimir.JudgeTextReadBack (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Fin using (#_)
open import Data.List using (_∷_; _++_)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
import Mimir.JudgeStateAtoms as AtomsDependency
private
  module Atoms = AtomsDependency floatConversion
import Mimir.JsonString as String
import Mimir.JsonStringParser as Strings
import Mimir.JsonStringWriter as Writer
import Mimir.JsonTextWriter as TextWriter
import Mimir.DecodedText as Decoded
import Mimir.UnicodeText as Unicode
import Mimir.SerdeReadBack as Back
import Mimir.SerdeScalar as ScalarDependency
private
  module Scalar = ScalarDependency floatConversion
import Mimir.Validation as V
import Mimir.SignedMachine as Machine

module Parser (checks : Machine.OverflowChecks) where
  private
    module A = Atoms.Parser checks

  checkedString : ∀ {Value} (check : Scalar.Scalar → V.Fault ⊎ Value) failure input
    (parsed : Strings.Parsed ((# 34) ∷ input)) →
    Strings.parse ((# 34) ∷ input) ≡ inj₂ parsed → ∀ output →
    check (Scalar.string (Decoded.text (String.values (Strings.Parsed.value parsed)))) ≡ inj₂ output →
    Back.Returns (Scalar.Parser.read checks check failure) ((# 34) ∷ input) output (Strings.Parsed.rest parsed)
  checkedString check failure input (Strings.parsed value rest exact) selected output admitted
    rewrite selected | admitted = Back.returned _ refl refl

  checkedRoundTrip : ∀ {Value} (check : Scalar.Scalar → V.Fault ⊎ Value) failure text valid output →
    check (Scalar.string text) ≡ inj₂ output → ∀ suffix →
    Back.Returns (Scalar.Parser.read checks check failure)
      (String.spellString (String.StringValue.body (TextWriter.render text valid)) ++ suffix) output suffix
  checkedRoundTrip check failure text valid output admitted suffix
    with Writer.roundTrip (Unicode.encodeValues valid) suffix
  ... | result , selected , sameSuffix , sameCodes = Back.retarget
    (checkedString check failure
     (String.spellBody
      (String.StringValue.body (TextWriter.render text valid))
      ++ suffix)
     result selected output
     (trans
      (cong (λ text → check (Scalar.string text))
       (trans
        (TextWriter.samePoints
         (String.values (Strings.Parsed.value result))
         (Unicode.encodeValues valid) sameCodes)
        (Decoded.roundTrip valid)))
      admitted))
    refl sameSuffix

  observed : ∀ input (parsed : Strings.Parsed ((# 34) ∷ input)) →
    Strings.parse ((# 34) ∷ input) ≡ inj₂ parsed →
    Back.Returns A.readText ((# 34) ∷ input)
      (Decoded.text (String.values (Strings.Parsed.value parsed))) (Strings.Parsed.rest parsed)
  observed input (Strings.parsed value rest exact) selected rewrite selected = Back.returned _ refl refl

  roundTrip : ∀ text valid suffix → Back.Returns A.readText
    (String.spellString (String.StringValue.body (TextWriter.render text valid)) ++ suffix) text suffix
  roundTrip text valid suffix with Writer.roundTrip (Unicode.encodeValues valid) suffix
  ... | result , selected , sameSuffix , sameCodes = Back.retarget
    (observed
     (String.spellBody
      (String.StringValue.body (TextWriter.render text valid))
      ++ suffix)
     result selected)
    (trans
     (TextWriter.samePoints
      (String.values (Strings.Parsed.value result))
      (Unicode.encodeValues valid) sameCodes)
     (Decoded.roundTrip valid))
    sameSuffix
