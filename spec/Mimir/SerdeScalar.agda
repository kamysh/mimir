{-# OPTIONS --safe #-}
-- Typed scalar dispatch retains numeric variants. Wrong container types are
-- rejected at their opening byte, without recursively parsing their contents.
import Mimir.FloatConversion
module Mimir.SerdeScalar (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Fin using (#_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.SerdeFlow as Flow
import Mimir.SerdeSuccess as Success
import Mimir.JsonAtoms as AtomsDependency
private
  module Atoms = AtomsDependency floatConversion
import Mimir.JsonTreeParser as TokensDependency
private
  module Tokens = TokensDependency floatConversion
import Mimir.JsonString as String
import Mimir.DecodedText as Decoded
import Mimir.JsonWhitespace as White
import Mimir.JsonControls as Controls
import Mimir.NumericTokens as Numeric
import Mimir.SignedMachine as Machine
import Mimir.Validation as V
module F = Flow.F

data Scalar : Set where
  unit : Scalar
  boolean : Bool → Scalar
  number : Numeric.Number → Scalar
  string : Text → Scalar

whitespace : ∀ {Value} input → Flow.Parser Value → Flow.Productive Value input
whitespace input next with White.take input
... | White.run consumed spaces remaining exact stopped with next remaining
... | Flow.productive result progress = Flow.productive (Flow.prefix before result)
    (Flow.preserveProgress before result progress)
    where before = F.cursor consumed remaining exact

module Parser (checks : Machine.OverflowChecks) where
  module N = Atoms.Numbers checks

  dispatch : V.Fault → Flow.Parser Scalar
  dispatch failure [] = Flow.productive (Flow.lift (Controls.C.fail (Controls.eofValue , Numeric.peek) [])) tt
  dispatch failure input@(byte ∷ rest) with Tokens.classify byte
  ... | Tokens.nullToken = Flow.fromJsonProductive (Atoms.literal unit byte ((# 117) ∷ (# 108) ∷ (# 108) ∷ []) rest)
  ... | Tokens.trueToken = Flow.fromJsonProductive (Atoms.literal (boolean true) byte ((# 114) ∷ (# 117) ∷ (# 101) ∷ []) rest)
  ... | Tokens.falseToken = Flow.fromJsonProductive (Atoms.literal (boolean false) byte ((# 97) ∷ (# 108) ∷ (# 115) ∷ (# 101) ∷ []) rest)
  ... | Tokens.numberToken = Flow.mapProductive number (Flow.fromJsonProductive (N.number input))
  ... | Tokens.stringToken = Flow.mapProductive (λ value → string (Decoded.text (String.values value)))
      (Flow.fromJsonProductive (Atoms.string input))
  ... | Tokens.arrayToken = Flow.productive (Flow.reject failure input) tt
  ... | Tokens.objectToken = Flow.productive (Flow.reject failure input) tt
  ... | Tokens.invalidToken = Flow.productive (Flow.lift (Controls.C.fail (Controls.expectedValue , Numeric.peek) input)) tt

  raw : V.Fault → Flow.Parser Scalar
  raw failure input = whitespace input (dispatch failure)

  read : ∀ {Value} → (Scalar → V.Fault ⊎ Value) → V.Fault → Flow.Parser Value
  read check failure input = Flow.validate check (raw failure input)

  Admitted : ∀ {Value} → (Scalar → V.Fault ⊎ Value) → Value → Set
  Admitted check value = Σ Scalar (λ scalar → check scalar ≡ inj₂ value)

  readEnsures : ∀ {Value} (check : Scalar → V.Fault ⊎ Value) failure input →
    Success.Ensures (Admitted check) (Flow.Productive.result (read check failure input))
  readEnsures check failure input = Success.validate check (Admitted check)
    (λ scalar value selected → scalar , selected) (raw failure input)

  readSound : ∀ {Value} (check : Scalar → V.Fault ⊎ Value) failure input value position →
    Flow.Productive.result (read check failure input) ≡ Flow.ordinary (F.success value position) → Admitted check value
  readSound check failure input value position observed = Success.extract (Admitted check)
    (Flow.Productive.result (read check failure input)) value position (readEnsures check failure input) observed

  rejectAll : ∀ {Value} → V.Fault → Flow.Parser Value
  rejectAll failure = read (λ scalar → inj₁ failure) failure

  rejectNeverSucceeds : ∀ {Value} failure input (value : Value) position →
    Flow.Productive.result (rejectAll failure input) ≡ Flow.ordinary (F.success value position) → ⊥
  rejectNeverSucceeds failure input value position observed
    with readSound (λ scalar → inj₁ failure) failure input value position observed
  ... | scalar , ()

  arrayNoDescent : ∀ failure byte rest → Tokens.classify byte ≡ Tokens.arrayToken →
    Flow.Productive.result (dispatch failure (byte ∷ rest)) ≡ Flow.reject failure (byte ∷ rest)
  arrayNoDescent failure byte rest classified rewrite classified = refl

  objectNoDescent : ∀ failure byte rest → Tokens.classify byte ≡ Tokens.objectToken →
    Flow.Productive.result (dispatch failure (byte ∷ rest)) ≡ Flow.reject failure (byte ∷ rest)
  objectNoDescent failure byte rest classified rewrite classified = refl
