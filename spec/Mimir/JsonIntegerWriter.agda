{-# OPTIONS --safe #-}
-- Canonical JSON decimal spelling for every integer, including signed minimum
-- magnitudes. Negative zero and a leading plus are never introduced.
module Mimir.JsonIntegerWriter where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.Maybe using (just)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
open import Mimir.Text using (Text)
import Mimir.Unsigned as Digits
import Mimir.NatDecimal as Decimal
import Mimir.JsonNumber as JSON
import Mimir.JsonNumberCompleteness as Complete

whole : ℕ → JSON.Whole
whole zero = JSON.zero
whole (suc number) = JSON.nonzero (Decimal.Decimal.head (Decimal.encode (suc number)))
  (Decimal.positiveHead number (Decimal.encode (suc number))) (Decimal.Decimal.tail (Decimal.encode (suc number)))

wholeSpelling : ∀ number → JSON.spellWhole (whole number) ≡ Decimal.text number
wholeSpelling zero = refl
wholeSpelling (suc number) = refl

form : ℤ → JSON.Syntax
form (+ number) = JSON.unsigned , whole number , JSON.absent , JSON.absent
form (-[1+ number ]) = JSON.minus , whole (suc number) , JSON.absent , JSON.absent

text : ℤ → Text
text (+ number) = Decimal.text number
text (-[1+ number ]) = '-' ∷ Decimal.text (suc number)

spelling : ∀ number → JSON.spell (form number) ≡ text number
spelling (+ number) = trans (++-identityʳ (JSON.spellWhole (whole number))) (wholeSpelling number)
spelling (-[1+ number ]) = cong ('-' ∷_)
  (trans (++-identityʳ (JSON.spellWhole (whole (suc number)))) (wholeSpelling (suc number)))

accepted : ∀ number → Σ (JSON.Parsed (text number)) (λ parsed → JSON.parse (text number) ≡ just parsed)
accepted number = subst (λ input → Σ (JSON.Parsed input) (λ parsed → JSON.parse input ≡ just parsed))
  (spelling number) (Complete.parseComplete (form number))

data Denotes : Text → ℤ → Set where
  positive : ∀ number → Digits.Digits 0 (Decimal.text number) number → Denotes (Decimal.text number) (+ number)
  negative : ∀ number → Digits.Digits 0 (Decimal.text (suc number)) (suc number) →
    Denotes ('-' ∷ Decimal.text (suc number)) (-[1+ number ])

exactValue : ∀ number → Denotes (text number) number
exactValue (+ number) = positive number (Decimal.renderedValue number)
exactValue (-[1+ number ]) = negative number (Decimal.renderedValue (suc number))
