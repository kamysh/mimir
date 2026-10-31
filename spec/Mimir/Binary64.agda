{-# OPTIONS --safe #-}
-- Exact interpretation of binary64 inputs. This module deliberately does not
-- equate rounded floating arithmetic with rational arithmetic. Rounding and
-- transcendental operations require their own contracts.
module Mimir.Binary64 where

open import Data.Fin using (Fin; toℕ)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _<_; _<?_; _≤?_)
open import Data.Nat.Properties using (*-suc)
open import Data.Integer using (+_)
open import Data.Rational using (ℚ; _/_; -_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; sym)

data Sign : Set where positive negative : Sign

record Word : Set where
  constructor bits
  field
    sign : Sign
    exponent : Fin 2048
    fraction : Fin 4503599627370496
open Word

Finite : Word → Set
Finite w = toℕ (exponent w) < 2047

finite? : ∀ w → Dec (Finite w)
finite? w = toℕ (exponent w) <? 2047

-- Writing a power of two as suc n makes positivity structural, including for
-- denominators of subnormal values. There is no nonzero-denominator axiom.
powerMinusOne : ℕ → ℕ
powerMinusOne zero = zero
powerMinusOne (suc n) = suc (2 * powerMinusOne n)

power : ℕ → ℕ
power n = suc (powerMinusOne n)

powerStep : ∀ n → power (suc n) ≡ 2 * power n
powerStep n = sym (*-suc 2 (powerMinusOne n))

scaleWith : ℕ → ℕ → ℕ → ℚ
scaleWith threshold mantissa exponent with exponent ≤? threshold
... | yes _ = (+ mantissa) / power (threshold ∸ exponent)
... | no _ = (+ (mantissa * power (exponent ∸ threshold))) / 1

scaled : ℕ → ℕ → ℚ
scaled mantissa zero = scaleWith 1075 mantissa zero
scaled mantissa (suc exponent) = scaleWith 1074 mantissa exponent

unsignedAt : ℕ → ℕ → ℕ → ℕ → ℚ
unsignedAt threshold base zero fraction = scaleWith threshold fraction zero
unsignedAt threshold base (suc exponent) fraction = scaleWith threshold (base + fraction) exponent

unsignedValue : Word → ℚ
unsignedValue w = unsignedAt 1074 4503599627370496 (toℕ (exponent w)) (toℕ (fraction w))

-- A second, common-unit representation makes order and rounding obligations
-- integral: every finite binary64 number is an integer multiple of 2^-1074.
-- This is a numeric carrier helper. The obsolete standalone dyadic/rounding
-- proofs were removed; no equivalence theorem is claimed here.
unitsAt : ℕ → ℕ → ℕ → ℕ
unitsAt base zero fraction = fraction
unitsAt base (suc exponent) fraction = (base + fraction) * power exponent

units : Word → ℕ
units w = unitsAt 4503599627370496 (toℕ (exponent w)) (toℕ (fraction w))

applySign : Sign → ℚ → ℚ
applySign positive value = value
applySign negative value = - value

record FiniteNumber : Set where
  constructor finiteNumber
  field word : Word; finite : Finite word

value : FiniteNumber → ℚ
value f = applySign (sign (FiniteNumber.word f)) (unsignedValue (FiniteNumber.word f))

-- A rejected nonfinite number retains its bits for diagnostics/serialization.
-- The nonfinite branch includes both infinities and all NaN payloads.
data Number : Set where
  finite : FiniteNumber → Number
  nonfinite : (word : Word) → (Finite word → ⊥) → Number

decode : Word → Number
decode w with finite? w
... | yes proof = finite (finiteNumber w proof)
... | no refutation = nonfinite w refutation

IsFinite : Number → Set
IsFinite (finite _) = ⊤
IsFinite (nonfinite _ _) = ⊥

isFinite? : (number : Number) → Dec (IsFinite number)
isFinite? (finite _) = yes tt
isFinite? (nonfinite _ _) = no (λ proof → proof)
