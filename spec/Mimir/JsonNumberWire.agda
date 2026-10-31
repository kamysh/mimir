{-# OPTIONS --safe #-}
-- Byte-level transport of the independent JSON number grammar and lexer.
-- Numeric range and rounded floating conversion are separate obligations.
module Mimir.JsonNumberWire where

open import Data.Char using (Char; toℕ)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.List.Properties using (map-++)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Nat using (suc; _+_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (m≤m+n)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong; trans)
open import Mimir.Bits using (Byte)
import Mimir.Unsigned as Digit
import Mimir.JsonNumber as Number
import Mimir.JsonNumberCompleteness as Complete
import Mimir.JsonNumberSuffix as Suffix
import Mimir.ParsedPart as TextPart
import Mimir.ByteText as Wire
import Mimir.BytePart as BytePart

abstract
  belowPadding : ∀ number extra → number < suc (number + extra)
  belowPadding number extra = s≤s (m≤m+n number extra)

digitBounded : ∀ digit → Wire.Bounded (Digit.character digit)
digitBounded Digit.d0 = belowPadding 48 207
digitBounded Digit.d1 = belowPadding 49 206
digitBounded Digit.d2 = belowPadding 50 205
digitBounded Digit.d3 = belowPadding 51 204
digitBounded Digit.d4 = belowPadding 52 203
digitBounded Digit.d5 = belowPadding 53 202
digitBounded Digit.d6 = belowPadding 54 201
digitBounded Digit.d7 = belowPadding 55 200
digitBounded Digit.d8 = belowPadding 56 199
digitBounded Digit.d9 = belowPadding 57 198

digitsBounded : ∀ digits → All Wire.Bounded (map Digit.character digits)
digitsBounded [] = All.[]
digitsBounded (digit ∷ rest) = digitBounded digit All.∷ digitsBounded rest

signBounded : ∀ sign → All Wire.Bounded (Number.spellSign sign)
signBounded Number.unsigned = All.[]
signBounded Number.minus = belowPadding 45 210 All.∷ All.[]

wholeBounded : ∀ whole → All Wire.Bounded (Number.spellWhole whole)
wholeBounded Number.zero = digitBounded Digit.d0 All.∷ All.[]
wholeBounded (Number.nonzero head notZero tail) = digitBounded head All.∷ digitsBounded tail

fractionBounded : ∀ fraction → All Wire.Bounded (Number.spellFraction fraction)
fractionBounded Number.absent = All.[]
fractionBounded (Number.fraction (head , tail)) = belowPadding 46 209 All.∷ digitBounded head All.∷ digitsBounded tail

exponentSignBounded : ∀ sign → All Wire.Bounded (Number.spellExponentSign sign)
exponentSignBounded Number.implicit = All.[]
exponentSignBounded Number.plus = belowPadding 43 212 All.∷ All.[]
exponentSignBounded Number.minus = belowPadding 45 210 All.∷ All.[]

markerBounded : ∀ marker → Wire.Bounded (Number.marker marker)
markerBounded Number.lower = belowPadding 101 154
markerBounded Number.upper = belowPadding 69 186

exponentBounded : ∀ exponent → All Wire.Bounded (Number.spellExponent exponent)
exponentBounded Number.absent = All.[]
exponentBounded (Number.exponent marker sign (head , tail)) =
  markerBounded marker All.∷ ++⁺ (exponentSignBounded sign) (digitBounded head All.∷ digitsBounded tail)

bounded : ∀ form → All Wire.Bounded (Number.spell form)
bounded (sign , whole , frac , expo) = ++⁺ (signBounded sign)
  (++⁺ (wholeBounded whole) (++⁺ (fractionBounded frac) (exponentBounded expo)))

module Prefix = BytePart.Lift Number.Syntax Number.spell bounded

spell : Number.Syntax → List Byte
spell = Prefix.spelling

read : ∀ input → Maybe (Prefix.Part input)
read = Prefix.parse Number.read

readComplete : ∀ form → Σ (Prefix.Part (spell form)) (λ result →
  read (spell form) ≡ just result × Prefix.Part.rest result ≡ [])
readComplete form = Prefix.successPreserved Number.read (spell form) []
  (subst (λ input → TextPart.Succeeded Number.read input []) (sym (Prefix.spellingText form)) (Complete.readComplete form))

readSuffixComplete : ∀ form rest → Suffix.Terminal (Wire.text rest) →
  Σ (Prefix.Part (spell form ++ rest)) (λ result →
    read (spell form ++ rest) ≡ just result × Prefix.Part.rest result ≡ rest)
readSuffixComplete form rest terminal = Prefix.successPreserved Number.read (spell form ++ rest) rest
  (subst (λ input → TextPart.Succeeded Number.read input (Wire.text rest))
    (sym (trans (map-++ Wire.character (spell form) rest) (cong (_++ Wire.text rest) (Prefix.spellingText form))))
    (Suffix.readComplete form (Wire.text rest) terminal))

spellPositive : ∀ form → 1 ≤ length (spell form)
spellPositive (Number.minus , whole , frac , expo) = s≤s z≤n
spellPositive (Number.unsigned , Number.zero , frac , expo) = s≤s z≤n
spellPositive (Number.unsigned , Number.nonzero head notZero tail , frac , expo) = s≤s z≤n
