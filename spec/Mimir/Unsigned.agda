{-# OPTIONS --safe #-}
-- Unsigned decimal fields used by CLI/configuration. Accept an optional leading
-- '+', require at least one ASCII digit, preserve the target integer bound,
-- and reject whitespace, signs in the body, and arithmetic overflow.
module Mimir.Unsigned where

open import Data.Char using (Char; _≟_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _+_; _*_; _≤_; _≤?_; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n)
open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Mimir.Text using (Text)

data Digit : Set where d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 : Digit

character : Digit → Char
character d0 = '0'
character d1 = '1'
character d2 = '2'
character d3 = '3'
character d4 = '4'
character d5 = '5'
character d6 = '6'
character d7 = '7'
character d8 = '8'
character d9 = '9'

value : Digit → ℕ
value d0 = 0
value d1 = 1
value d2 = 2
value d3 = 3
value d4 = 4
value d5 = 5
value d6 = 6
value d7 = 7
value d8 = 8
value d9 = 9

record ReadDigit (input : Char) : Set where
  constructor readDigit
  field digit : Digit; spelling : input ≡ character digit

findDigit : (input : Char) → List Digit → Maybe (ReadDigit input)
findDigit input [] = nothing
findDigit input (d ∷ ds) with input ≟ character d
... | yes same = just (readDigit d same)
... | no _ = findDigit input ds

decodeDigit : (input : Char) → Maybe (ReadDigit input)
decodeDigit input = findDigit input (d0 ∷ d1 ∷ d2 ∷ d3 ∷ d4 ∷ d5 ∷ d6 ∷ d7 ∷ d8 ∷ d9 ∷ [])

record UInt (maximum : ℕ) : Set where
  constructor uint
  field number : ℕ; bounded : number ≤ maximum

data Digits : ℕ → Text → ℕ → Set where
  end : ∀ n → Digits n [] n
  next : ∀ {before c cs after} (d : Digit) → c ≡ character d →
    Digits (10 * before + value d) cs after → Digits before (c ∷ cs) after

record Parsed (maximum start : ℕ) (input : Text) : Set where
  constructor parsed
  field result : UInt maximum; interpretation : Digits start input (UInt.number result)

data Error : Set where empty invalidDigit overflow : Error

consume : ∀ maximum (before : UInt maximum) (input : Text) →
  Error ⊎ Parsed maximum (UInt.number before) input
consume maximum before [] = inj₂ (parsed before (end (UInt.number before)))
consume maximum before (c ∷ cs) with decodeDigit c
... | nothing = inj₁ invalidDigit
... | just (readDigit d same) with (10 * UInt.number before + value d) ≤? maximum
...   | no _ = inj₁ overflow
...   | yes within with consume maximum (uint (10 * UInt.number before + value d) within) cs
...     | inj₁ error = inj₁ error
...     | inj₂ (parsed result interpretation) = inj₂ (parsed result (next d same interpretation))

data NonemptyDigits : Text → ℕ → Set where
  digits : ∀ c cs n → Digits 0 (c ∷ cs) n → NonemptyDigits (c ∷ cs) n

data Syntax : Text → ℕ → Set where
  plain : ∀ {text n} → NonemptyDigits text n → Syntax text n
  plus : ∀ {text n} → NonemptyDigits text n → Syntax ('+' ∷ text) n

record Number (maximum : ℕ) (input : Text) : Set where
  constructor numeric
  field result : UInt maximum; wellFormed : Syntax input (UInt.number result)

nonemptyBody : ∀ maximum input → Error ⊎ Σ (UInt maximum) (λ n → NonemptyDigits input (UInt.number n))
nonemptyBody maximum [] = inj₁ empty
nonemptyBody maximum (c ∷ cs) with consume maximum (uint 0 z≤n) (c ∷ cs)
... | inj₁ error = inj₁ error
... | inj₂ (parsed result interpretation) = inj₂ (result , digits c cs (UInt.number result) interpretation)

parse : ∀ maximum input → Error ⊎ Number maximum input
parse maximum [] = inj₁ empty
parse maximum (c ∷ cs) with c ≟ '+'
... | yes refl with nonemptyBody maximum cs
...   | inj₁ error = inj₁ error
...   | inj₂ (result , proof) = inj₂ (numeric result (plus proof))
parse maximum (c ∷ cs) | no _ with nonemptyBody maximum (c ∷ cs)
... | inj₁ error = inj₁ error
... | inj₂ (result , proof) = inj₂ (numeric result (plain proof))

parsedWithinBound : ∀ {maximum input} (result : Number maximum input) →
  UInt.number (Number.result result) ≤ maximum
parsedWithinBound result = UInt.bounded (Number.result result)

parsedHasDecimalInterpretation : ∀ {maximum input} (result : Number maximum input) →
  Syntax input (UInt.number (Number.result result))
parsedHasDecimalInterpretation result = Number.wellFormed result

decodeComplete : ∀ d → decodeDigit (character d) ≡ just (readDigit d refl)
decodeComplete d0 = refl
decodeComplete d1 = refl
decodeComplete d2 = refl
decodeComplete d3 = refl
decodeComplete d4 = refl
decodeComplete d5 = refl
decodeComplete d6 = refl
decodeComplete d7 = refl
decodeComplete d8 = refl
decodeComplete d9 = refl

digitNotPlus : ∀ d → character d ≢ '+'
digitNotPlus d0 ()
digitNotPlus d1 ()
digitNotPlus d2 ()
digitNotPlus d3 ()
digitNotPlus d4 ()
digitNotPlus d5 ()
digitNotPlus d6 ()
digitNotPlus d7 ()
digitNotPlus d8 ()
digitNotPlus d9 ()

digitNotMinus : ∀ d → character d ≢ '-'
digitNotMinus d0 ()
digitNotMinus d1 ()
digitNotMinus d2 ()
digitNotMinus d3 ()
digitNotMinus d4 ()
digitNotMinus d5 ()
digitNotMinus d6 ()
digitNotMinus d7 ()
digitNotMinus d8 ()
digitNotMinus d9 ()

zeroOnly : ∀ d → character d ≡ '0' → d ≡ d0
zeroOnly d0 same = refl
zeroOnly d1 ()
zeroOnly d2 ()
zeroOnly d3 ()
zeroOnly d4 ()
zeroOnly d5 ()
zeroOnly d6 ()
zeroOnly d7 ()
zeroOnly d8 ()
zeroOnly d9 ()

-- Prefix overflow cannot occur on the way to an in-range unsigned result.
-- This argument needs decimal monotonicity, not an assumption about input size.
stepMonotone : ∀ n d → n ≤ 10 * n + value d
stepMonotone n d = ≤-trans (m≤m+n n (9 * n)) (m≤m+n (10 * n) (value d))

digitsMonotone : ∀ {before text after} → Digits before text after → before ≤ after
digitsMonotone (end n) = ≤-refl
digitsMonotone (next {before} d same rest) = ≤-trans (stepMonotone before d) (digitsMonotone rest)

consumeComplete : ∀ maximum before input final →
  Digits (UInt.number before) input final → final ≤ maximum →
  Σ (Parsed maximum (UInt.number before) input) (λ result → consume maximum before input ≡ inj₂ result)
consumeComplete maximum before [] .(UInt.number before) (end .(UInt.number before)) bounded =
  parsed before (end (UInt.number before)) , refl
consumeComplete maximum before .(character d ∷ _) final (next d refl rest) bounded
  rewrite decodeComplete d with (10 * UInt.number before + value d) ≤? maximum
... | no impossible = ⊥-elim (impossible (≤-trans (digitsMonotone rest) bounded))
... | yes within with consumeComplete maximum (uint (10 * UInt.number before + value d) within) _ final rest bounded
...   | parsed result interpretation , equation rewrite equation =
  parsed result (next d refl interpretation) , refl

bodyComplete : ∀ maximum input final → NonemptyDigits input final → final ≤ maximum →
  Σ (Σ (UInt maximum) (λ n → NonemptyDigits input (UInt.number n)))
    (λ result → nonemptyBody maximum input ≡ inj₂ result)
bodyComplete maximum .(c ∷ cs) final (digits c cs .final grammar) bounded
  with consumeComplete maximum (uint 0 z≤n) (c ∷ cs) final grammar bounded
... | parsed result interpretation , equation rewrite equation =
  (result , digits c cs (UInt.number result) interpretation) , refl

parseComplete : ∀ maximum input final → Syntax input final → final ≤ maximum →
  Σ (Number maximum input) (λ result → parse maximum input ≡ inj₂ result)
parseComplete maximum .(character d ∷ cs) final
  (plain (digits .(character d) cs .final (next d refl grammar))) bounded
  with character d ≟ '+'
... | yes impossible = ⊥-elim (digitNotPlus d impossible)
... | no notPlus with bodyComplete maximum (character d ∷ cs) final
  (digits (character d) cs final (next d refl grammar)) bounded
...   | (result , interpretation) , equation rewrite equation = numeric result (plain interpretation) , refl
parseComplete maximum .('+' ∷ input) final (plus {input} body) bounded with '+' ≟ '+'
... | no impossible = ⊥-elim (impossible refl)
... | yes refl with bodyComplete maximum input final body bounded
...   | (result , interpretation) , equation rewrite equation = numeric result (plus interpretation) , refl
