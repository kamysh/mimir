{-# OPTIONS --safe #-}
-- Independent JSON string escape grammar. Spelling starts immediately after
-- the initial backslash; a surrogate pair includes its second backslash.
module Mimir.JsonEscape where

open import Data.Fin using (Fin; #_; toℕ; _≟_)
open import Data.Fin.Properties using (toℕ<n)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Nat using (ℕ; _+_; _*_; _∸_; _≤_; _<_; s≤s⁻¹)
open import Data.Nat.Properties using (<-≤-trans; m≤m+n)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Sum using (inj₁)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Mimir.Bits using (Byte)
import Mimir.HexEscape as Hex
import Mimir.UTF16Escape as U
import Mimir.UnicodeScalar as Number

data Short : Set where
  quotation backslash slash backspace formfeed newline carriageReturn tab : Short

marker : Short → Byte
marker quotation = # 34
marker backslash = # 92
marker slash = # 47
marker backspace = # 98
marker formfeed = # 102
marker newline = # 110
marker carriageReturn = # 114
marker tab = # 116

ascii : Short → Fin 128
ascii quotation = # 34
ascii backslash = # 92
ascii slash = # 47
ascii backspace = # 8
ascii formfeed = # 12
ascii newline = # 10
ascii carriageReturn = # 13
ascii tab = # 9

record ReadShort (input : Byte) : Set where
  constructor readShort
  field escape : Short; spelling : input ≡ marker escape

find : ∀ input candidates → Dec (Any (λ escape → input ≡ marker escape) candidates)
find input [] = no (λ ())
find input (escape ∷ rest) with input ≟ marker escape
... | yes same = yes (here same)
... | no different with find input rest
...   | yes found = yes (there found)
...   | no missing = no λ { (here same) → different same ; (there found) → missing found }

extract : ∀ {input candidates} → Any (λ escape → input ≡ marker escape) candidates → ReadShort input
extract {candidates = escape ∷ rest} (here same) = readShort escape same
extract (there found) = extract found

candidates : List Short
candidates = quotation ∷ backslash ∷ slash ∷ backspace ∷ formfeed ∷ newline ∷ carriageReturn ∷ tab ∷ []

included : ∀ escape → Any (λ candidate → marker escape ≡ marker candidate) candidates
included quotation = here refl
included backslash = there (here refl)
included slash = there (there (here refl))
included backspace = there (there (there (here refl)))
included formfeed = there (there (there (there (here refl))))
included newline = there (there (there (there (there (here refl)))))
included carriageReturn = there (there (there (there (there (there (here refl))))))
included tab = there (there (there (there (there (there (there (here refl)))))))

read : ∀ input → Dec (ReadShort input)
read input with find input candidates
... | yes found = yes (extract found)
... | no missing = no λ { (readShort escape refl) → missing (included escape) }

readComplete : ∀ escape → read (marker escape) ≡ yes (readShort escape refl)
readComplete quotation = refl
readComplete backslash = refl
readComplete slash = refl
readComplete backspace = refl
readComplete formfeed = refl
readComplete newline = refl
readComplete carriageReturn = refl
readComplete tab = refl

data Raw : Set where
  short : Short → Raw
  unit : Hex.Four → Raw
  pair : Hex.Four → Hex.Four → Raw

Valid : Raw → Set
Valid (short escape) = ⊤
Valid (unit digits) = Number.Valid (U.value (Hex.unit digits))
Valid (pair first second) = U.Leading (U.value (Hex.unit first)) × U.Trailing (U.value (Hex.unit second))

spell : Raw → List Byte
spell (short escape) = marker escape ∷ []
spell (unit digits) = (# 117) ∷ Hex.spell digits
spell (pair first second) = (# 117) ∷ (Hex.spell first ++ ((# 92) ∷ (# 117) ∷ Hex.spell second))

number : Raw → ℕ
number (short escape) = toℕ (ascii escape)
number (unit digits) = U.value (Hex.unit digits)
number (pair first second) = ((U.value (Hex.unit first) ∸ 55296) * 1024 +
  (U.value (Hex.unit second) ∸ 56320)) + 65536

abstract
  padding : ∀ number extra → number ≤ number + extra
  padding = m≤m+n

  asciiValid : ∀ (value : Fin 128) → Number.Valid (toℕ value)
  asciiValid value = s≤s⁻¹ (<-≤-trans (toℕ<n {128} value) (padding 128 1113984)) ,
    inj₁ (<-≤-trans (toℕ<n {128} value) (padding 128 55168))

numberValid : ∀ raw → Valid raw → Number.Valid (number raw)
numberValid (short escape) valid = asciiValid (ascii escape)
numberValid (unit digits) valid = valid
numberValid (pair first second) (leading , trailing) =
  subst Number.Valid (U.pairFormula (U.value (Hex.unit first)) leading (U.value (Hex.unit second)) trailing)
    (U.pairValid (U.leadingBits (U.value (Hex.unit first)) leading) (U.trailingBits (U.value (Hex.unit second)) trailing))

encode : ∀ raw → Valid raw → Number.Encoded (number raw)
encode raw valid = Number.encode (number raw) (numberValid raw valid)
