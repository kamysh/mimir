{-# OPTIONS --safe #-}
-- RFC 8259 numeric form, independent of numeric range/conversion. Parsed
-- results carry an exact reconstruction by the independent form datatype.
module Mimir.JsonNumber where

open import Data.Char using (Char; _≟_)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (++-identityʳ; ∷-injectiveˡ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym)
open import Mimir.Text using (Text)
open import Mimir.ParsedPart using (Part; part; pairSpelling; join; sequence)
import Mimir.Unsigned as D
import Mimir.DecimalLexer as Digits

data Sign : Set where unsigned minus : Sign
data Whole : Set where
  zero : Whole
  nonzero : (head : D.Digit) → head ≢ D.d0 → List D.Digit → Whole

NonemptyDigits = D.Digit × List D.Digit

data Fraction : Set where absent : Fraction; fraction : NonemptyDigits → Fraction
data Marker : Set where lower upper : Marker
data ExponentSign : Set where implicit plus minus : ExponentSign
data Exponent : Set where absent : Exponent; exponent : Marker → ExponentSign → NonemptyDigits → Exponent

spellSign : Sign → Text
spellSign unsigned = []
spellSign minus = '-' ∷ []

spellWhole : Whole → Text
spellWhole zero = '0' ∷ []
spellWhole (nonzero head notZero tail) = D.character head ∷ map D.character tail

spellDigits : NonemptyDigits → Text
spellDigits (head , tail) = D.character head ∷ map D.character tail

spellFraction : Fraction → Text
spellFraction absent = []
spellFraction (fraction digits) = '.' ∷ spellDigits digits

marker : Marker → Char
marker lower = 'e'
marker upper = 'E'

spellExponentSign : ExponentSign → Text
spellExponentSign implicit = []
spellExponentSign plus = '+' ∷ []
spellExponentSign minus = '-' ∷ []

spellExponent : Exponent → Text
spellExponent absent = []
spellExponent (exponent e sign digits) = marker e ∷ (spellExponentSign sign ++ spellDigits digits)

Syntax = Sign × (Whole × (Fraction × Exponent))

spell : Syntax → Text
spell = pairSpelling spellSign (pairSpelling spellWhole (pairSpelling spellFraction spellExponent))

readSign : (input : Text) → Part Sign spellSign input
readSign [] = part unsigned [] refl
readSign (c ∷ cs) with c ≟ '-'
... | yes refl = part minus cs refl
... | no _ = part unsigned (c ∷ cs) refl

readWhole : (input : Text) → Maybe (Part Whole spellWhole input)
readWhole [] = nothing
readWhole (c ∷ cs) with c ≟ '0'
... | yes refl = just (part zero cs refl)
... | no notZero with Digits.classify c
...   | no _ = nothing
...   | yes (head , same) with Digits.take cs
...     | Digits.run tail rest reconstruct stopped = just
  (part (nonzero head (λ { refl → notZero same }) tail) rest
    (trans (cong (_∷ cs) same) (cong (D.character head ∷_) reconstruct)))

readDigits : (input : Text) → Maybe (Part NonemptyDigits spellDigits input)
readDigits input with Digits.take input
... | Digits.run [] rest reconstruct stopped = nothing
... | Digits.run (head ∷ tail) rest reconstruct stopped = just (part (head , tail) rest reconstruct)

readFraction : (input : Text) → Maybe (Part Fraction spellFraction input)
readFraction [] = just (part absent [] refl)
readFraction (c ∷ cs) with c ≟ '.'
... | no _ = just (part absent (c ∷ cs) refl)
... | yes refl with readDigits cs
...   | nothing = nothing
...   | just (part digits rest reconstruct) = just (part (fraction digits) rest (cong ('.' ∷_) reconstruct))

readExponentSign : (input : Text) → Part ExponentSign spellExponentSign input
readExponentSign [] = part implicit [] refl
readExponentSign (c ∷ cs) with c ≟ '+'
... | yes refl = part plus cs refl
... | no _ with c ≟ '-'
...   | yes refl = part minus cs refl
...   | no _ = part implicit (c ∷ cs) refl

readExponentBody : (e : Marker) (input : Text) → Maybe (Part Exponent spellExponent (marker e ∷ input))
readExponentBody e input with sequence (λ input → just (readExponentSign input)) readDigits input
... | nothing = nothing
... | just (part (sign , body) rest reconstruct) = just
  (part (exponent e sign body) rest (cong (marker e ∷_) reconstruct))

readExponent : (input : Text) → Maybe (Part Exponent spellExponent input)
readExponent [] = just (part absent [] refl)
readExponent (c ∷ cs) with c ≟ 'e'
... | yes refl = readExponentBody lower cs
... | no _ with c ≟ 'E'
...   | yes refl = readExponentBody upper cs
...   | no _ = just (part absent (c ∷ cs) refl)

read : (input : Text) → Maybe (Part Syntax spell input)
read = sequence (λ input → just (readSign input)) (sequence readWhole (sequence readFraction readExponent))

record Parsed (input : Text) : Set where
  constructor parsed
  field form : Syntax; exact : input ≡ spell form

parse : (input : Text) → Maybe (Parsed input)
parse input with read input
... | nothing = nothing
... | just (part form [] reconstruct) = just (parsed form (trans reconstruct (++-identityʳ (spell form))))
... | just (part form (_ ∷ _) reconstruct) = nothing

wholeCannotBeginWithPlus : ∀ whole tail rest → spellWhole whole ++ tail ≢ '+' ∷ rest
wholeCannotBeginWithPlus zero tail rest ()
wholeCannotBeginWithPlus (nonzero head notZero digits) tail rest same = D.digitNotPlus head (∷-injectiveˡ same)

syntaxCannotBeginWithPlus : ∀ form rest → spell form ≢ '+' ∷ rest
syntaxCannotBeginWithPlus (unsigned , whole , frac , expo) rest =
  wholeCannotBeginWithPlus whole (spellFraction frac ++ spellExponent expo) rest
syntaxCannotBeginWithPlus (minus , whole , frac , expo) rest ()

leadingPlusRefused : ∀ rest → Parsed ('+' ∷ rest) → ⊥
leadingPlusRefused rest (parsed form exact) = syntaxCannotBeginWithPlus form rest (sym exact)
