{-# OPTIONS --safe #-}
module Mimir.JsonNumberCompleteness where

open import Data.Char using (Char; _≟_)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (++-identityʳ)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; subst; trans)
open import Mimir.Text using (Text)
open import Mimir.ParsedPart
open import Mimir.JsonNumber
import Mimir.Unsigned as D
import Mimir.DecimalLexer as Digits

digitsComplete : ∀ head tail rest → Digits.Stopped rest →
  Succeeded readDigits (spellDigits (head , tail) ++ rest) rest
digitsComplete head tail rest terminal with Digits.take (spellDigits (head , tail) ++ rest) |
  Digits.complete (head ∷ tail) rest terminal
... | Digits.run [] suffix reconstruct stopped | () , sameSuffix
... | Digits.run (d ∷ ds) suffix reconstruct stopped | sameDigits , sameSuffix =
  part (d , ds) suffix reconstruct , refl , sameSuffix

digitsAtEnd : ∀ head tail → Succeeded readDigits (spellDigits (head , tail)) []
digitsAtEnd head tail = subst (λ input → Succeeded readDigits input [])
  (++-identityʳ (spellDigits (head , tail))) (digitsComplete head tail [] tt)

wholeComplete : ∀ whole rest → Digits.Stopped rest →
  Succeeded readWhole (spellWhole whole ++ rest) rest
wholeComplete zero rest terminal = part zero rest refl , refl , refl
wholeComplete (nonzero head notZero tail) rest terminal with D.character head ≟ '0'
... | yes same = ⊥-elim (notZero (D.zeroOnly head same))
... | no different rewrite Digits.classifyComplete head
  with Digits.take (map D.character tail ++ rest) | Digits.complete tail rest terminal
... | Digits.run digits suffix reconstruct stopped | sameDigits , sameSuffix =
  part (nonzero head (λ { refl → different refl }) digits) suffix
    (cong (D.character head ∷_) reconstruct) , refl , sameSuffix

exponentSignComplete : ∀ sign head tail →
  Succeeded (λ input → just (readExponentSign input))
    (spellExponentSign sign ++ spellDigits (head , tail)) (spellDigits (head , tail))
exponentSignComplete plus head tail = part plus (spellDigits (head , tail)) refl , refl , refl
exponentSignComplete minus head tail = part minus (spellDigits (head , tail)) refl , refl , refl
exponentSignComplete implicit head tail with D.character head ≟ '+'
... | yes same = ⊥-elim (D.digitNotPlus head same)
... | no _ with D.character head ≟ '-'
...   | yes same = ⊥-elim (D.digitNotMinus head same)
...   | no _ = part implicit (spellDigits (head , tail)) refl , refl , refl

exponentBodyComplete : ∀ e sign head tail →
  Σ[ result ∈ Part Exponent spellExponent
    (marker e ∷ (spellExponentSign sign ++ spellDigits (head , tail))) ]
    (readExponentBody e (spellExponentSign sign ++ spellDigits (head , tail)) ≡ just result ×
      Part.rest result ≡ [])
exponentBodyComplete e sign head tail with sequenceComplete
  (λ input → just (readExponentSign input)) readDigits
  (spellExponentSign sign ++ spellDigits (head , tail)) (spellDigits (head , tail)) []
  (exponentSignComplete sign head tail) (digitsAtEnd head tail)
... | part (parsedSign , parsedDigits) rest reconstruct , equation , sameRest
  rewrite equation = part (exponent e parsedSign parsedDigits) rest
    (cong (marker e ∷_) reconstruct) , refl , sameRest

exponentComplete : ∀ expo → Succeeded readExponent (spellExponent expo) []
exponentComplete absent = part absent [] refl , refl , refl
exponentComplete (exponent lower sign (head , tail)) = exponentBodyComplete lower sign head tail
exponentComplete (exponent upper sign (head , tail)) = exponentBodyComplete upper sign head tail

exponentStopped : ∀ expo → Digits.Stopped (spellExponent expo)
exponentStopped absent = tt
exponentStopped (exponent lower sign digits) = Digits.notDecoded 'e' refl
exponentStopped (exponent upper sign digits) = Digits.notDecoded 'E' refl

fractionStopped : ∀ frac expo → Digits.Stopped (spellFraction frac ++ spellExponent expo)
fractionStopped absent expo = exponentStopped expo
fractionStopped (fraction digits) expo = Digits.notDecoded '.' refl

fractionComplete : ∀ frac expo →
  Succeeded readFraction (spellFraction frac ++ spellExponent expo) (spellExponent expo)
fractionComplete absent absent = part absent [] refl , refl , refl
fractionComplete absent (exponent lower sign digits) = part absent (spellExponent (exponent lower sign digits)) refl , refl , refl
fractionComplete absent (exponent upper sign digits) = part absent (spellExponent (exponent upper sign digits)) refl , refl , refl
fractionComplete (fraction (head , tail)) expo
  with digitsComplete head tail (spellExponent expo) (exponentStopped expo)
... | part digits rest reconstruct , equation , sameRest rewrite equation =
  part (fraction digits) rest (cong ('.' ∷_) reconstruct) , refl , sameRest

signComplete : ∀ sign whole rest →
  Succeeded (λ input → just (readSign input))
    (spellSign sign ++ (spellWhole whole ++ rest)) (spellWhole whole ++ rest)
signComplete minus whole rest = part minus (spellWhole whole ++ rest) refl , refl , refl
signComplete unsigned zero rest = part unsigned ('0' ∷ rest) refl , refl , refl
signComplete unsigned (nonzero head notZero tail) rest with D.character head ≟ '-'
... | yes same = ⊥-elim (D.digitNotMinus head same)
... | no _ = part unsigned (spellWhole (nonzero head notZero tail) ++ rest) refl , refl , refl

readComplete : ∀ form → Succeeded read (spell form) []
readComplete form@(sign , whole , frac , expo) = sequenceComplete
  (λ input → just (readSign input)) (sequence readWhole (sequence readFraction readExponent))
  (spell form) (spellWhole whole ++ (spellFraction frac ++ spellExponent expo)) []
  (signComplete sign whole (spellFraction frac ++ spellExponent expo))
  (sequenceComplete readWhole (sequence readFraction readExponent)
    (spellWhole whole ++ (spellFraction frac ++ spellExponent expo))
    (spellFraction frac ++ spellExponent expo) []
    (wholeComplete whole (spellFraction frac ++ spellExponent expo) (fractionStopped frac expo))
    (sequenceComplete readFraction readExponent (spellFraction frac ++ spellExponent expo)
      (spellExponent expo) [] (fractionComplete frac expo) (exponentComplete expo)))

parseComplete : ∀ form → Σ[ result ∈ Parsed (spell form) ] parse (spell form) ≡ just result
parseComplete form with readComplete form
... | part parsedForm [] reconstruct , equation , refl rewrite equation =
  parsed parsedForm (trans reconstruct (++-identityʳ (spell parsedForm))) , refl

Language : Text → Set
Language input = Σ[ form ∈ Syntax ] input ≡ spell form

validInputAccepted : ∀ input → Language input →
  Σ[ result ∈ Parsed input ] parse input ≡ just result
validInputAccepted .(spell form) (form , refl) = parseComplete form

decide : ∀ input → Dec (Language input)
decide input with parse input in result
... | just parsedValue = yes (Parsed.form parsedValue , Parsed.exact parsedValue)
... | nothing = no (λ valid → rejected valid (validInputAccepted input valid))
  where
  rejected : Language input → (Σ[ parsedValue ∈ Parsed input ] parse input ≡ just parsedValue) → Data.Empty.⊥
  rejected valid (parsedValue , equation) = Digits.nothingNotJust (trans (sym result) equation)
