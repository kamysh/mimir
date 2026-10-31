{-# OPTIONS --safe #-}
-- Number completeness inside arrays/objects and before JSON whitespace.
-- Trailing input is preserved exactly, rather than accepted as number digits.
module Mimir.JsonNumberSuffix where

open import Data.Char using (Char; _≟_)
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Maybe using (just)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Mimir.Text using (Text)
open import Mimir.ParsedPart
open import Mimir.JsonNumber
import Mimir.JsonNumberCompleteness as Complete
import Mimir.DecimalLexer as Digits
import Mimir.Unsigned as D

data Delimiter : Char → Set where
  space : Delimiter ' '
  horizontalTab : Delimiter '\t'
  lineFeed : Delimiter '\n'
  carriageReturn : Delimiter '\r'
  comma : Delimiter ','
  arrayEnd : Delimiter ']'
  objectEnd : Delimiter '}'

Terminal : Text → Set
Terminal [] = ⊤
Terminal (first ∷ rest) = Delimiter first

stopped : ∀ rest → Terminal rest → Digits.Stopped rest
stopped [] terminal = tt
stopped (. ' ' ∷ rest) space = Digits.notDecoded ' ' refl
stopped (. '\t' ∷ rest) horizontalTab = Digits.notDecoded '\t' refl
stopped (. '\n' ∷ rest) lineFeed = Digits.notDecoded '\n' refl
stopped (. '\r' ∷ rest) carriageReturn = Digits.notDecoded '\r' refl
stopped (. ',' ∷ rest) comma = Digits.notDecoded ',' refl
stopped (. ']' ∷ rest) arrayEnd = Digits.notDecoded ']' refl
stopped (. '}' ∷ rest) objectEnd = Digits.notDecoded '}' refl

noFraction : ∀ rest → Terminal rest → readFraction rest ≡ just (part absent rest refl)
noFraction [] terminal = refl
noFraction (. ' ' ∷ rest) space = refl
noFraction (. '\t' ∷ rest) horizontalTab = refl
noFraction (. '\n' ∷ rest) lineFeed = refl
noFraction (. '\r' ∷ rest) carriageReturn = refl
noFraction (. ',' ∷ rest) comma = refl
noFraction (. ']' ∷ rest) arrayEnd = refl
noFraction (. '}' ∷ rest) objectEnd = refl

noExponent : ∀ rest → Terminal rest → readExponent rest ≡ just (part absent rest refl)
noExponent [] terminal = refl
noExponent (. ' ' ∷ rest) space = refl
noExponent (. '\t' ∷ rest) horizontalTab = refl
noExponent (. '\n' ∷ rest) lineFeed = refl
noExponent (. '\r' ∷ rest) carriageReturn = refl
noExponent (. ',' ∷ rest) comma = refl
noExponent (. ']' ∷ rest) arrayEnd = refl
noExponent (. '}' ∷ rest) objectEnd = refl

exponentSignComplete : ∀ sign head tail rest →
  Succeeded (λ input → just (readExponentSign input))
    (spellExponentSign sign ++ (spellDigits (head , tail) ++ rest))
    (spellDigits (head , tail) ++ rest)
exponentSignComplete plus head tail rest = _ , refl , refl
exponentSignComplete minus head tail rest = _ , refl , refl
exponentSignComplete implicit head tail rest with D.character head ≟ '+'
... | yes same = ⊥-elim (D.digitNotPlus head same)
... | no _ with D.character head ≟ '-'
...   | yes same = ⊥-elim (D.digitNotMinus head same)
...   | no _ = _ , refl , refl

exponentBodyComplete : ∀ e sign head tail rest → Terminal rest →
  Σ (Part Exponent spellExponent (marker e ∷ (spellExponentSign sign ++ (spellDigits (head , tail) ++ rest))))
    (λ result → readExponentBody e (spellExponentSign sign ++ (spellDigits (head , tail) ++ rest)) ≡ just result × Part.rest result ≡ rest)
exponentBodyComplete e sign head tail rest terminal with sequenceComplete
  (λ input → just (readExponentSign input)) readDigits
  (spellExponentSign sign ++ (spellDigits (head , tail) ++ rest)) (spellDigits (head , tail) ++ rest) rest
  (exponentSignComplete sign head tail rest) (Complete.digitsComplete head tail rest (stopped rest terminal))
... | part (parsedSign , parsedDigits) suffix exact , observed , sameRest rewrite observed =
  part (exponent e parsedSign parsedDigits) suffix (cong (marker e ∷_) exact) , refl , sameRest

exponentComplete : ∀ expo rest → Terminal rest → Succeeded readExponent (spellExponent expo ++ rest) rest
exponentComplete absent rest terminal = part absent rest refl , noExponent rest terminal , refl
exponentComplete (exponent lower sign (head , tail)) rest terminal
  rewrite ++-assoc (spellExponentSign sign) (spellDigits (head , tail)) rest =
  exponentBodyComplete lower sign head tail rest terminal
exponentComplete (exponent upper sign (head , tail)) rest terminal
  rewrite ++-assoc (spellExponentSign sign) (spellDigits (head , tail)) rest =
  exponentBodyComplete upper sign head tail rest terminal

exponentStopped : ∀ expo rest → Terminal rest → Digits.Stopped (spellExponent expo ++ rest)
exponentStopped absent rest terminal = stopped rest terminal
exponentStopped (exponent lower sign digits) rest terminal = Digits.notDecoded 'e' refl
exponentStopped (exponent upper sign digits) rest terminal = Digits.notDecoded 'E' refl

fractionStopped : ∀ frac expo rest → Terminal rest → Digits.Stopped (spellFraction frac ++ (spellExponent expo ++ rest))
fractionStopped absent expo rest terminal = exponentStopped expo rest terminal
fractionStopped (fraction digits) expo rest terminal = Digits.notDecoded '.' refl

fractionComplete : ∀ frac expo rest → Terminal rest →
  Succeeded readFraction (spellFraction frac ++ (spellExponent expo ++ rest)) (spellExponent expo ++ rest)
fractionComplete absent absent rest terminal = part absent rest refl , noFraction rest terminal , refl
fractionComplete absent (exponent lower sign digits) rest terminal = _ , refl , refl
fractionComplete absent (exponent upper sign digits) rest terminal = _ , refl , refl
fractionComplete (fraction (head , tail)) expo rest terminal with
  Complete.digitsComplete head tail (spellExponent expo ++ rest) (exponentStopped expo rest terminal)
... | part digits suffix exact , observed , sameRest rewrite observed =
  part (fraction digits) suffix (cong ('.' ∷_) exact) , refl , sameRest

readComplete : ∀ form rest → Terminal rest → Succeeded read (spell form ++ rest) rest
readComplete (sign , whole , frac , expo) rest terminal
  rewrite ++-assoc (spellSign sign) (spellWhole whole ++ (spellFraction frac ++ spellExponent expo)) rest |
    ++-assoc (spellWhole whole) (spellFraction frac ++ spellExponent expo) rest |
    ++-assoc (spellFraction frac) (spellExponent expo) rest =
  sequenceComplete (λ input → just (readSign input)) (sequence readWhole (sequence readFraction readExponent))
    (spellSign sign ++ (spellWhole whole ++ (spellFraction frac ++ (spellExponent expo ++ rest))))
    (spellWhole whole ++ (spellFraction frac ++ (spellExponent expo ++ rest))) rest
    (Complete.signComplete sign whole (spellFraction frac ++ (spellExponent expo ++ rest)))
    (sequenceComplete readWhole (sequence readFraction readExponent)
      (spellWhole whole ++ (spellFraction frac ++ (spellExponent expo ++ rest)))
      (spellFraction frac ++ (spellExponent expo ++ rest)) rest
      (Complete.wholeComplete whole (spellFraction frac ++ (spellExponent expo ++ rest)) (fractionStopped frac expo rest terminal))
      (sequenceComplete readFraction readExponent (spellFraction frac ++ (spellExponent expo ++ rest))
        (spellExponent expo ++ rest) rest (fractionComplete frac expo rest terminal) (exponentComplete expo rest terminal)))
