{-# OPTIONS --safe #-}
-- Syntactic numeric scanning preserves a delimited suffix without arithmetic.
module Mimir.JsonIgnoredNumberReadBack where

open import Data.Char using (Char; _≟_)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
import Mimir.Unsigned as Decimal
import Mimir.DecimalLexer as Digits
import Mimir.JsonIgnoredNumber as Number
module C = Number.C

record Returned {input} (result : C.Result ⊤ input) (suffix : List Char) : Set where
  constructor returned
  field
    consumed : List Char
    exact : input ≡ consumed ++ suffix
    observed : result ≡ C.success tt consumed suffix exact

done : ∀ suffix → Returned (C.done tt suffix) suffix
done suffix = returned [] refl refl

prefix : ∀ before {input suffix} {result : C.Result ⊤ input} →
  Returned result suffix → Returned (C.prefix before result) suffix
prefix before (returned consumed exact refl) = returned (before ++ consumed) _ refl

reframe : ∀ {input source suffix} (exact : input ≡ source) {result : C.Result ⊤ source} →
  Returned result suffix → Returned (C.reframe exact result) suffix
reframe refl receipt = receipt

scan : ∀ next scanned input suffix → Digits.Stopped input → Returned (next input) suffix →
  Returned (Number.digits next (map Decimal.character scanned ++ input)) suffix
scan next scanned input suffix stopped receipt with Digits.take (map Decimal.character scanned ++ input)
  | Digits.complete scanned input stopped
... | Digits.run .scanned .input exact terminal | refl , refl = reframe exact (prefix (map Decimal.character scanned) receipt)

Stopped : List Char → Set
Stopped [] = ⊤
Stopped (char ∷ rest) = Digits.NotDigit char × (char ≢ '.' × (char ≢ 'e' × char ≢ 'E'))

afterFraction : ∀ suffix → Stopped suffix → Returned (Number.afterFraction suffix) suffix
afterFraction [] stopped = done []
afterFraction (char ∷ rest) (notDigit , notDot , notLower , notUpper) with char ≟ 'e'
... | yes same = ⊥-elim (notLower same)
... | no lower with char ≟ 'E'
...   | yes same = ⊥-elim (notUpper same)
...   | no upper = done (char ∷ rest)

afterInteger : ∀ suffix → Stopped suffix → Returned (Number.afterInteger suffix) suffix
afterInteger [] stopped = done []
afterInteger (char ∷ rest) stopped@(notDigit , notDot , notLower , notUpper) with char ≟ '.'
... | yes same = ⊥-elim (notDot same)
... | no other = afterFraction (char ∷ rest) stopped

stoppedDigits : ∀ suffix → Stopped suffix → Digits.Stopped suffix
stoppedDigits [] stopped = tt
stoppedDigits (char ∷ rest) (notDigit , others) = notDigit

afterZero : ∀ input suffix → Digits.Stopped input →
  Returned (Number.afterInteger input) suffix → Returned (Number.afterZero input) suffix
afterZero [] suffix stopped receipt = receipt
afterZero (char ∷ rest) suffix stopped receipt with Digits.classify char
... | yes (digit , same) = ⊥-elim (stopped digit same)
... | no other = receipt

integerZero : ∀ input suffix → Digits.Stopped input →
  Returned (Number.afterInteger input) suffix → Returned (Number.integer ('0' ∷ input)) suffix
integerZero input suffix stopped receipt = prefix ('0' ∷ []) (afterZero input suffix stopped receipt)

integerNonzero : ∀ first scanned input suffix → Decimal.character first ≢ '0' → Digits.Stopped input →
  Returned (Number.afterInteger input) suffix →
  Returned (Number.integer (Decimal.character first ∷ (map Decimal.character scanned ++ input))) suffix
integerNonzero first scanned input suffix nonzero stopped receipt with Decimal.character first ≟ '0'
... | yes same = ⊥-elim (nonzero same)
... | no other rewrite Digits.classifyComplete first = prefix (Decimal.character first ∷ [])
  (scan Number.afterInteger scanned input suffix stopped receipt)

digitNotMinus : ∀ digit → Decimal.character digit ≢ '-'
digitNotMinus digit = λ same → Digits.notDecoded '-' refl digit (sym same)

positive : ∀ first rest suffix → Returned (Number.integer (Decimal.character first ∷ rest)) suffix →
  Returned (Number.read (Decimal.character first ∷ rest)) suffix
positive first rest suffix receipt with Decimal.character first ≟ '-'
... | yes same = ⊥-elim (digitNotMinus first same)
... | no other = receipt

negative : ∀ input suffix → Returned (Number.integer input) suffix →
  Returned (Number.read ('-' ∷ input)) suffix
negative input suffix receipt = prefix ('-' ∷ []) receipt

fraction : ∀ first scanned input suffix → Digits.Stopped input →
  Returned (Number.afterFraction input) suffix →
  Returned (Number.fraction (Decimal.character first ∷ (map Decimal.character scanned ++ input))) suffix
fraction first scanned input suffix stopped receipt
  with Digits.take (Decimal.character first ∷ (map Decimal.character scanned ++ input))
     | Digits.complete (first ∷ scanned) input stopped
... | Digits.run .(first ∷ scanned) .input exact terminal | refl , refl = reframe exact
  (prefix (Decimal.character first ∷ map Decimal.character scanned)
   receipt)

exponentFirst : ∀ first scanned suffix → Digits.Stopped suffix →
  Returned (Number.exponentFirst (Decimal.character first ∷ (map Decimal.character scanned ++ suffix))) suffix
exponentFirst first scanned suffix stopped rewrite Digits.classifyComplete first = prefix (Decimal.character first ∷ [])
  (scan Number.finish scanned suffix suffix stopped (done suffix))

digitNotPlus : ∀ digit → Decimal.character digit ≢ '+'
digitNotPlus digit = λ same → Digits.notDecoded '+' refl digit (sym same)

exponentUnsigned : ∀ first rest suffix →
  Returned (Number.exponentFirst (Decimal.character first ∷ rest)) suffix →
  Returned (Number.exponentSign (Decimal.character first ∷ rest)) suffix
exponentUnsigned first rest suffix receipt with Decimal.character first ≟ '+'
... | yes same = ⊥-elim (digitNotPlus first same)
... | no notPlus with Decimal.character first ≟ '-'
...   | yes same = ⊥-elim (digitNotMinus first same)
...   | no notMinus = receipt

exponentPlus : ∀ input suffix → Returned (Number.exponentFirst input) suffix →
  Returned (Number.exponentSign ('+' ∷ input)) suffix
exponentPlus input suffix receipt = prefix ('+' ∷ []) receipt

exponentMinus : ∀ input suffix → Returned (Number.exponentFirst input) suffix →
  Returned (Number.exponentSign ('-' ∷ input)) suffix
exponentMinus input suffix receipt = prefix ('-' ∷ []) receipt

lowerExponent : ∀ input suffix → Returned (Number.exponentSign input) suffix →
  Returned (Number.afterFraction ('e' ∷ input)) suffix
lowerExponent input suffix receipt = prefix ('e' ∷ []) receipt

upperExponent : ∀ input suffix → Returned (Number.exponentSign input) suffix →
  Returned (Number.afterFraction ('E' ∷ input)) suffix
upperExponent input suffix receipt = prefix ('E' ∷ []) receipt

withFraction : ∀ input suffix → Returned (Number.fraction input) suffix →
  Returned (Number.afterInteger ('.' ∷ input)) suffix
withFraction input suffix receipt = prefix ('.' ∷ []) receipt

withoutFraction : ∀ char rest suffix → char ≢ '.' →
  Returned (Number.afterFraction (char ∷ rest)) suffix →
  Returned (Number.afterInteger (char ∷ rest)) suffix
withoutFraction char rest suffix notDot receipt with char ≟ '.'
... | yes same = ⊥-elim (notDot same)
... | no other = receipt
