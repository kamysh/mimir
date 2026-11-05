{-# OPTIONS --safe #-}
-- Canonical decimal rendering: nonempty ASCII digits, exact numeric value,
-- and no leading zero except the single digit zero. Division decreases the
-- recursion measure; no unchecked termination is used.
module Mimir.NatDecimal where

open import Data.Fin using (Fin; toℕ; fromℕ<; zero; suc)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Nat using (ℕ; _+_; _*_; _/_; _%_; _<_; s≤s; z≤n)
import Data.Nat as Nat
open import Data.Nat.Properties using (+-identityʳ; +-comm; *-comm)
import Data.Char as Char
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (inj₂)
open import Data.Nat.DivMod using (m/n<m; m%n<n; m≡m%n+[m/n]*n)
open import Data.Nat.Induction using (Acc; acc; <-wellFounded)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym; subst)
open import Mimir.Text using (Text)
import Mimir.Unsigned as D

digit : Fin 10 → D.Digit
digit zero = D.d0
digit (suc zero) = D.d1
digit (suc (suc zero)) = D.d2
digit (suc (suc (suc zero))) = D.d3
digit (suc (suc (suc (suc zero)))) = D.d4
digit (suc (suc (suc (suc (suc zero))))) = D.d5
digit (suc (suc (suc (suc (suc (suc zero)))))) = D.d6
digit (suc (suc (suc (suc (suc (suc (suc zero))))))) = D.d7
digit (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = D.d8
digit (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = D.d9

digitValue : ∀ value → D.value (digit value) ≡ toℕ value
digitValue zero = refl
digitValue (suc zero) = refl
digitValue (suc (suc zero)) = refl
digitValue (suc (suc (suc zero))) = refl
digitValue (suc (suc (suc (suc zero)))) = refl
digitValue (suc (suc (suc (suc (suc zero))))) = refl
digitValue (suc (suc (suc (suc (suc (suc zero)))))) = refl
digitValue (suc (suc (suc (suc (suc (suc (suc zero))))))) = refl
digitValue (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = refl
digitValue (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = refl

fold : ℕ → List D.Digit → ℕ
fold before [] = before
fold before (first ∷ rest) = fold (10 * before + D.value first) rest

foldAppend : ∀ before first second → fold before (first ++ second) ≡ fold (fold before first) second
foldAppend before [] second = refl
foldAppend before (head ∷ tail) second = foldAppend (10 * before + D.value head) tail second

record Decimal (number : ℕ) : Set where
  constructor decimal
  field
    head : D.Digit
    tail : List D.Digit
    exact : fold 0 (head ∷ tail) ≡ number
    leadingZero : head ≡ D.d0 → tail ≡ []

digits : ∀ {number} → Decimal number → List D.Digit
digits representation = Decimal.head representation ∷ Decimal.tail representation

positiveHead : ∀ number (representation : Decimal (Nat.suc number)) → Decimal.head representation ≢ D.d0
positiveHead number (decimal D.d0 tail exact leading) refl with leading refl
... | refl with exact
...   | ()

append : ∀ number → Decimal (Nat.suc number) → (last : D.Digit) → Decimal (10 * Nat.suc number + D.value last)
append number representation last = decimal (Decimal.head representation) (Decimal.tail representation ++ (last ∷ []))
  (trans (foldAppend 0 (digits representation) (last ∷ [])) (cong (λ n → 10 * n + D.value last) (Decimal.exact representation)))
  (λ zeroHead → ⊥-elim (positiveHead number representation zeroHead))

reindex : ∀ {first second} → first ≡ second → Decimal first → Decimal second
reindex refl representation = representation

remainder : ℕ → D.Digit
remainder number = digit (fromℕ< (m%n<n number 10))

remainderValue : ∀ number → D.value (remainder number) ≡ number % 10
remainderValue number = trans (digitValue (fromℕ< (m%n<n number 10))) (toℕ-fromℕ< (m%n<n number 10))

encodeAcc : ∀ number → Acc _<_ number → Decimal number
encodeAcc Nat.zero accessible = decimal D.d0 [] refl (λ same → refl)
encodeAcc (Nat.suc number) (acc smaller) with (Nat.suc number) / 10 in quotient
... | Nat.zero = decimal (remainder (Nat.suc number)) []
    (trans (remainderValue (Nat.suc number)) (sym (trans decomposition (+-identityʳ ((Nat.suc number) % 10)))))
    (λ same → refl)
  where decomposition = trans (m≡m%n+[m/n]*n (Nat.suc number) 10) (cong (λ q → (Nat.suc number) % 10 + q * 10) quotient)
... | Nat.suc q = reindex target (append q recursive (remainder (Nat.suc number)))
  where
  recursive = encodeAcc (Nat.suc q) (smaller (subst (_< Nat.suc number) quotient (m/n<m (Nat.suc number) 10 (s≤s (s≤s z≤n)))))
  decomposition = trans (m≡m%n+[m/n]*n (Nat.suc number) 10) (cong (λ q → (Nat.suc number) % 10 + q * 10) quotient)
  target : 10 * Nat.suc q + D.value (remainder (Nat.suc number)) ≡ Nat.suc number
  target = trans (cong (10 * Nat.suc q +_) (remainderValue (Nat.suc number)))
    (trans (+-comm (10 * Nat.suc q) ((Nat.suc number) % 10))
      (trans (cong ((Nat.suc number) % 10 +_) (*-comm 10 (Nat.suc q))) (sym decomposition)))

encode : ∀ number → Decimal number
encode number = encodeAcc number (<-wellFounded number)

interpretation : ∀ before values → D.Digits before (map D.character values) (fold before values)
interpretation before [] = D.end before
interpretation before (first ∷ rest) = D.next first refl (interpretation (10 * before + D.value first) rest)

text : ℕ → Text
text number = map D.character (digits (encode number))

renderedValue : ∀ number → D.Digits 0 (text number) number
renderedValue number = subst (D.Digits 0 (text number)) (Decimal.exact (encode number)) (interpretation 0 (digits (encode number)))

characterValue : ∀ digit → Char.toℕ (D.character digit) ≡ 48 + D.value digit
characterValue D.d0 = refl
characterValue D.d1 = refl
characterValue D.d2 = refl
characterValue D.d3 = refl
characterValue D.d4 = refl
characterValue D.d5 = refl
characterValue D.d6 = refl
characterValue D.d7 = refl
characterValue D.d8 = refl
characterValue D.d9 = refl

sameCharacterValue : ∀ first second → D.character first ≡ D.character second → D.value first ≡ D.value second
sameCharacterValue first second same = Data.Nat.Properties.+-cancelˡ-≡ 48 (D.value first) (D.value second)
  (trans (sym (characterValue first)) (trans (cong Char.toℕ same) (characterValue second)))

digitsUnique : ∀ {before input first second} → D.Digits before input first → D.Digits before input second → first ≡ second
digitsUnique (D.end number) (D.end .number) = refl
digitsUnique (D.next first firstSpelling firstRest) (D.next second secondSpelling secondRest)
  rewrite sameCharacterValue first second (trans (sym firstSpelling) secondSpelling) = digitsUnique firstRest secondRest

syntaxUnique : ∀ {input first second} → D.Syntax input first → D.Syntax input second → first ≡ second
syntaxUnique (D.plain (D.digits c cs first firstGrammar)) (D.plain (D.digits .c .cs second secondGrammar)) = digitsUnique firstGrammar secondGrammar
syntaxUnique (D.plus (D.digits c cs first firstGrammar)) (D.plus (D.digits .c .cs second secondGrammar)) = digitsUnique firstGrammar secondGrammar
syntaxUnique (D.plain (D.digits .('+' ) cs first (D.next digit spelling rest))) (D.plus second) = ⊥-elim (D.digitNotPlus digit (sym spelling))
syntaxUnique (D.plus first) (D.plain (D.digits .('+' ) cs second (D.next digit spelling rest))) = ⊥-elim (D.digitNotPlus digit (sym spelling))

renderedSyntax : ∀ number → D.Syntax (text number) number
renderedSyntax number = D.plain (D.digits (D.character (Decimal.head (encode number)))
  (map D.character (Decimal.tail (encode number))) number (renderedValue number))

parseRoundTrip : ∀ maximum number → number Nat.≤ maximum →
  Σ (D.Number maximum (text number)) (λ parsed →
    D.parse maximum (text number) ≡ inj₂ parsed × D.UInt.number (D.Number.result parsed) ≡ number)
parseRoundTrip maximum number bounded with D.parseComplete maximum (text number) number (renderedSyntax number) bounded
... | parsed , observed = parsed , observed , syntaxUnique (D.Number.wellFormed parsed) (renderedSyntax number)
