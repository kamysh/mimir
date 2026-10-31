{-# OPTIONS --safe #-}
-- Whole-word membership for split_whitespace scope lists. A substring inside
-- a larger word is not a scope; both word boundaries must be witnessed.
module Mimir.WhitespaceWords where

open import Data.Char using (Char; _≟_)
open import Data.Bool using (Bool; true; false)
open import Data.List using ([]; _∷_)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable.Core using (_×-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text

isTrue? : ∀ value → Dec (value ≡ true)
isTrue? true = yes refl
isTrue? false = no (λ ())

isFalse? : ∀ value → Dec (value ≡ false)
isFalse? false = yes refl
isFalse? true = no (λ ())

Boundary : Text → Set
Boundary [] = ⊤
Boundary (c ∷ cs) = isWhitespace c ≡ true

boundary? : ∀ text → Dec (Boundary text)
boundary? [] = yes tt
boundary? (c ∷ cs) = isTrue? (isWhitespace c)

PrefixWord : Text → Text → Set
PrefixWord [] input = Boundary input
PrefixWord (_ ∷ _) [] = ⊥
PrefixWord (c ∷ word) (d ∷ input) = c ≡ d × (isWhitespace c ≡ false × PrefixWord word input)

prefixWord? : ∀ word input → Dec (PrefixWord word input)
prefixWord? [] input = boundary? input
prefixWord? (_ ∷ _) [] = no (λ ())
prefixWord? (c ∷ word) (d ∷ input) = (c ≟ d) ×-dec (isFalse? (isWhitespace c) ×-dec prefixWord? word input)

data Found (word : Text) : Bool → Text → Set where
  here : ∀ {boundary input} → boundary ≡ true → Nonempty word → PrefixWord word input → Found word boundary input
  later : ∀ {boundary c input} → Found word (isWhitespace c) input → Found word boundary (c ∷ input)

here? : ∀ word boundary input → Dec (boundary ≡ true × (Nonempty word × PrefixWord word input))
here? word boundary input = isTrue? boundary ×-dec (nonempty? word ×-dec prefixWord? word input)

found? : ∀ word boundary input → Dec (Found word boundary input)
found? word boundary [] with here? word boundary []
... | yes (begins , nonempty , prefix) = yes (here begins nonempty prefix)
... | no notHere = no (λ { (here begins nonempty prefix) → notHere (begins , nonempty , prefix) })
found? word boundary (c ∷ input) with here? word boundary (c ∷ input)
... | yes (begins , nonempty , prefix) = yes (here begins nonempty prefix)
... | no notHere with found? word (isWhitespace c) input
...   | yes rest = yes (later rest)
...   | no notLater = no (λ
  { (here begins nonempty prefix) → notHere (begins , nonempty , prefix)
  ; (later rest) → notLater rest })

WholeWord : Text → Text → Set
WholeWord word input = Found word true input

wholeWord? : ∀ word input → Dec (WholeWord word input)
wholeWord? word input = found? word true input

cannotStartInsideWord : ∀ {word input} → Found word false input →
  Σ Char (λ c → Σ Text (λ tail → input ≡ c ∷ tail × Found word (isWhitespace c) tail))
cannotStartInsideWord (here () nonempty prefix)
cannotStartInsideWord (later {c = c} {input = tail} rest) = c , tail , refl , rest
