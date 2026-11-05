{-# OPTIONS --safe #-}
-- Rust strings are Unicode scalar sequences. Length constraints in the public
-- learning contract count UTF-8 bytes; whitespace checks use Unicode White_Space.
module Mimir.Text where

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Char using (Char; toℕ)
open import Data.List using (List; []; _∷_; foldr; reverse)
open import Data.Nat using (ℕ; _+_; _≤_; _≤?_; _≟_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

Text = List Char

member : ℕ → List ℕ → Bool
member n [] = false
member n (x ∷ xs) with n ≟ x
... | yes _ = true
... | no _ = member n xs

whiteSpaceCodepoints : List ℕ
whiteSpaceCodepoints =
  9 ∷ 10 ∷ 11 ∷ 12 ∷ 13 ∷ 32 ∷ 133 ∷ 160 ∷ 5760 ∷
  8192 ∷ 8193 ∷ 8194 ∷ 8195 ∷ 8196 ∷ 8197 ∷ 8198 ∷ 8199 ∷
  8200 ∷ 8201 ∷ 8202 ∷ 8232 ∷ 8233 ∷ 8239 ∷ 8287 ∷ 12288 ∷ []

isWhitespace : Char → Bool
isWhitespace c = member (toℕ c) whiteSpaceCodepoints

nonblank : Text → Bool
nonblank [] = false
nonblank (c ∷ cs) with isWhitespace c
... | true = nonblank cs
... | false = true

widthAt : ℕ → ℕ
widthAt number with number ≤? 127
... | yes _ = 1
... | no _ with number ≤? 2047
...   | yes _ = 2
...   | no _ with number ≤? 65535
...     | yes _ = 3
...     | no _ = 4

width : Char → ℕ
width c = widthAt (toℕ c)

byteLength : Text → ℕ
byteLength = foldr (λ c n → width c + n) 0

Nonblank : Text → Set
Nonblank text = nonblank text ≡ true

nonblank? : (text : Text) → Dec (Nonblank text)
nonblank? text with nonblank text
... | true = yes refl
... | false = no (λ ())

Bounded : ℕ → Text → Set
Bounded limit text = byteLength text ≤ limit

bounded? : ∀ limit text → Dec (Bounded limit text)
bounded? limit text = byteLength text ≤? limit

data Nonempty : Text → Set where
  cons : ∀ c cs → Nonempty (c ∷ cs)

nonempty? : ∀ text → Dec (Nonempty text)
nonempty? [] = no (λ ())
nonempty? (c ∷ cs) = yes (cons c cs)

trimStart : Text → Text
trimStart [] = []
trimStart (c ∷ cs) with isWhitespace c
... | true = trimStart cs
... | false = c ∷ cs

trim : Text → Text
trim text = reverse (trimStart (reverse (trimStart text)))

trimStartIdempotent : ∀ text → trimStart (trimStart text) ≡ trimStart text
trimStartIdempotent [] = refl
trimStartIdempotent (c ∷ cs) with isWhitespace c in space
... | true = trimStartIdempotent cs
... | false rewrite space = refl
