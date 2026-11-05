{-# OPTIONS --safe #-}
-- Checked ASCII literal encoding for native filenames. Every output byte is
-- exactly the character's code point; no lossy conversion or truncation occurs.
module Mimir.ASCIIPath where

open import Data.Char using (Char)
import Data.Char as Char
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (_<_; _<?_; _≤?_)
open import Data.Nat.Properties using (<-≤-trans)
open import Data.Fin using (fromℕ<; toℕ)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; cong₂)
open import Mimir.Text using (Text)
open import Mimir.Bits using (Byte)
import Mimir.Collections as C

ASCII : Text → Set
ASCII = All (λ char → Char.toℕ char < 128)

ascii? : ∀ text → Dec (ASCII text)
ascii? = C.all? (λ char → Char.toℕ char <? 128)

encodeByte : (char : Char) → Char.toℕ char < 128 → Byte
encodeByte char small = fromℕ< (<-≤-trans small (toWitness {a? = 128 ≤? 256} tt))

encode : ∀ {text} → ASCII text → List Byte
encode [] = []
encode {char ∷ text} (small ∷ rest) = encodeByte char small ∷ encode rest

encodeExact : ∀ {text} (valid : ASCII text) → map toℕ (encode valid) ≡ map Char.toℕ text
encodeExact [] = Relation.Binary.PropositionalEquality.refl
encodeExact {char ∷ text} (small ∷ rest) =
  cong₂ _∷_ (toℕ-fromℕ< (<-≤-trans small (toWitness {a? = 128 ≤? 256} tt))) (encodeExact rest)

literal : (text : Text) → True (ascii? text) → List Byte
literal text valid = encode (toWitness valid)
