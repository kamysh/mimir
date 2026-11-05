{-# OPTIONS --safe #-}
-- The exact leading-byte and second-byte ranges used by Rust Utf8Chunks.
-- Group boundaries are separate from the later scalar-decoding proof.
module Mimir.UTF8LossyGroup where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (toℕ)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Nat using (ℕ; _≤_; _≟_; suc; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Mimir.Bits using (Byte)
import Mimir.UTF8LossyTail as T

data Width : Set where two three four : Width

tailCount : Width → ℕ
tailCount two = 1
tailCount three = 2
tailCount four = 3

Leading : Width → Byte → Set
Leading two = T.Between 194 223
Leading three = T.Between 224 239
Leading four = T.Between 240 244

Unsupported : Byte → Set
Unsupported byte = ¬ T.Between 0 127 byte × (¬ Leading two byte × (¬ Leading three byte × ¬ Leading four byte))

data Head (byte : Byte) : Set where
  ascii : T.Between 0 127 byte → Head byte
  multibyte : ∀ width → Leading width byte → Head byte
  invalid : Unsupported byte → Head byte

classify : ∀ byte → Head byte
classify byte with T.between? 0 127 byte
... | yes ordinary = ascii ordinary
... | no notASCII with T.between? 194 223 byte
...   | yes valid = multibyte two valid
...   | no notTwo with T.between? 224 239 byte
...     | yes valid = multibyte three valid
...     | no notThree with T.between? 240 244 byte
...       | yes valid = multibyte four valid
...       | no notFour = invalid (notASCII , notTwo , notThree , notFour)

secondRange : Width → Byte → ℕ × ℕ
secondRange two byte = 128 , 191
secondRange three byte with toℕ byte ≟ 224
... | yes e0 = 160 , 191
... | no notE0 with toℕ byte ≟ 237
...   | yes ed = 128 , 159
...   | no notED = 128 , 191
secondRange four byte with toℕ byte ≟ 240
... | yes f0 = 144 , 191
... | no notF0 with toℕ byte ≟ 244
...   | yes f4 = 128 , 143
...   | no notF4 = 128 , 191

Tail : Width → Byte → List Byte → Set
Tail width byte input = T.Read (proj₁ (secondRange width byte)) (proj₂ (secondRange width byte)) (tailCount width) input

data Group (byte : Byte) (input : List Byte) : Set where
  single : T.Between 0 127 byte → Group byte input
  badHead : Unsupported byte → Group byte input
  multiple : ∀ width → Leading width byte → Tail width byte input → Group byte input

read : ∀ byte input → Group byte input
read byte input with classify byte
... | ascii ordinary = single ordinary
... | invalid unsupported = badHead unsupported
... | multibyte width valid = multiple width valid
  (T.read (proj₁ (secondRange width byte)) (proj₂ (secondRange width byte)) (tailCount width) input)

consumed : ∀ {byte input} → Group byte input → List Byte
consumed {byte} (single ordinary) = byte ∷ []
consumed {byte} (badHead unsupported) = byte ∷ []
consumed {byte} (multiple width valid tail) = byte ∷ T.Read.consumed tail

remaining : ∀ {byte input} → Group byte input → List Byte
remaining {input = input} (single ordinary) = input
remaining {input = input} (badHead unsupported) = input
remaining (multiple width valid tail) = T.Read.remaining tail

valid : ∀ {byte input} → Group byte input → Bool
valid (single ordinary) = true
valid (badHead unsupported) = false
valid (multiple width admitted tail) with T.Read.status tail
... | T.complete = true
... | T.interrupted = false

exact : ∀ {byte input} (group : Group byte input) → byte ∷ input ≡ consumed group ++ remaining group
exact (single ordinary) = refl
exact (badHead unsupported) = refl
exact {byte} (multiple width admitted tail) = cong (byte ∷_) (T.exact (T.Read.meaning tail))

positive : ∀ {byte input} (group : Group byte input) → 1 ≤ length (consumed group)
positive (single ordinary) = ≤-refl
positive (badHead unsupported) = ≤-refl
positive (multiple width admitted tail) = s≤s z≤n

tailBound : ∀ width → tailCount width ≤ 3
tailBound two = s≤s z≤n
tailBound three = s≤s (s≤s z≤n)
tailBound four = ≤-refl

bounded : ∀ {byte input} (group : Group byte input) → length (consumed group) ≤ 4
bounded (single ordinary) = s≤s z≤n
bounded (badHead unsupported) = s≤s z≤n
bounded (multiple width admitted tail) = s≤s (≤-trans (T.lengthBound (T.Read.meaning tail)) (tailBound width))

invalidBound : ∀ {byte input} (group : Group byte input) → valid group ≡ false → length (consumed group) ≤ 3
invalidBound (single ordinary) ()
invalidBound (badHead unsupported) rejected = s≤s z≤n
invalidBound (multiple width admitted (T.readResult consumed remaining T.complete meaning)) ()
invalidBound (multiple width admitted (T.readResult consumed remaining T.interrupted meaning)) rejected =
  ≤-trans (T.interruptedShort meaning) (tailBound width)
