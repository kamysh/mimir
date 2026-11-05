{-# OPTIONS --safe #-}
-- The independent group grammar completely determines the reader output,
-- including consumed bytes, untouched suffix and validity flag.
module Mimir.UTF8LossyGroupComplete where

open import Data.Bool using (Bool)
open import Data.List using (List)
open import Data.Nat using (s≤s)
open import Data.Nat.Properties using (≤-trans)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Bits using (Byte)
import Mimir.UTF8LossyGroup as G
import Mimir.UTF8LossyTail as T
import Mimir.UTF8CanonicalBounds as Bounds
import Mimir.UTF8ByteDecode as Decode

data Shape : Set where ascii invalid : Shape; multibyte : G.Width → Shape

shape : ∀ {byte} → G.Head byte → Shape
shape (G.ascii ordinary) = ascii
shape (G.invalid unsupported) = invalid
shape (G.multibyte width admitted) = multibyte width

classifiedLike : ∀ {byte} (head : G.Head byte) → shape (G.classify byte) ≡ shape head
classifiedLike {byte} (G.ascii ordinary) with T.between? 0 127 byte
... | yes accepted = refl
... | no rejected = ⊥-elim (rejected ordinary)
classifiedLike {byte} (G.multibyte G.two admitted) with T.between? 0 127 byte
... | yes ordinary = ⊥-elim (Decode.separated (≤-trans (Bounds.padding 128 66) (proj₁ admitted)) (s≤s (proj₂ ordinary)))
... | no notASCII with T.between? 194 223 byte
...   | yes accepted = refl
...   | no rejected = ⊥-elim (rejected admitted)
classifiedLike {byte} (G.multibyte G.three admitted) with T.between? 0 127 byte
... | yes ordinary = ⊥-elim (Decode.separated (≤-trans (Bounds.padding 128 96) (proj₁ admitted)) (s≤s (proj₂ ordinary)))
... | no notASCII with T.between? 194 223 byte
...   | yes two = ⊥-elim (Decode.separated (proj₁ admitted) (s≤s (proj₂ two)))
...   | no notTwo with T.between? 224 239 byte
...     | yes accepted = refl
...     | no rejected = ⊥-elim (rejected admitted)
classifiedLike {byte} (G.multibyte G.four admitted) with T.between? 0 127 byte
... | yes ordinary = ⊥-elim (Decode.separated (≤-trans (Bounds.padding 128 112) (proj₁ admitted)) (s≤s (proj₂ ordinary)))
... | no notASCII with T.between? 194 223 byte
...   | yes two = ⊥-elim (Decode.separated (≤-trans (Bounds.padding 224 16) (proj₁ admitted)) (s≤s (proj₂ two)))
...   | no notTwo with T.between? 224 239 byte
...     | yes three = ⊥-elim (Decode.separated (proj₁ admitted) (s≤s (proj₂ three)))
...     | no notThree with T.between? 240 244 byte
...       | yes accepted = refl
...       | no rejected = ⊥-elim (rejected admitted)
classifiedLike {byte} (G.invalid (notASCII , notTwo , notThree , notFour)) with T.between? 0 127 byte
... | yes ordinary = ⊥-elim (notASCII ordinary)
... | no rejectedASCII with T.between? 194 223 byte
...   | yes two = ⊥-elim (notTwo two)
...   | no rejectedTwo with T.between? 224 239 byte
...     | yes three = ⊥-elim (notThree three)
...     | no rejectedThree with T.between? 240 244 byte
...       | yes four = ⊥-elim (notFour four)
...       | no rejectedFour = refl

view : ∀ {byte input} → G.Group byte input → List Byte × List Byte × Bool
view group = G.consumed group , G.remaining group , G.valid group

readComplete : ∀ {byte input} (group : G.Group byte input) → view (G.read byte input) ≡ view group
readComplete {byte} (G.single ordinary) with G.classify byte | classifiedLike (G.ascii ordinary)
... | G.ascii accepted | refl = refl
readComplete {byte} (G.badHead unsupported) with G.classify byte | classifiedLike (G.invalid unsupported)
... | G.invalid rejected | refl = refl
readComplete {byte} {input} (G.multiple width admitted (T.readResult consumed remaining status meaning))
  with G.classify byte | classifiedLike (G.multibyte width admitted)
... | G.multibyte .width accepted | refl
  with T.read (proj₁ (G.secondRange width byte)) (proj₂ (G.secondRange width byte)) (G.tailCount width) input |
    T.completeRead meaning
...   | T.readResult .consumed .remaining .status checked | refl = refl
