{-# OPTIONS --safe #-}
-- The eager block-buffer padding branch, with exact marker/zero/length layout.
-- Bit-length arithmetic and full-input buffering are separate from this step.
module Mimir.SHA256Padding where

open import Data.Nat using (ℕ; suc; _∸_; _<_; _≤_; _≤?_)
open import Data.Fin using (Fin; zero; fromℕ<)
open import Data.List as List using (List)
import Data.List.Properties as List
open import Data.Vec using (Vec; _∷ʳ_; _++_; replicate; toList)
open import Data.Vec.Properties using (toList-++; toList-∷ʳ; toList-replicate)
open import Relation.Nullary using (yes; no)
import Relation.Nullary.Decidable.Core
import Data.Unit
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)
open import Mimir.ExactBytes using (Byte; Bytes)
import Mimir.VectorFill as Fill
import Mimir.FixedBlocks as Fixed

module Blocks = Fixed.Blocks Byte

-- The marker is 0x80. Construct its bounded value with the ordinary decision
-- procedure, so the Fin value is not an unchecked numeric coercion.
paddingMarker : Byte
paddingMarker = fromℕ< (Relation.Nullary.Decidable.Core.toWitness {a? = 128 Data.Nat.<? 256} Data.Unit.tt)

finish : ∀ {size} → Bytes size → size < 64 → Bytes 8 → List (Bytes 64)
finish {size} buffer bounded lengthField with suc size ≤? 56
... | yes room = (Fill.fill 56 (buffer ∷ʳ paddingMarker) room zero ++ lengthField) List.∷ List.[]
... | no crowded = Fill.fill 64 (buffer ∷ʳ paddingMarker) bounded zero List.∷
  (replicate 56 zero ++ lengthField) List.∷ List.[]

zeroCount : ℕ → ℕ
zeroCount size with suc size ≤? 56
... | yes room = 56 ∸ suc size
... | no crowded = (64 ∸ suc size) Data.Nat.+ 56

oneLayout : ∀ {size} (buffer : Bytes size) room (lengthField : Bytes 8) →
  toList (Fill.fill 56 (buffer ∷ʳ paddingMarker) room zero ++ lengthField) ≡
  toList buffer List.++ (paddingMarker List.∷ List.replicate (56 ∸ suc size) zero) List.++ toList lengthField
oneLayout {size} buffer room lengthField =
  trans (toList-++ (Fill.fill 56 (buffer ∷ʳ paddingMarker) room zero) lengthField)
  (trans (cong (List._++ toList lengthField) (Fill.exact 56 (buffer ∷ʳ paddingMarker) room zero))
  (trans (cong (λ before → (before List.++ List.replicate (56 ∸ suc size) zero) List.++ toList lengthField)
    (toList-∷ʳ paddingMarker buffer))
  (trans (cong (List._++ toList lengthField) (List.++-assoc (toList buffer) (paddingMarker List.∷ List.[]) _))
    (List.++-assoc (toList buffer) (paddingMarker List.∷ List.replicate (56 ∸ suc size) zero) (toList lengthField)))))

flattenOne : ∀ (block : Bytes 64) → Blocks.flatten (block List.∷ List.[]) ≡ toList block
flattenOne block = List.++-identityʳ (toList block)

oneBlockExact : ∀ {size} (buffer : Bytes size) bounded lengthField room → (suc size ≤? 56) ≡ yes room →
  Blocks.flatten (finish buffer bounded lengthField) ≡
  toList buffer List.++ (paddingMarker List.∷ List.replicate (56 ∸ suc size) zero) List.++ toList lengthField
oneBlockExact {size} buffer bounded lengthField room accepted rewrite accepted =
  trans (flattenOne (Fill.fill 56 (buffer ∷ʳ paddingMarker) room zero ++ lengthField))
    (oneLayout buffer room lengthField)

replicateAppend : ∀ {A : Set} first second (value : A) →
  List.replicate (first Data.Nat.+ second) value ≡ List.replicate first value List.++ List.replicate second value
replicateAppend Data.Nat.zero second value = refl
replicateAppend (suc first) second value = cong (value List.∷_) (replicateAppend first second value)

joinPadding : ∀ (before zeros1 zeros2 ending : List Byte) marker →
  ((before List.++ marker List.∷ List.[]) List.++ zeros1) List.++ (zeros2 List.++ ending) ≡
  before List.++ (marker List.∷ (zeros1 List.++ zeros2)) List.++ ending
joinPadding before zeros1 zeros2 ending marker =
  trans (List.++-assoc (before List.++ marker List.∷ List.[]) zeros1 (zeros2 List.++ ending))
  (trans (List.++-assoc before (marker List.∷ List.[]) (zeros1 List.++ (zeros2 List.++ ending)))
    (cong (λ suffix → before List.++ marker List.∷ suffix) (sym (List.++-assoc zeros1 zeros2 ending))))

twoLayout : ∀ {size} (buffer : Bytes size) bounded (lengthField : Bytes 8) →
  Blocks.flatten (Fill.fill 64 (buffer ∷ʳ paddingMarker) bounded zero List.∷
    (replicate 56 zero ++ lengthField) List.∷ List.[]) ≡
  toList buffer List.++ (paddingMarker List.∷ List.replicate ((64 ∸ suc size) Data.Nat.+ 56) zero) List.++ toList lengthField
twoLayout {size} buffer bounded lengthField
  rewrite List.++-identityʳ (toList (replicate 56 zero ++ lengthField)) |
    toList-++ (replicate 56 zero) lengthField | toList-replicate {A = Byte} 56 zero |
    Fill.exact 64 (buffer ∷ʳ paddingMarker) bounded zero | toList-∷ʳ paddingMarker buffer =
  trans (joinPadding (toList buffer) (List.replicate (64 ∸ suc size) zero)
    (List.replicate 56 zero) (toList lengthField) paddingMarker)
    (cong (λ zeros → toList buffer List.++ (paddingMarker List.∷ zeros) List.++ toList lengthField)
      (sym (replicateAppend (64 ∸ suc size) 56 zero)))

layout : ∀ {size} (buffer : Bytes size) bounded (lengthField : Bytes 8) →
  Blocks.flatten (finish buffer bounded lengthField) ≡
  toList buffer List.++ (paddingMarker List.∷ List.replicate (zeroCount size) zero) List.++ toList lengthField
layout {size} buffer bounded lengthField with suc size ≤? 56
... | yes room = trans (flattenOne (Fill.fill 56 (buffer ∷ʳ paddingMarker) room zero ++ lengthField)) (oneLayout buffer room lengthField)
... | no crowded = twoLayout buffer bounded lengthField
