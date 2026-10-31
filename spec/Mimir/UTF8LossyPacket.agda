{-# OPTIONS --safe #-}
-- Every canonical packet has an independently admitted lossy group, with
-- its exact bytes consumed and an arbitrary following suffix untouched.
module Mimir.UTF8LossyPacket where

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Nat using (suc)
import Data.Vec as V
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
open import Mimir.Bits using (Byte; Word)
import Mimir.UTF8Byte as B
import Mimir.UTF8Packet as P
import Mimir.UTF8LossyTail as T
import Mimir.UTF8LossyGroup as G
import Mimir.UTF8LossyGroupComplete as Complete
import Mimir.UTF8LossyAdmission as Admission

continuations : ∀ {count} (words : V.Vec (Word 6) count) suffix →
  T.Tail 128 191 count (map B.continuationByte (V.toList words) ++ suffix)
    (map B.continuationByte (V.toList words)) suffix T.complete
continuations V.[] suffix = T.done 128 191 suffix
continuations (word V.∷ rest) suffix = T.accepted 128 191 _ (B.continuationByte word) _ _ suffix T.complete
  (Admission.continuation word) (continuations rest suffix)

restricted : ∀ {count} lower upper word (rest : V.Vec (Word 6) count) suffix →
  T.Between lower upper (B.continuationByte word) →
  T.Tail lower upper (suc count)
    ((B.continuationByte word ∷ map B.continuationByte (V.toList rest)) ++ suffix)
    (B.continuationByte word ∷ map B.continuationByte (V.toList rest)) suffix T.complete
restricted lower upper word rest suffix admitted = T.accepted lower upper _ (B.continuationByte word) _ _ suffix T.complete
  admitted (continuations rest suffix)

head : P.Raw → Byte
head (P.one word) = B.singleByte word
head (P.two high low) = B.twoByte high
head (P.three high middle low) = B.threeByte high
head (P.four high middle next low) = B.fourByte high

tail : P.Raw → List Byte
tail (P.one word) = []
tail (P.two high low) = B.continuationByte low ∷ []
tail (P.three high middle low) = B.continuationByte middle ∷ B.continuationByte low ∷ []
tail (P.four high middle next low) = B.continuationByte middle ∷ B.continuationByte next ∷ B.continuationByte low ∷ []

split : ∀ raw suffix → P.encode raw ++ suffix ≡ head raw ∷ (tail raw ++ suffix)
split (P.one word) suffix = refl
split (P.two high low) suffix = refl
split (P.three high middle low) suffix = refl
split (P.four high middle next low) suffix = refl

reference : ∀ raw → P.Canonical raw → ∀ suffix → G.Group (head raw) (tail raw ++ suffix)
reference (P.one word) canonical suffix = G.single (Admission.single word)
reference (P.two high low) canonical suffix = G.multiple G.two (Admission.two high low canonical)
  (T.readResult (tail (P.two high low)) suffix T.complete
    (restricted 128 191 low V.[] suffix (Admission.continuation low)))
reference (P.three high middle low) canonical suffix = G.multiple G.three (Admission.three high)
  (T.readResult (tail (P.three high middle low)) suffix T.complete
    (restricted (proj₁ (G.secondRange G.three (B.threeByte high))) (proj₂ (G.secondRange G.three (B.threeByte high)))
      middle (low V.∷ V.[]) suffix (Admission.threeSecond high middle low canonical)))
reference (P.four high middle next low) canonical suffix = G.multiple G.four (Admission.four high middle next low canonical)
  (T.readResult (tail (P.four high middle next low)) suffix T.complete
    (restricted (proj₁ (G.secondRange G.four (B.fourByte high))) (proj₂ (G.secondRange G.four (B.fourByte high)))
      middle (next V.∷ low V.∷ V.[]) suffix (Admission.fourSecond high middle next low canonical)))

referenceConsumed : ∀ raw canonical suffix → G.consumed (reference raw canonical suffix) ≡ P.encode raw
referenceConsumed (P.one word) canonical suffix = refl
referenceConsumed (P.two high low) canonical suffix = refl
referenceConsumed (P.three high middle low) canonical suffix = refl
referenceConsumed (P.four high middle next low) canonical suffix = refl

referenceRemaining : ∀ raw canonical suffix → G.remaining (reference raw canonical suffix) ≡ suffix
referenceRemaining (P.one word) canonical suffix = refl
referenceRemaining (P.two high low) canonical suffix = refl
referenceRemaining (P.three high middle low) canonical suffix = refl
referenceRemaining (P.four high middle next low) canonical suffix = refl

referenceValid : ∀ raw canonical suffix → G.valid (reference raw canonical suffix) ≡ true
referenceValid (P.one word) canonical suffix = refl
referenceValid (P.two high low) canonical suffix = refl
referenceValid (P.three high middle low) canonical suffix = refl
referenceValid (P.four high middle next low) canonical suffix = refl

referenceView : ∀ raw canonical suffix → Complete.view (reference raw canonical suffix) ≡ (P.encode raw , suffix , true)
referenceView (P.one word) canonical suffix = refl
referenceView (P.two high low) canonical suffix = refl
referenceView (P.three high middle low) canonical suffix = refl
referenceView (P.four high middle next low) canonical suffix = refl

readPacket : ∀ raw canonical suffix → Complete.view (G.read (head raw) (tail raw ++ suffix)) ≡ (P.encode raw , suffix , true)
readPacket raw canonical suffix = trans (Complete.readComplete (reference raw canonical suffix)) (referenceView raw canonical suffix)
