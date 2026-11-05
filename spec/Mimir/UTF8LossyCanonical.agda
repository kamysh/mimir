{-# OPTIONS --safe #-}
-- Every group accepted by the lossy byte checks is an actual canonical
-- scalar, with exactly the original bytes. This closes the validity bridge.
module Mimir.UTF8LossyCanonical where

open import Data.Bool using (true)
open import Data.Fin using (toℕ)
open import Data.List using ([]; _∷_)
import Data.Vec as V
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans)
import Mimir.UTF8Byte as B
import Mimir.UTF8ByteDecode as Decode
import Mimir.UTF8Packet as P
import Mimir.UTF8CanonicalBounds as Bounds
import Mimir.UTF8LossyGroup as G
import Mimir.UTF8LossyTail as T
import Mimir.UTF8LossyPayload as Tail
import Mimir.UTF8LossyConditions as Conditions
import Mimir.Bits as Bits

Decoded : ∀ {byte input} → G.Group byte input → Set
Decoded group = Σ P.Scalar (λ value → G.consumed group ≡ P.encode (P.Scalar.raw value))

decode : ∀ {byte input} (group : G.Group byte input) → G.valid group ≡ true → Decoded group
decode {byte} (G.single ordinary) accepted with Decode.singlePayload byte ordinary
... | word , exact = P.scalar (P.one word) (Bounds.oneCanonical word) , cong (_∷ []) exact
decode (G.badHead unsupported) ()
decode (G.multiple width leading (T.readResult consumed remaining T.interrupted meaning)) ()
decode {byte} (G.multiple G.two leading (T.readResult consumed remaining T.complete meaning)) accepted
  with Decode.twoPayload byte (≤-trans (Bounds.padding 192 2) (proj₁ leading) , proj₂ leading) |
    Tail.decode ≤-refl ≤-refl meaning
... | high , exactHead | Tail.decoded (low V.∷ V.[]) exactTail first =
  P.scalar (P.two high low) (Bounds.twoCanonical high low
    (Conditions.shiftLower (Bits.Binary.value high) 192 (toℕ byte) 2
      (trans (cong toℕ exactHead) (B.twoNumeric high)) (proj₁ leading))) , cong₂ _∷_ exactHead exactTail
decode {byte} (G.multiple G.three leading (T.readResult consumed remaining T.complete meaning)) accepted
  with Decode.threePayload byte leading |
    Tail.decode (proj₁ (Conditions.secondBounds G.three byte)) (proj₂ (Conditions.secondBounds G.three byte)) meaning
... | high , exactHead | Tail.decoded (middle V.∷ low V.∷ V.[]) exactTail first
  with Conditions.threeConditions byte high middle exactHead first
... | minimum , surrogate = P.scalar (P.three high middle low) (Bounds.threeCanonical high middle low minimum surrogate) ,
  cong₂ _∷_ exactHead exactTail
decode {byte} (G.multiple G.four leading (T.readResult consumed remaining T.complete meaning)) accepted
  with Decode.fourPayload byte (proj₁ leading , ≤-trans (proj₂ leading) (Bounds.padding 244 3)) |
    Tail.decode (proj₁ (Conditions.secondBounds G.four byte)) (proj₂ (Conditions.secondBounds G.four byte)) meaning
... | high , exactHead | Tail.decoded (middle V.∷ next V.∷ low V.∷ V.[]) exactTail first
  with Conditions.fourConditions byte high middle exactHead leading first
... | minimum , maximum = P.scalar (P.four high middle next low) (Bounds.fourCanonical high middle next low minimum maximum) ,
  cong₂ _∷_ exactHead exactTail
