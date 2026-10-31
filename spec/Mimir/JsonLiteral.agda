{-# OPTIONS --safe #-}
-- UTF-8 packets admitted verbatim by the JSON string serializer. Numeric
-- scalar conditions are connected to every actual emitted byte.
module Mimir.JsonLiteral where

open import Data.Fin using (#_; toℕ)
open import Data.List using (List; []; _∷_; _++_; map)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.All using (All)
open import Data.Nat using (ℕ; suc; _+_; _≤_; _<_; s≤s)
open import Data.Nat.Properties using (m≤m+n; m≤n+m; ≤-trans; ≤-<-trans; <-irrefl)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Mimir.Bits using (Byte)
import Mimir.Bits as Bits
import Mimir.UTF8Byte as B
import Mimir.UTF8Packet as Packet
import Mimir.JsonString as String

Regular : ℕ → Set
Regular number = 32 ≤ number × (number ≢ 34 × number ≢ 92)

fromNumeric : ∀ byte number → toℕ byte ≡ number → Regular number → String.Literal byte
fromNumeric byte number same (large , notQuote , notSlash) =
  subst (32 ≤_) (sym same) large ,
  (λ equal → notQuote (trans (sym same) (cong toℕ equal))) ,
  (λ equal → notSlash (trans (sym same) (cong toℕ equal)))

abstract
  padding : ∀ number extra → number ≤ number + extra
  padding = m≤m+n

  belowPadding : ∀ number extra → number < suc (number + extra)
  belowPadding number extra = s≤s (m≤m+n number extra)

differentBelow : ∀ number target → 128 ≤ number → target < 128 → number ≢ target
differentBelow number .number lower upper refl = <-irrefl refl (≤-<-trans lower upper)

aboveASCII : ∀ byte → 128 ≤ toℕ byte → String.Literal byte
aboveASCII byte lower = fromNumeric byte (toℕ byte) refl
  (≤-trans (padding 32 96) lower ,
    differentBelow (toℕ byte) 34 lower (belowPadding 34 93) ,
    differentBelow (toℕ byte) 92 lower (belowPadding 92 35))

offset : ∀ byte payload base → toℕ byte ≡ payload + base → 128 ≤ base → String.Literal byte
offset byte payload base same lower = aboveASCII byte
  (subst (128 ≤_) (sym same) (≤-trans lower (m≤n+m base payload)))

continuation : ∀ payload → String.Literal (B.continuationByte payload)
continuation payload = offset (B.continuationByte payload) (Bits.Binary.value payload) 128
  (B.continuationNumeric payload) (padding 128 0)

packetLiteral : ∀ raw → Regular (Packet.codePoint raw) → All String.Literal (Packet.encode raw)
packetLiteral (Packet.one payload) regular = fromNumeric (B.singleByte payload) (Packet.codePoint (Packet.one payload))
  (trans (B.singleNumeric payload) (sym (Packet.fromSevenValue payload))) regular All.∷ All.[]
packetLiteral (Packet.two high low) regular =
  offset (B.twoByte high) (Bits.Binary.value high) 192 (B.twoNumeric high) (padding 128 64) All.∷
  continuation low All.∷ All.[]
packetLiteral (Packet.three high middle low) regular =
  offset (B.threeByte high) (Bits.Binary.value high) 224 (B.threeNumeric high) (padding 128 96) All.∷
  continuation middle All.∷ continuation low All.∷ All.[]
packetLiteral (Packet.four high middle next low) regular =
  offset (B.fourByte high) (Bits.Binary.value high) 240 (B.fourNumeric high) (padding 128 112) All.∷
  continuation middle All.∷ continuation next All.∷ continuation low All.∷ All.[]

literalBody : List Byte → String.Body
literalBody = map String.literal

literalValid : ∀ {bytes} → All String.Literal bytes → String.ValidBody (literalBody bytes)
literalValid All.[] = All.[]
literalValid (valid All.∷ rest) = valid All.∷ literalValid rest

literalOutput : ∀ bytes (valid : All String.Literal bytes) →
  String.bodyOutput (literalBody bytes) (literalValid valid) ≡ bytes
literalOutput [] All.[] = refl
literalOutput (byte ∷ rest) (valid All.∷ remaining) = cong (byte ∷_) (literalOutput rest remaining)
