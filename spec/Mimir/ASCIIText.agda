{-# OPTIONS --safe #-}
-- Every ASCII byte sequence has a canonical UTF-8 decoding with unchanged
-- bytes; the bound is evidence, not a lossy conversion or unchecked cast.
module Mimir.ASCIIText where

open import Data.Fin using (toℕ)
open import Data.Fin.Properties using (toℕ-injective)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (_<_; z≤n)
open import Data.Nat.Properties using (≤-trans; <⇒≤)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong₂; sym)
open import Mimir.Bits using (Byte)
import Mimir.Bits as Bits
import Mimir.UTF8Byte as B
import Mimir.UTF8Packet as Packet
import Mimir.UTF8Text as UTF8
import Mimir.UnicodeScalar as Scalar

ASCII : Byte → Set
ASCII byte = toℕ byte < 128

record Single (byte : Byte) : Set where
  constructor single
  field value : Packet.Scalar; exact : byte ∷ [] ≡ Packet.encode (Packet.Scalar.raw value)

abstract
  make : ∀ byte → ASCII byte → Single byte
  make byte small = single (Packet.scalar (Packet.one word) canonical) (cong (_∷ []) (sym byteExact))
    where
    word : Bits.Word 7
    word = Bits.Binary.Expansion.digits (Bits.Binary.encode 7 (toℕ byte) small)
    wordExact : Bits.Binary.value word ≡ toℕ byte
    wordExact = Bits.Binary.decodeEncode 7 (toℕ byte) small
    byteExact : B.singleByte word ≡ byte
    byteExact = toℕ-injective (trans (B.singleNumeric word) wordExact)
    pointExact : Packet.codePoint (Packet.one word) ≡ toℕ byte
    pointExact = trans (Packet.fromSevenValue word) wordExact
    valid : Scalar.Valid (toℕ byte)
    valid = ≤-trans (<⇒≤ small) (Scalar.padding 128 1113983) ,
      inj₁ (≤-trans small (Scalar.padding 128 55168))
    canonical : Packet.Canonical (Packet.one word)
    canonical = Scalar.canonicalFromNumber (Packet.one word) (toℕ byte) 0 pointExact refl z≤n valid

prepend : ∀ {byte bytes} → Single byte → UTF8.Decoded bytes → UTF8.Decoded (byte ∷ bytes)
prepend (single value exact) (UTF8.decoded values later) = UTF8.decoded (value ∷ values)
  (cong₂ Data.List._++_ exact later)

decode : ∀ {bytes} → All ASCII bytes → UTF8.Decoded bytes
decode [] = UTF8.decoded [] refl
decode {byte ∷ bytes} (small ∷ rest) = prepend (make byte small) (decode rest)
