{-# OPTIONS --safe #-}
-- Every lossy output is a complete valid UTF-8 sequence. The replacement
-- literal is part of the specified output alphabet, not a regression input.
module Mimir.UTF8LossyValid where

open import Data.Bool using (true; false)
open import Data.Fin using (#_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans; sym)
import Mimir.UTF8Packet as P
import Mimir.UTF8Text as UTF8
import Mimir.UTF8LossyGroup as G
import Mimir.UTF8LossyBytes as Lossy
import Mimir.UTF8LossyCanonical as Canonical

oneDecoded : ∀ bytes (value : P.Scalar) → bytes ≡ P.encode (P.Scalar.raw value) → UTF8.Decoded bytes
oneDecoded bytes value exact = UTF8.decoded (value ∷ [])
  (trans exact (sym (++-identityʳ (P.encode (P.Scalar.raw value)))))

replacement : UTF8.Decoded Lossy.replacement
replacement with Canonical.decode (G.read (# 239) (# 191 ∷ # 189 ∷ [])) refl
... | value , exact = oneDecoded Lossy.replacement value exact

groupDecoded : ∀ {byte input} (group : G.Group byte input) → UTF8.Decoded (Lossy.renderPiece (Lossy.fromGroup group))
groupDecoded group with G.valid group in admitted
... | false = replacement
... | true with Canonical.decode group admitted
...   | value , exact = oneDecoded (G.consumed group) value exact

encodeAppend : ∀ (first second : List P.Scalar) → UTF8.encode (first ++ second) ≡ UTF8.encode first ++ UTF8.encode second
encodeAppend [] second = refl
encodeAppend (value ∷ first) second rewrite encodeAppend first second =
  sym (++-assoc (P.encode (P.Scalar.raw value)) (UTF8.encode first) (UTF8.encode second))

appendDecoded : ∀ {first second} → UTF8.Decoded first → UTF8.Decoded second → UTF8.Decoded (first ++ second)
appendDecoded (UTF8.decoded first exactFirst) (UTF8.decoded second exactSecond) = UTF8.decoded (first ++ second)
  (trans (cong₂ _++_ exactFirst exactSecond) (sym (encodeAppend first second)))

partitionDecoded : ∀ {input pieces} → Lossy.Partition input pieces → UTF8.Decoded (Lossy.render pieces)
partitionDecoded Lossy.empty = UTF8.decoded [] refl
partitionDecoded (Lossy.next byte input group meaning) = appendDecoded (groupDecoded group) (partitionDecoded meaning)

decoded : ∀ input → UTF8.Decoded (Lossy.decode input)
decoded input with Lossy.parse input
... | pieces , meaning = partitionDecoded meaning
