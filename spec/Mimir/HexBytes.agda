{-# OPTIONS --safe #-}
-- Fixed-count hexadecimal byte sequences preserve any following suffix.
module Mimir.HexBytes where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc; length-++)
import Data.Vec as V
import Data.Vec.Properties as Vec
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (*-suc; +-assoc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong₂; sym; subst)
open import Mimir.Bits using (Byte)
import Mimir.ByteHex as Hex

data Pairs : ∀ {count} → List Byte → V.Vec Byte count → List Byte → Set where
  empty : ∀ rest → Pairs rest V.[] rest
  pair : ∀ {count} high low source byte (bytes : V.Vec Byte count) rest → Hex.decode high low ≡ just byte →
    Pairs source bytes rest → Pairs (high ∷ low ∷ source) (byte V.∷ bytes) rest

read : ∀ count → List Byte → Maybe (V.Vec Byte count × List Byte)
read zero input = just (V.[] , input)
read (suc count) [] = nothing
read (suc count) (high ∷ []) = nothing
read (suc count) (high ∷ low ∷ source) with Hex.decode high low
... | nothing = nothing
... | just byte with read count source
...   | nothing = nothing
...   | just (bytes , rest) = just (byte V.∷ bytes , rest)

complete : ∀ {count source} {bytes : V.Vec Byte count} {rest} → Pairs source bytes rest → read count source ≡ just (bytes , rest)
complete (empty rest) = refl
complete (pair high low source byte bytes rest decoded later) rewrite decoded | complete later = refl

encode : ∀ {count} → V.Vec Byte count → List Byte
encode V.[] = []
encode (byte V.∷ bytes) = V.toList (Hex.pair byte) ++ encode bytes

encodedLength : ∀ {count} (bytes : V.Vec Byte count) → length (encode bytes) ≡ 2 * count
encodedLength V.[] = refl
encodedLength {suc count} (byte V.∷ bytes) = trans (length-++ (V.toList (Hex.pair byte)))
  (trans (cong₂ _+_ (Vec.length-toList (Hex.pair byte)) (encodedLength bytes)) (sym (*-suc 2 count)))

prefix : ∀ {count source} {bytes : V.Vec Byte count} {rest} pairBytes byte →
  Hex.decodePair pairBytes ≡ just byte → Pairs source bytes rest →
  Pairs (V.toList pairBytes ++ source) (byte V.∷ bytes) rest
prefix (high V.∷ low V.∷ V.[]) byte decoded later = pair high low _ byte _ _ decoded later

encodedMeaning : ∀ {count} (bytes : V.Vec Byte count) rest → Pairs (encode bytes ++ rest) bytes rest
encodedMeaning V.[] rest = empty rest
encodedMeaning (byte V.∷ bytes) rest = subst (λ input → Pairs input (byte V.∷ bytes) rest)
  (sym (++-assoc (V.toList (Hex.pair byte)) (encode bytes) rest))
  (prefix (Hex.pair byte) byte (Hex.roundTrip byte) (encodedMeaning bytes rest))

roundTrip : ∀ {count} (bytes : V.Vec Byte count) rest → read count (encode bytes ++ rest) ≡ just (bytes , rest)
roundTrip bytes rest = complete (encodedMeaning bytes rest)

sound : ∀ count source bytes rest → read count source ≡ just (bytes , rest) → Pairs source bytes rest
sound zero source .V.[] .source refl = empty source
sound (suc count) [] bytes rest ()
sound (suc count) (high ∷ []) bytes rest ()
sound (suc count) (high ∷ low ∷ source) bytes rest observed with Hex.decode high low in decoded
... | nothing with observed
...   | ()
sound (suc count) (high ∷ low ∷ source) bytes rest observed | just byte with read count source in later
... | nothing with observed
...   | ()
sound (suc count) (high ∷ low ∷ source) .(byte V.∷ bytes) .rest refl | just byte | just (bytes , rest) =
  pair high low source byte bytes rest decoded (sound count source bytes rest later)

consumedLength : ∀ {count input} {bytes : V.Vec Byte count} {rest} → Pairs input bytes rest →
  length input ≡ 2 * count + length rest
consumedLength (empty rest) = refl
consumedLength (pair {count} high low source byte bytes rest decoded later) = trans (cong (2 +_) (consumedLength later))
  (trans (sym (+-assoc 2 (2 * count) (length rest))) (cong (_+ length rest) (sym (*-suc 2 count))))
