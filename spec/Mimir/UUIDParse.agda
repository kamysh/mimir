{-# OPTIONS --safe #-}
-- The plain UUID parser used by serde's JSON string visitor. Failure retains
-- the exact inner/original slice and requested format used by uuid 1.28.0.
module Mimir.UUIDParse where

open import Data.Fin using (#_)
import Data.Fin as Fin
open import Data.List using (List; []; _∷_; _++_; length; take; drop)
open import Data.List.Properties using (++-identityʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym)
open import Mimir.Bits using (Byte)
import Mimir.HexBytes as Hex
import Mimir.UUIDGroups as G
import Mimir.UUIDHyphenated as H

data Requested : Set where any hyphenated : Requested
record Failure : Set where
  constructor failure
  field source : List Byte; requested : Requested

data Result : Set where
  accepted : G.UUID → Result
  rejected : Failure → Result

finish : List Byte → Requested → Maybe (G.UUID × List Byte) → Result
finish input requested nothing = rejected (failure input requested)
finish input requested (just (value , [])) = accepted value
finish input requested (just (value , byte ∷ rest)) = rejected (failure input requested)

hyphenatedSized : ℕ → List Byte → Result
hyphenatedSized size input with size ≟ 36
... | yes sized = finish input hyphenated (H.decode input)
... | no wrongSize = rejected (failure input hyphenated)

readHyphenated : List Byte → Result
readHyphenated input = hyphenatedSized (length input) input

-- Prefix pairs are exact lowercase/uppercase alternatives. In particular,
-- punctuation is not matched by blindly setting bit 0x20 on every byte.
urnPrefix : List (Byte × Byte)
urnPrefix = ((# 117) , (# 85)) ∷ ((# 114) , (# 82)) ∷ ((# 110) , (# 78)) ∷
  ((# 58) , (# 58)) ∷ ((# 117) , (# 85)) ∷ ((# 117) , (# 85)) ∷
  ((# 105) , (# 73)) ∷ ((# 100) , (# 68)) ∷ ((# 58) , (# 58)) ∷ []

prefix : List (Byte × Byte) → List Byte → Maybe (List Byte)
prefix [] input = just input
prefix (pair ∷ expected) [] = nothing
prefix ((lower , upper) ∷ expected) (byte ∷ input) with byte Fin.≟ lower
... | yes lowercase = prefix expected input
... | no notLower with byte Fin.≟ upper
...   | yes uppercase = prefix expected input
...   | no notUpper = nothing

braced : List Byte → Result
braced [] = rejected (failure [] any)
braced input@(first ∷ rest) with first Fin.≟ (# 123)
... | no noOpen = rejected (failure input any)
... | yes opened with drop 36 rest
...   | [] = rejected (failure input any)
...   | last ∷ next ∷ following = rejected (failure input any)
...   | last ∷ [] with last Fin.≟ (# 125)
...     | no noClose = rejected (failure input any)
...     | yes closed = readHyphenated (take 36 rest)

urn : List Byte → Result
urn input with prefix urnPrefix input
... | nothing = rejected (failure input any)
... | just body = readHyphenated body

readSized : ℕ → List Byte → Result
readSized size input with size ≟ 32
... | yes simple = finish input any (Hex.read 16 input)
... | no notSimple with size ≟ 36
...   | yes regular = readHyphenated input
...   | no notRegular with size ≟ 38
...     | yes wrapped = braced input
...     | no notWrapped with size ≟ 45
...       | yes prefixed = urn input
...       | no invalidSize = rejected (failure input any)

read : List Byte → Result
read input = readSized (length input) input

decodeCanonical : ∀ value → H.decode (H.encode value) ≡ just (value , [])
decodeCanonical value = trans (cong H.decode (sym (++-identityʳ (H.encode value)))) (H.uuidRoundTrip value [])

canonicalRoundTrip : ∀ value → read (H.encode value) ≡ accepted value
canonicalRoundTrip value = trans (cong (λ size → readSized size (H.encode value)) (H.uuidLength value))
  (trans (cong (λ size → hyphenatedSized size (H.encode value)) (H.uuidLength value))
    (cong (finish (H.encode value) hyphenated) (decodeCanonical value)))

decodeSimple : ∀ value → Hex.read 16 (Hex.encode value) ≡ just (value , [])
decodeSimple value = trans (cong (Hex.read 16) (sym (++-identityʳ (Hex.encode value)))) (Hex.roundTrip value [])

simpleRoundTrip : ∀ value → read (Hex.encode value) ≡ accepted value
simpleRoundTrip value = trans (cong (λ size → readSized size (Hex.encode value)) (Hex.encodedLength value))
  (cong (finish (Hex.encode value) any) (decodeSimple value))
