{-# OPTIONS --safe #-}
-- Every fully accepted continuation tail is represented by its actual
-- six-bit words; restricted first-byte bounds remain available to canonicality.
module Mimir.UTF8LossyPayload where

open import Data.List using (List; []; _∷_; map)
import Data.Vec as V
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂; subst)
open import Mimir.Bits using (Byte; Word)
import Mimir.UTF8Byte as B
import Mimir.UTF8ByteDecode as Decode
import Mimir.UTF8LossyTail as T

First : ∀ {count} → ℕ → ℕ → V.Vec (Word 6) count → Set
First lower upper V.[] = ⊤
First lower upper (word V.∷ rest) = T.Between lower upper (B.continuationByte word)

record Decoded (lower upper count : ℕ) (consumed : List Byte) : Set where
  constructor decoded
  field
    words : V.Vec (Word 6) count
    exact : consumed ≡ map B.continuationByte (V.toList words)
    first : First lower upper words

weaken : ∀ lower upper byte → 128 ≤ lower → upper ≤ 191 → T.Between lower upper byte → T.Between 128 191 byte
weaken lower upper byte low high (above , below) = ≤-trans low above , ≤-trans below high

decode : ∀ {lower upper count input consumed remaining} → 128 ≤ lower → upper ≤ 191 →
  T.Tail lower upper count input consumed remaining T.complete → Decoded lower upper count consumed
decode low high (T.done lower upper input) = decoded V.[] refl tt
decode low high (T.accepted lower upper count byte input consumed remaining .T.complete bound rest)
  with Decode.continuationPayload byte (weaken lower upper byte low high bound) | decode ≤-refl ≤-refl rest
... | word , exactByte | decoded words exactTail first = decoded (word V.∷ words)
  (cong₂ _∷_ exactByte exactTail) (subst (T.Between lower upper) exactByte bound)
