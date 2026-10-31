{-# OPTIONS --safe #-}
-- Lexicographic order on UTF-8 byte codes. Decoding constructs bounded keys;
-- the order itself is total on arbitrary natural-number sequences.
module Mimir.ByteKeyOrder where

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
import Data.Nat.Properties as Nat
open import Data.Empty using (⊥)
open import Relation.Binary.Definitions using (Tri; tri<; tri≈; tri>)
open import Relation.Binary.Bundles using (StrictTotalOrder)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.List.Relation.Binary.Lex.Strict as Lex
import Data.List.Relation.Binary.Pointwise as Pointwise

Key = List ℕ
module Order = StrictTotalOrder (Lex.<-strictTotalOrder Nat.<-strictTotalOrder)
open Order public using (_<_; trans)

pointwiseRefl : (key : Key) → Pointwise.Pointwise _≡_ key key
pointwiseRefl [] = Pointwise.[]
pointwiseRefl (byte ∷ rest) = refl Pointwise.∷ pointwiseRefl rest

pointwiseEquality : ∀ {first second : Key} → Pointwise.Pointwise _≡_ first second → first ≡ second
pointwiseEquality Pointwise.[] = refl
pointwiseEquality (refl Pointwise.∷ rest) rewrite pointwiseEquality rest = refl

equalityPointwise : ∀ {first second : Key} → first ≡ second → Pointwise.Pointwise _≡_ first second
equalityPointwise {first} refl = pointwiseRefl first

compare : ∀ first second → Tri (first < second) (first ≡ second) (second < first)
compare first second with Order.compare first second
... | tri< before different notAfter = tri< before (λ same → different (equalityPointwise same)) notAfter
... | tri≈ notBefore same notAfter = tri≈ notBefore (pointwiseEquality same) notAfter
... | tri> notBefore different after = tri> notBefore (λ same → different (equalityPointwise same)) after

irreflexive : ∀ key → key < key → ⊥
irreflexive key = Order.irrefl (pointwiseRefl key)
