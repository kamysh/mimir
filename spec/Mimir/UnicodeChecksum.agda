{-# OPTIONS --safe #-}
-- Checksum construction is defined on admitted Rust strings. Invalid Agda
-- Char sequences receive no invented replacement-byte or checksum behavior.
module Mimir.UnicodeChecksum where

open import Data.Char using (toℕ)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Mimir.Text using (Text)
open import Mimir.ExactBytes using (Bytes)
import Mimir.UnicodeScalar as Scalar
import Mimir.UnicodeText as Unicode
import Mimir.UTF8Text as UTF8
import Mimir.SHA256Hash as SHA

validIrrelevant : ∀ text (first second : Unicode.Valid text) → first ≡ second
validIrrelevant [] [] [] = refl
validIrrelevant (char ∷ rest) (first ∷ remaining) (second ∷ other) =
  cong₂ _∷_ (Scalar.validIrrelevant (toℕ char) first second) (validIrrelevant rest remaining other)

checksum : ∀ text → Unicode.Valid text → Bytes 32
checksum text valid = SHA.hash (UTF8.encode (Unicode.encodeValues valid))

proofIndependent : ∀ text (first second : Unicode.Valid text) → checksum text first ≡ checksum text second
proofIndependent text first second = cong (checksum text) (validIrrelevant text first second)
