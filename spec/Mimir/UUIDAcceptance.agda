{-# OPTIONS --safe #-}
-- Complete acceptance decision and canonicalization for every byte sequence.
module Mimir.UUIDAcceptance where

open import Data.List using (List)
open import Data.Product using (Σ; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong)
open import Mimir.Bits using (Byte)
import Mimir.UUIDGroups as G
import Mimir.UUIDHyphenated as H
import Mimir.UUIDParse as P
import Mimir.UUIDParseGrammar as Grammar
import Mimir.UUIDParseComplete as Complete

acceptedInjective : ∀ {left right} → P.accepted left ≡ P.accepted right → left ≡ right
acceptedInjective refl = refl

disjoint : ∀ {value failure} → P.accepted value ≡ P.rejected failure → ⊥
disjoint ()

unique : ∀ {input left right} → Grammar.Accepted input left → Grammar.Accepted input right → left ≡ right
unique left right = acceptedInjective (trans (sym (Complete.complete left)) (Complete.complete right))

rejectedExcludes : ∀ {input failure} → P.read input ≡ P.rejected failure →
  ¬ (Σ G.UUID (Grammar.Accepted input))
rejectedExcludes observed (value , admitted) = disjoint (trans (sym (Complete.complete admitted)) observed)

excludedRejects : ∀ input → ¬ (Σ G.UUID (Grammar.Accepted input)) →
  Σ P.Failure (λ failure → P.read input ≡ P.rejected failure)
excludedRejects input excluded with P.read input in observed
... | P.accepted value = ⊥-elim (excluded (value , Grammar.sound input value observed))
... | P.rejected diagnostic = diagnostic , refl

decide : ∀ input → Dec (Σ G.UUID (Grammar.Accepted input))
decide input with P.read input in observed
... | P.accepted value = yes (value , Grammar.sound input value observed)
... | P.rejected diagnostic = no (rejectedExcludes observed)

canonicalInjective : ∀ {left right} → H.encode left ≡ H.encode right → left ≡ right
canonicalInjective {left} {right} same = acceptedInjective
  (trans (sym (P.canonicalRoundTrip left)) (trans (cong P.read same) (P.canonicalRoundTrip right)))

canonicalMeaning : ∀ value → Grammar.Accepted (H.encode value) value
canonicalMeaning value = Grammar.sound (H.encode value) value (P.canonicalRoundTrip value)

-- Normalization preserves errors unchanged; successful inputs have exactly
-- one canonical representation. No UUID version or freshness premise occurs.
data Normalized : Set where
  canonical : List Byte → Normalized
  invalid : P.Failure → Normalized

normalizeResult : P.Result → Normalized
normalizeResult (P.accepted value) = canonical (H.encode value)
normalizeResult (P.rejected diagnostic) = invalid diagnostic

normalize : List Byte → Normalized
normalize input = normalizeResult (P.read input)

normalizeAccepted : ∀ {input value} → Grammar.Accepted input value → normalize input ≡ canonical (H.encode value)
normalizeAccepted admitted = cong normalizeResult (Complete.complete admitted)

canonicalStable : ∀ value → normalize (H.encode value) ≡ canonical (H.encode value)
canonicalStable value = cong normalizeResult (P.canonicalRoundTrip value)

failurePreserved : ∀ {input failure} → P.read input ≡ P.rejected failure → normalize input ≡ invalid failure
failurePreserved observed = cong normalizeResult observed
