{-# OPTIONS --safe #-}
module Mimir.SourceProtocol where

open import Data.Nat using (ℕ) renaming (_≟_ to _≟ℕ_)
open import Data.Char using (Char) renaming (_≟_ to _≟Char_)
open import Data.List using (List; _++_)
open import Data.List.Properties using (≡-dec)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.Empty using (⊥-elim)
open import Mimir.SourceText
open import Mimir.Text using (Text)
open import Mimir.SourceSchema using (Provenance)
import Mimir.SourceSchema as Schema

-- Internal ranges count Unicode scalars, so a selected span cannot split an
-- encoded character. The public legacy quotation remains an unchanged string.
open Selection Char
open Matching Char _≟Char_

Actor = Text
_≟Text_ = ≡-dec _≟Char_

record Source : Set where
  constructor source
  field
    identity : Text
    revision : ℕ
    actor : Actor
    provenance : Provenance
    raw : Text

contextualize : ℕ → Schema.Source → Source
contextualize revision s = source (Schema.Source.reference s) revision
  (Schema.Source.actor s) (Schema.Source.provenance s) (Schema.Source.text s)

record Request : Set where
  constructor request
  field
    identity : Text
    revision offset countMinusOne : ℕ

data Error : Set where wrongSource staleRevision outOfBounds : Error

record Quotation (s : Source) : Set where
  constructor quoted
  field
    offset countMinusOne : ℕ
    location : Location offset countMinusOne (Source.raw s)

data Answer (s : Source) : Set where
  selected : Quotation s → Answer s
  rejected : Error → Answer s

resolve : (s : Source) → Request → Answer s
resolve s r with Request.identity r ≟Text Source.identity s
... | no _ = rejected wrongSource
... | yes _ with Request.revision r ≟ℕ Source.revision s
...   | no _ = rejected staleRevision
...   | yes _ with select (Request.offset r) (Request.countMinusOne r) (Source.raw s)
...     | nothing = rejected outOfBounds
...     | just location = selected (quoted (Request.offset r) (Request.countMinusOne r) location)

foreignSourceRefused : ∀ s r → Request.identity r ≢ Source.identity s →
  resolve s r ≡ rejected wrongSource
foreignSourceRefused s r different with Request.identity r ≟Text Source.identity s
... | no _ = refl
... | yes same = ⊥-elim (different same)

staleRevisionRefused : ∀ s r → Request.identity r ≡ Source.identity s →
  Request.revision r ≢ Source.revision s → resolve s r ≡ rejected staleRevision
staleRevisionRefused s r same different with Request.identity r ≟Text Source.identity s
... | no unequal = ⊥-elim (unequal same)
... | yes _ with Request.revision r ≟ℕ Source.revision s
...   | no _ = refl
...   | yes equal = ⊥-elim (different equal)

-- The quotation stores neither a model-supplied actor nor replacement text.
quotationActor : ∀ {s} → Quotation s → Actor
quotationActor {s} q = Source.actor s

quotationProvenance : ∀ {s} → Quotation s → Provenance
quotationProvenance {s} q = Source.provenance s

actorPreserved : ∀ {s} (q : Quotation s) → quotationActor q ≡ Source.actor s
actorPreserved q = refl

provenancePreserved : ∀ {s} (q : Quotation s) →
  quotationProvenance q ≡ Source.provenance s
provenancePreserved q = refl

-- Resolving a source request is observational: it cannot commit a review or
-- alter any store. Store is universally quantified, not assumed to be a unit.
resolveIn : ∀ {Store : Set} → Store → (s : Source) → Request → Store × Answer s
resolveIn store s r = store , resolve s r

storePreserved : ∀ {Store : Set} (store : Store) s r →
  Data.Product.proj₁ (resolveIn store s r) ≡ store
storePreserved store s r = refl

-- The legacy wire contract remains literal containment. Already valid legacy
-- text is accepted unchanged; spans produce text satisfying the same relation.
record Accepted (s : Source) : Set where
  constructor accepted
  field
    text : Text
    contained : Contains text (Source.raw s)

matchLegacy : (s : Source) → Text → Maybe (Accepted s)
matchLegacy s text with contains? text (Source.raw s)
... | yes proof = just (accepted text proof)
... | no _ = nothing

legacyComplete : ∀ s text → Contains text (Source.raw s) →
  Σ (Accepted s) (λ result →
    (matchLegacy s text ≡ just result) × (Accepted.text result ≡ text))
legacyComplete s text proof with contains? text (Source.raw s)
... | yes found = accepted text found , (refl , refl)
... | no absent = ⊥-elim (absent proof)

selectedSatisfiesLegacy : ∀ {s} (q : Quotation s) →
  Σ (Accepted s) (λ result →
    (matchLegacy s (quotation (Quotation.location q)) ≡ just result) ×
    (Accepted.text result ≡ quotation (Quotation.location q)))
selectedSatisfiesLegacy {s} q = legacyComplete s
  (quotation (Quotation.location q)) (selectedQuoteContained (Quotation.location q))
