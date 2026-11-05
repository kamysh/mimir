{-# OPTIONS --safe #-}
-- Typed record decoding after tokenization. The caller selects whether the
-- input is a raw object or a last-write-normalized serde_json::Value object.
module Mimir.RecordDecoding where

open import Data.List using (List; []; _∷_)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ-syntax; _,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.Validation
open import Mimir.StructuredValue
open import Mimir.JsonObjects using (UnknownPolicy; DuplicatePolicy)

infixl 1 _>>=_
_>>=_ : ∀ {A B : Set} → Fault ⊎ A → (A → Fault ⊎ B) → Fault ⊎ B
inj₁ failure >>= next = inj₁ failure
inj₂ value >>= next = next value

mapResult : ∀ {A B : Set} → (A → B) → Fault ⊎ A → Fault ⊎ B
mapResult f result = result >>= λ value → inj₂ (f value)

readRecord : ∀ {A : Set} → UnknownPolicy → DuplicatePolicy → List Text →
  (Object.View → Fault ⊎ A) → Value → Fault ⊎ A
readRecord unknownPolicy duplicates names decode raw = asObject raw >>= λ fields →
  inspect fields
  where
  inspect : Object.Fields → _
  inspect fields with Object.checkUnknowns unknownPolicy names fields
  ... | rejected failure invalid = inj₁ failure
  ... | accepted known with Object.checkDuplicates duplicates names fields
  ...   | rejected failure invalid = inj₁ failure
  ...   | accepted unique = decode (Object.normalize fields)

readElementsFrom : ∀ {A : Set} → ℕ → (Value → Fault ⊎ A) → List Value → Fault ⊎ List A
readElementsFrom offset decode [] = inj₂ []
readElementsFrom offset decode (raw ∷ rest) with decode raw
... | inj₁ failure = inj₁ (prependPath (index offset) failure)
... | inj₂ value = mapResult (value ∷_) (readElementsFrom (suc offset) decode rest)

readArray : ∀ {A : Set} → (Value → Fault ⊎ A) → Value → Fault ⊎ List A
readArray decode raw = asArray raw >>= readElementsFrom 0 decode

validateDecoded : ∀ {A : Set} {P : A → Set} → ((a : A) → Checked (P a)) →
  Fault ⊎ A → Fault ⊎ (Σ[ a ∈ A ] P a)
validateDecoded validator (inj₁ failure) = inj₁ failure
validateDecoded validator (inj₂ value) with validator value
... | rejected failure invalid = inj₁ failure
... | accepted proof = inj₂ (value , proof)

failureIsPreserved : ∀ {A B : Set} failure (next : A → Fault ⊎ B) →
  (inj₁ failure >>= next) ≡ inj₁ failure
failureIsPreserved failure next = refl

bindSuccess : ∀ {A B : Set} (first : Fault ⊎ A) (next : A → Fault ⊎ B) value →
  (first >>= next) ≡ inj₂ value →
  Σ[ intermediate ∈ A ] (first ≡ inj₂ intermediate × next intermediate ≡ inj₂ value)
bindSuccess (inj₁ failure) next value ()
bindSuccess (inj₂ intermediate) next value observed = intermediate , refl , observed

afterSuccess : ∀ {A B : Set} {P : Set} (first : Fault ⊎ A) (next : A → Fault ⊎ B) value →
  (∀ intermediate → first ≡ inj₂ intermediate → next intermediate ≡ inj₂ value → P) →
  (first >>= next) ≡ inj₂ value → P
afterSuccess (inj₁ failure) next value property ()
afterSuccess (inj₂ intermediate) next value property observed = property intermediate refl observed

elementsRoundTrip : ∀ {A : Set} (encode : A → Value) decode →
  (∀ value → decode (encode value) ≡ inj₂ value) → ∀ offset values →
  readElementsFrom offset decode (Data.List.map encode values) ≡ inj₂ values
elementsRoundTrip encode decode roundTrip offset [] = refl
elementsRoundTrip encode decode roundTrip offset (value ∷ values)
  rewrite roundTrip value | elementsRoundTrip encode decode roundTrip (suc offset) values = refl

validDecodedAccepted : ∀ {A : Set} {P : A → Set} validator (value : A) → P value →
  Σ[ proof ∈ P value ] validateDecoded validator (inj₂ value) ≡ inj₂ (value , proof)
validDecodedAccepted validator value valid with validator value
... | accepted proof = proof , refl
... | rejected failure invalid = ⊥-elim (invalid valid)
