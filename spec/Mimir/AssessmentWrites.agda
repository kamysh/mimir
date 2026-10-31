{-# OPTIONS --safe #-}
-- Exact application write expressions for immutable assessment rows. Arithmetic
-- is an external operation boundary: these terms specify the Rust evaluation
-- order without equating floating results to ideal rational arithmetic or
-- reimplementing a formatter/float library. SQL encoding and arithmetic
-- execution correspondence remain separate obligations.
module Mimir.AssessmentWrites where

open import Data.List using (List; []; _∷_; map; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym)
open import Mimir.Binary64 using (Number)
open import Mimir.Text using (Text)
open import Mimir.NumericValidation using (Axis)
open import Mimir.LearningSchema using (Assessment; Target; existing; candidate)
import Mimir.ReviewSchema as Reviews
import Mimir.ReviewResolution as Resolution

data Term : Set where
  literal : Number → Term
  zero one : Term
  multiply subtract : Term → Term → Term

estimate : Axis → Term
estimate a with Axis.estimate a
... | nothing = zero
... | just value = literal value

record Values : Set where
  constructor values
  field positive negative benefit weight : Term

calculate : Assessment → Values
calculate a = values
  (multiply (literal (Axis.weight (Assessment.correctness a))) (estimate (Assessment.correctness a)))
  (multiply (literal (Axis.weight (Assessment.correctness a))) (subtract one (estimate (Assessment.correctness a))))
  (multiply (literal (Axis.weight (Assessment.usefulness a))) (estimate (Assessment.usefulness a)))
  (literal (Axis.weight (Assessment.usefulness a)))

module Applied = Resolution.Apply [] []

targetID : (target : Target) → Applied.Existing target → ℕ
targetID (existing identity) proof = identity
targetID (candidate name) ()

targetExact : ∀ target proof → target ≡ existing (targetID target proof)
targetExact (existing identity) proof = refl
targetExact (candidate name) ()

record Row : Set where
  constructor row
  field
    experience revision belief : ℕ
    payload : Assessment
    calculated : Values

-- Scope/rubric and numeric inputs are taken from the same stored payload.
-- The SQL adapter must bind these projections, not independent caller values.
scope : Row → Text
scope entry = Assessment.scope (Row.payload entry)

rubric : Row → Text
rubric entry = Assessment.rubric (Row.payload entry)

-- existing is injective, so this is the physical belief/scope/rubric key in
-- the same carrier used by post-resolution review validation.
key : Row → Reviews.AssessmentKey
key entry = existing (Row.belief entry) , scope entry , rubric entry

Owned : ℕ → ℕ → Row → Set
Owned experience revision entry = Row.experience entry ≡ experience ×
  (Row.revision entry ≡ revision ×
  (Assessment.target (Row.payload entry) ≡ existing (Row.belief entry) ×
    Row.calculated entry ≡ calculate (Row.payload entry)))

write : ℕ → ℕ → (a : Assessment) → Applied.Existing (Assessment.target a) → Row
write experience revision a resolved = row experience revision
  (targetID (Assessment.target a) resolved) a (calculate a)

writeOwned : ∀ experience revision a resolved → Owned experience revision (write experience revision a resolved)
writeOwned experience revision a resolved = refl , refl , targetExact (Assessment.target a) resolved , refl

writes : ℕ → ℕ → (assessments : List Assessment) → All (λ a → Applied.Existing (Assessment.target a)) assessments → List Row
writes experience revision = Resolution.mapEvidence (write experience revision)

allOwned : ∀ experience revision assessments resolved → All (Owned experience revision) (writes experience revision assessments resolved)
allOwned experience revision assessments resolved = Resolution.mapEvidenceAll (write experience revision)
  (writeOwned experience revision) assessments resolved

countExact : ∀ experience revision assessments resolved → length (writes experience revision assessments resolved) ≡ length assessments
countExact experience revision assessments resolved = Resolution.mapEvidenceLength (write experience revision)
  assessments resolved

payloadsExact : ∀ experience revision assessments resolved → map Row.payload (writes experience revision assessments resolved) ≡ assessments
payloadsExact experience revision [] [] = refl
payloadsExact experience revision (a ∷ rest) (resolved ∷ remaining) = cong (a ∷_) (payloadsExact experience revision rest remaining)

writeKey : ∀ experience revision a resolved → key (write experience revision a resolved) ≡ Reviews.assessmentKey a
writeKey experience revision a resolved = cong (λ target → target , Assessment.scope a , Assessment.rubric a)
  (sym (targetExact (Assessment.target a) resolved))

keysExact : ∀ experience revision assessments resolved →
  map key (writes experience revision assessments resolved) ≡
  map Reviews.assessmentKey assessments
keysExact experience revision [] [] = refl
keysExact experience revision (a ∷ rest) (resolved ∷ remaining) = cong₂ _∷_ (writeKey experience revision a resolved)
  (keysExact experience revision rest remaining)

-- Primary-key uniqueness is checked after target resolution: two distinct
-- candidate names can otherwise alias the same belief/scope/rubric tuple.
uniqueKeys : ∀ experience revision assessments resolved →
  Reviews.AssessmentKeys.Unique (map Reviews.assessmentKey assessments) →
  Reviews.AssessmentKeys.Unique
    (map key (writes experience revision assessments resolved))
uniqueKeys experience revision assessments resolved unique rewrite keysExact experience revision assessments resolved = unique
