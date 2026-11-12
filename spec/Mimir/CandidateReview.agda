{-# OPTIONS --safe #-}
-- Candidate reservation and review materialization share one prepared result.
-- Nothing is published by preparation. A later transaction must publish the
-- candidate nodes, registry and admitted review together.
module Mimir.CandidateReview where

open import Data.List using (List; length)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (just)
open import Mimir.UUIDGroups using (UUID)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.Validation using (Fault; accepted; rejected)
open import Mimir.LearningCandidates using (Candidate)
open import Mimir.LearningSchema using (Target; candidate)
open import Mimir.ReviewSchema using (Review; ReviewValid; validateReview)
import Mimir.CandidateRegistry as Registry
import Mimir.CandidateBatch as Batch
import Mimir.ReviewResolution as Resolution

record Prepared (occupied : List UUID) (before : Registry.Registry) (requested : Review) : Set where
  constructor prepared
  field
    after : Registry.Registry
    bindings : Resolution.Registry
    reservations : Batch.Batch occupied (Review.experienceID requested) before (Review.candidates requested) after bindings
    resolution : Resolution.Apply.Prepared (Review.candidates requested) bindings requested

prepareValid : ∀ occupied before requested → ReviewValid requested →
  (Candidate → UUID) → Fault ⊎ Prepared occupied before requested
prepareValid occupied before requested valid fresh
  with Batch.prepare occupied (Review.experienceID requested) before (Review.candidates requested) fresh
... | inj₁ fault = inj₁ fault
... | inj₂ (after , bindings , reservations)
  with Resolution.Apply.checkReady (Review.candidates requested) bindings requested
...   | rejected failure invalid = inj₁ failure
...   | accepted resolution
  with validateReview (Resolution.Apply.apply (Review.candidates requested) bindings requested resolution)
...     | rejected failure invalid = inj₁ failure
...     | accepted appliedValid = inj₂ (prepared after bindings reservations
  record { candidatesAgree = refl ; requestedValid = valid ; resolution = resolution ; appliedValid = appliedValid })

prepare : ∀ occupied before requested → (Candidate → UUID) → Fault ⊎ Prepared occupied before requested
prepare occupied before requested fresh with validateReview requested
... | rejected failure invalid = inj₁ failure
... | accepted valid = prepareValid occupied before requested valid fresh

materialized : ∀ {occupied before requested} → Prepared occupied before requested → Review
materialized {requested = requested} receipt = Resolution.Apply.apply (Review.candidates requested)
  (Prepared.bindings receipt) requested (Resolution.Apply.Prepared.resolution (Prepared.resolution receipt))

-- This is concrete supplied resolution, rather than an assumed function
-- from all requests to materialized contributions.
validMaterialized : ∀ {occupied before requested} (receipt : Prepared occupied before requested) →
  ReviewValid (materialized receipt)
validMaterialized receipt = Resolution.Apply.Prepared.appliedValid (Prepared.resolution receipt)

allBindingsReserved : ∀ {occupied before requested} (receipt : Prepared occupied before requested) →
  All (Batch.Supported (Review.experienceID requested) (Prepared.after receipt)) (Prepared.bindings receipt)
allBindingsReserved receipt = Batch.bindingsSupported (Prepared.reservations receipt)

candidateIsOwned : ∀ {occupied before requested} (receipt : Prepared occupied before requested) name identity →
  Resolution.Resolution (Review.candidates requested) (Prepared.bindings receipt) (candidate name) identity →
  Batch.Supported (Review.experienceID requested) (Prepared.after receipt) (name , identity)
candidateIsOwned receipt name identity (declared , found) = Batch.resolvedReservation (Prepared.reservations receipt) name
  identity found

everyCandidateReturned : ∀ {occupied before requested} (receipt : Prepared occupied before requested) →
  length (Prepared.bindings receipt) ≡ length (Review.candidates requested)
everyCandidateReturned receipt = Batch.countExact (Prepared.reservations receipt)

assessmentsPreserved : ∀ {occupied before requested} (receipt : Prepared occupied before requested) →
  length (Review.assessments (materialized receipt)) ≡ length (Review.assessments requested)
assessmentsPreserved {requested = requested} receipt = Resolution.Apply.assessmentCountPreserved
  (Review.candidates requested) (Prepared.bindings receipt) requested
  (Resolution.Apply.Prepared.resolution
   (Prepared.resolution receipt))

originalsPreserved : ∀ {occupied before requested} (receipt : Prepared occupied before requested) →
  Review.extracted (materialized receipt) ≡ Review.extracted requested ×
  Review.coverage (materialized receipt) ≡ Review.coverage requested
originalsPreserved {requested = requested} receipt = Resolution.Apply.originalsPreserved (Review.candidates requested)
  (Prepared.bindings receipt) requested
  (Resolution.Apply.Prepared.resolution
   (Prepared.resolution receipt))
