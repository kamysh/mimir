{-# OPTIONS --safe #-}
module Mimir.JudgeAcknowledgement where

open import Data.Integer using (_<_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Mimir.ReviewObservation as Observation

record Evidence (p : Observation.Pin) : Set where
  constructor evidence
  field
    snapshot : Observation.Snapshot
    valid : Observation.SnapshotValid snapshot
    acknowledgement : Observation.Ack p snapshot

sameExperience : ∀ p (e : Evidence p) → Observation.IdentityMatches p (Evidence.snapshot e)
sameExperience p e = Observation.confirmationPinsIdentity p (Evidence.snapshot e) (Evidence.acknowledgement e)

sameSourceRevision : ∀ p (e : Evidence p) →
  Observation.Snapshot.revision (Evidence.snapshot e) ≡ Observation.Pin.sourceRevision p
sameSourceRevision p e = Observation.confirmationPinsSource p (Evidence.snapshot e) (Evidence.acknowledgement e)

newReviewRevision : ∀ p (e : Evidence p) →
  Observation.Pin.reviewRevision p < Observation.Snapshot.reviewRevision (Evidence.snapshot e)
newReviewRevision p e = Observation.confirmationRequiresNewReview p (Evidence.snapshot e) (Evidence.acknowledgement e)
