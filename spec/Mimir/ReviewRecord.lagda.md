# Correcting a review

A review interprets one saved revision of an experience. The request names
that source revision and supplies the last review revision the caller has
seen. The first review uses expected review revision zero. These are
different numbers. A new observation requires the judge to reassess the
source, while a competing review requires the caller to reconcile its changes
with the current judgment.

For example, if a second reviewer has already replaced review 1 with
review 2, a different submission based on review 1 is refused. Read
`get_learning_review`, reconcile the changes, and submit against revision 2.
If the experience itself has changed, use `get_experience` and re-evaluate
the evidence before submitting. Both refusals name the stale field.

An identical request for the current source, with the current review
revision or its immediate predecessor, returns the saved result. It adds
no contributions and keeps the candidate bindings. Changing a review
keeps the prior version in history and replaces its active contributions
and links. Extracted identities and quotations remain tied to the original
observations. The corrected review, updated assessments, and affected
belief values become visible together on commit.

[ReviewPlanning](ReviewPlanning.agda) checks the source, freshness, and
replay conditions. [ReviewPreparationPublication](ReviewPreparationPublication.agda)
connects the new review to the approved contributions and links.
[LearningOperations](LearningOperations.agda) supplies the transaction and
requires a commit for a fresh result. New beliefs also require
[prepared grounding and embedding](ReviewBeliefPreparation.lagda.md).
[The Rust store](../../crates/core/src/store/learning.rs) rechecks both
revisions inside the locked transaction before accepting a changed review.

```agda
{-# OPTIONS --safe #-}
module Mimir.ReviewRecord where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; suc)
open import Mimir.UUIDGroups using (UUID)
open import Data.Integer using (ℤ; +_; ∣_∣)
import Data.Integer.Properties as Integer
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.ReviewSchema using (Review)
open import Mimir.LearningCandidates using (Candidate)
import Mimir.Validation as Validation
import Mimir.LearningStore as Store
import Mimir.ExperienceRead as Read
import Mimir.ExperienceRecord as Record
import Mimir.ReviewObservation as Observation
import Mimir.ReviewPreparationPublication as Publication
import Mimir.ReviewNumericalPublication as Numerical
import Mimir.PosteriorComputation as Posterior
import Mimir.CandidateGraph as Graph
import Mimir.CandidateRegistry as Registry
import Mimir.CandidateReview as Candidates
import Mimir.RevisionBounds as Bounds

data Failure : Set where
  invalid : Validation.Fault → Failure
  invalidExpected missingExperience incoherentSnapshot : Failure
  numeric : Numerical.NumericFailure → Failure

data Decision : Set where
  rejected : Failure → Decision
  replay : Observation.Snapshot → Decision
  fresh : Store.World → Observation.Snapshot → Bool → Decision

module For (calculation : Posterior.Calculation)
  (before : Store.World) (old : Observation.Snapshot) (requested : Review)
  (expected : ℕ) (clock : Candidate → ℤ) (now : ℤ)
  (unique : Registry.IDs.Unique (map Graph.nodeID (Publication.World.nodes (Store.World.publication before)))) where

  module N = Numerical.For calculation (Store.World.publication before) (Observation.Snapshot.experience old)
    requested clock unique expected (Store.identities before) (Store.World.grounding before)

  convert : N.Decision → Decision
  convert (N.refused failure) = rejected (invalid failure)
  convert (N.numericFailure failure) = rejected (numeric failure)
  convert (N.replay receipt) = replay (record old { candidateIDs = N.P.replayBindings receipt })
  convert d@(N.fresh selected nodes same limit) = fresh
    (record before
      { publication = N.proposed d
      ; current = Store.reviewed (record result { candidateIDs = [] }) (Store.World.current before)
      ; reviewTimes = Store.reviewTime (Review.experienceID requested) (suc expected) now ∷ Store.World.reviewTimes before }) result limit
    where
    result = record old
      { reviewRevision = + suc expected
      ; reviewedRevision = Observation.Snapshot.revision old
      ; candidateIDs = Candidates.Prepared.bindings
          (N.F.P.Prepared.reservation (N.F.Fresh.preparation selected)) }

  plan : (Candidate → UUID) → Decision
  plan identities = convert (N.plan identities)

checkState : (calculation : Posterior.Calculation) → Store.World → Observation.Snapshot → Review → ℕ → (Candidate → ℤ) → ℤ → (Candidate → UUID) → Decision
checkState calculation before old requested expected clock now identities with Observation.checkSnapshot old
... | Validation.rejected failure refutation = rejected (invalid failure)
... | Validation.accepted valid with Record.coherent before old
...   | false = rejected incoherentSnapshot
...   | true with Registry.IDs.checkUnique (map Graph.nodeID (Publication.World.nodes (Store.World.publication before)))
...     | Validation.rejected failure refutation = rejected (invalid failure)
...     | Validation.accepted unique = For.plan calculation before old requested expected clock now unique identities

plan : (calculation : Posterior.Calculation) → Store.World → Review → ℤ → (Candidate → ℤ) → ℤ → (Candidate → UUID) → Decision
plan calculation before requested expected clock now identities with does ((+ 0) Integer.≤? expected) ∧ does (expected Integer.<? (+ Bounds.i64Maximum))
... | false = rejected invalidExpected
... | true with Read.get (Review.experienceID requested) (Store.World.current before)
...   | nothing = rejected missingExperience
...   | just old = checkState calculation before old requested ∣ expected ∣ clock now identities

proposed : Store.World → Decision → Store.World
proposed before (rejected failure) = before
proposed before (replay receipt) = before
proposed before (fresh after receipt limit) = after

replayPreservesStore : ∀ before receipt → proposed before (replay receipt) ≡ before
replayPreservesStore before receipt = refl

rejectionPreservesStore : ∀ before failure → proposed before (rejected failure) ≡ before
rejectionPreservesStore before failure = refl
```
