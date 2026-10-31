{-# OPTIONS --safe #-}
-- Concrete semantic payload keys instantiate the formerly abstract comparison
-- used for retries. Projects remain literal text; there is no interning axiom.
module Mimir.LearningRevision where

open import Data.Bool using (Bool)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.SemanticKey using (Key; equal)
open import Mimir.ReviewSchema using (Review)
open import Mimir.LearningKeys using (review)
import Mimir.LearningContracts as Contracts
import Mimir.CommitProtocol as Commit
import Mimir.RevisionBounds as Limits

module Revisions = Contracts.Revision Key equal
module Publication = Commit.ReviewCommit Key equal
module Bounded = Limits.Limited Key equal Limits.i64Maximum

sameTypedReviewDoesNotReapply : ∀ state (request : Review) valid →
  Revisions.submit (Revisions.commit state (review request))
    (Revisions.Cell.project state) (Revisions.Cell.current state)
    (Revisions.Cell.review state) (review request) valid ≡
    just (Revisions.commit state (review request))
sameTypedReviewDoesNotReapply state request valid =
  Revisions.exact-retry-no-new-commit state (review request) valid

equivalentTypedReviewDoesNotReapply : ∀ state first second valid → review first ≡ review second →
  Revisions.submit (Revisions.commit state (review first))
    (Revisions.Cell.project state) (Revisions.Cell.current state)
    (Revisions.Cell.review state) (review second) valid ≡
    just (Revisions.commit state (review first))
equivalentTypedReviewDoesNotReapply state first second valid same rewrite same =
  Revisions.exact-retry-no-new-commit state (review second) valid
