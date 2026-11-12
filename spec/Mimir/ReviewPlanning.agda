{-# OPTIONS --safe #-}
-- Decide refusal, exact replay or fresh state-dependent preparation before
-- choosing any publication. Replay reconstructs live reserved IDs; it cannot
-- fall through to ownership, candidate creation or append-history effects.
module Mimir.ReviewPlanning where

open import Data.Bool using (true; false)
open import Data.List using ([]; map)
open import Data.List.Relation.Unary.All using (All)
open import Data.Integer using (ℤ; +_)
open import Data.Nat using (ℕ; _<?_; _≟_)
open import Mimir.UUIDGroups using (UUID)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; cong)
open import Mimir.ExperienceSchema using (Experience)
open import Mimir.ReviewSchema using (Review; validateReview)
open import Mimir.LearningCandidates using (Candidate)
open import Mimir.SourceReview using (_≟Text_)
open import Mimir.Validation using (Fault; fault; staleRevision; wrongIdentity; accepted; rejected)
open import Mimir.RevisionBounds using (i64Maximum)
import Mimir.LearningKeys as Keys
import Mimir.CandidateRegistry as Registry
import Mimir.CandidateGraph as Graph
import Mimir.CandidateBatch as Batch
import Mimir.CandidateReplay as Replay
import Mimir.ReviewResolution as Resolution
import Mimir.ReviewAdmission as Admission
import Mimir.ReviewLedger as Ledger
import Mimir.ReviewPreparationPublication as Publication
import Mimir.LearningContracts as Contracts
open import Data.Empty using (⊥-elim)

module For (before : Publication.World) (current : Experience) (requested : Review)
  (clock : Candidate → ℤ)
  (unique : Registry.IDs.Unique (map Graph.nodeID (Publication.World.nodes before)))
  (expected : ℕ) where

  module F = Publication.For before current requested clock unique
  module Read = Replay.Read (Review.experienceID requested) (Publication.World.registry before)

  record Replayed : Set where
    constructor replayed
    field
      same : Ledger.R.replay F.state expected (Keys.review requested) ≡ true
      pinned : Admission.Pinned F.P.originalEnvironment requested
      declarations : All (Batch.Declared (Review.experienceID requested) (Publication.World.registry before))
        (Review.candidates requested)

  data Decision : Set where
    refused : Fault → Decision
    replay : Replayed → Decision
    fresh : F.Fresh expected → Decision

  plan : (Candidate → UUID) → Decision
  plan identities with validateReview requested
  ... | rejected failure invalid = refused failure
  ... | accepted structure with expected <? i64Maximum
  ...   | no invalid = refused (fault [] staleRevision "expected review revision exceeds storage range")
  ...   | yes room with Admission.checkPin F.P.originalEnvironment requested
  ...     | rejected failure invalid = refused failure
  ...     | accepted pinned with Experience.project current ≟Text Ledger.R.Cell.project F.state
  ...       | no different = refused (fault [] wrongIdentity "experience project does not match its revision cell")
  ...       | yes project with Ledger.R.replay F.state expected (Keys.review requested) in retry
  ...         | true with Replay.check (Review.experienceID requested) (Publication.World.registry before) (Review.candidates requested)
  ...           | rejected failure invalid = refused failure
  ...           | accepted declarations = replay (replayed retry pinned declarations)
  plan identities | accepted structure | yes room | accepted pinned | yes project | false
    with expected ≟ Ledger.R.Cell.review F.state
  ... | no different = refused (fault [] staleRevision "stale review revision")
  ... | yes same with F.P.prepare identities
  ...   | inj₁ failure = refused failure
  ...   | inj₂ preparation = fresh (F.fresh project same retry room preparation)

  proposed : Decision → Publication.World
  proposed (refused failure) = before
  proposed (replay receipt) = before
  proposed (fresh selected) = F.publish selected

  replayBindings : Replayed → Resolution.Registry
  replayBindings receipt = Read.bindings (Review.candidates requested) (Replayed.declarations receipt)

  replayBindingsSupported : ∀ receipt →
    All (Batch.Supported (Review.experienceID requested) (Publication.World.registry before)) (replayBindings receipt)
  replayBindingsSupported receipt = Read.allSupported (Review.candidates requested)
    (Replayed.declarations receipt)

  replayHasNoWrites : ∀ receipt → proposed (replay receipt) ≡ before
  replayHasNoWrites receipt = refl

  refusalHasNoWrites : ∀ failure → proposed (refused failure) ≡ before
  refusalHasNoWrites failure = refl

  decisionValid : ∀ selected → Publication.LedgerAndIdentityValid before →
    Publication.LedgerAndIdentityValid (proposed selected)
  decisionValid (refused failure) valid = valid
  decisionValid (replay receipt) valid = valid
  decisionValid (fresh selected) valid = F.publicationValid selected (proj₁ valid)

  replayCannotAppend : Ledger.R.replay F.state expected (Keys.review requested) ≡ true →
    ∀ selected → proposed selected ≡ before
  replayCannotAppend same (refused failure) = refl
  replayCannotAppend same (replay receipt) = refl
  replayCannotAppend same (fresh selected) with trans (sym (F.Fresh.notReplay selected)) same
  ... | ()

  staleReviewCannotAppend : expected ≢ Ledger.R.Cell.review F.state → ∀ selected → proposed selected ≡ before
  staleReviewCannotAppend stale (refused failure) = refl
  staleReviewCannotAppend stale (replay receipt) = refl
  staleReviewCannotAppend stale (fresh selected) = ⊥-elim (stale (F.Fresh.expectedMatches selected))

  staleSourceCannotAppend : Review.experienceRevision requested ≢ (+ Ledger.R.Cell.current F.state) →
    ∀ selected → proposed selected ≡ before
  staleSourceCannotAppend stale (refused failure) = refl
  staleSourceCannotAppend stale (replay receipt) = refl
  staleSourceCannotAppend stale (fresh selected) = ⊥-elim
    (stale
     (proj₂
      (Admission.For.Admitted.pinned
       (F.P.Prepared.admitted (F.Fresh.preparation selected)))))

-- The second plan is built from the actual first publication, including its
-- prepared nodes, ownership, assessment rows and edges. Native locking and
-- fresh-read correspondence must supply this state; they are not assumed here.
module Following (before : Publication.World) (current : Experience)
  (first second : Review) (firstClock secondClock : Candidate → ℤ)
  (unique : Registry.IDs.Unique (map Graph.nodeID (Publication.World.nodes before)))
  (expected : ℕ)
  (selected : Publication.For.Fresh before current first firstClock unique expected) where

  module First = Publication.For before current first firstClock unique
  after = First.publish selected
  afterUnique = First.P.proposedUnique
    (First.P.Prepared.reservation (First.Fresh.preparation selected))
  module Next = For after current second secondClock afterUnique expected

  publishedCell : Next.F.state ≡ Ledger.R.commit First.state (Keys.review first)
  publishedCell = Ledger.Cells.write-own First.identity
    (Ledger.R.commit First.state (Keys.review first))
    (Ledger.World.cells (Publication.World.ledger before))

  expectedNowStale : expected ≢ Ledger.R.Cell.review Next.F.state
  expectedNowStale same = Contracts.not-successor (Ledger.R.Cell.review First.state)
    (trans (sym (First.Fresh.expectedMatches selected))
     (trans same (cong Ledger.R.Cell.review publishedCell)))

  secondCannotPublish : ∀ decision → Next.proposed decision ≡ after
  secondCannotPublish decision = Next.staleReviewCannotAppend expectedNowStale decision

  secondPlanInert : ∀ identities → Next.proposed (Next.plan identities) ≡ after
  secondPlanInert identities = secondCannotPublish (Next.plan identities)
