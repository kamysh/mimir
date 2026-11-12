{-# OPTIONS --safe #-}
-- Atomic publication of existing experience revisions and their active
-- contributions. The SQL adapter must implement this transition; transaction
-- atomicity alone does not prove that it writes the correct cells/effects.
module Mimir.LearningPublication where

open import Data.Bool using (Bool)
open import Data.Nat using (ℕ; _≟_)
open import Mimir.UUIDGroups using (UUID; _≟UUID_)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapMaybe)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans; subst)
import Mimir.LearningContracts as Contracts
import Mimir.CommitProtocol as Commit
import Mimir.DatabaseTransaction as Database

module Over (Payload Contribution : Set) (equal : DecidableEquality Payload)
  (materialize : Payload → Contribution) where
  module R = Contracts.Revision Payload equal
  module C = Commit.ReviewCommit Payload equal
  module Cells = Contracts.OwnershipWith UUID R.Cell _≟UUID_
  module Contributions = Contracts.OwnershipWith UUID (Maybe Contribution) _≟UUID_

  -- Retry equality belongs to the submitted payload. The application must
  -- separately supply and justify its contribution materialization, including
  -- stable candidate resolution; the two representations need not be equal.
  activeContribution : R.Cell → Maybe Contribution
  activeContribution state = mapMaybe materialize (R.active state)

  record World : Set where
    constructor world
    field
      cells : UUID → R.Cell
      contributions : UUID → Maybe Contribution
  open World

  Consistent : World → Set
  Consistent before = ∀ identity → contributions before identity ≡ activeContribution (cells before identity)

  SameAt : World → World → UUID → Set
  SameAt first second identity = cells first identity ≡ cells second identity ×
    contributions first identity ≡ contributions second identity

  install : UUID → R.Cell → World → World
  install identity after before = world
    (Cells.write identity after (cells before))
    (Contributions.write identity (activeContribution after) (contributions before))

  installedCell : ∀ identity after before → cells (install identity after before) identity ≡ after
  installedCell identity after before = Cells.write-own identity after (cells before)

  installedContribution : ∀ identity after before →
    contributions (install identity after before) identity ≡ activeContribution after
  installedContribution identity after before = Contributions.write-own identity (activeContribution after)
    (contributions before)

  unrelatedPreserved : ∀ identity after before other → other ≢ identity →
    SameAt (install identity after before) before other
  unrelatedPreserved identity after before other distinct = Cells.write-other identity other after (cells before) distinct ,
    Contributions.write-other identity other (activeContribution after)
    (contributions before) distinct

  installConsistent : ∀ identity after before → Consistent before → Consistent (install identity after before)
  installConsistent identity after before consistent queried with queried ≟UUID identity
  ... | yes refl = refl
  ... | no different = consistent queried

  reinstallUnchanged : ∀ identity before → Consistent before →
    ∀ queried → SameAt (install identity (cells before identity) before) before queried
  reinstallUnchanged identity before consistent queried with queried ≟UUID identity
  ... | yes refl = refl , sym (consistent identity)
  ... | no different = refl , refl

  record Outcome : Set where
    constructor outcome
    field durable : World; observation : C.Observation

  publish : UUID → World → Maybe R.Cell → C.Delivery → Outcome
  publish identity before nothing delivery = outcome before C.refused
  publish identity before (just after) C.abortBeforeCommit = outcome before C.notCommitted
  publish identity before (just after) C.commitDeliverReceipt = outcome (install identity after before) (C.acknowledged after)

  attempt : UUID → World → C.Request → C.Delivery → Outcome
  attempt identity before submitted delivery = publish identity before (C.planned (cells before identity) submitted) delivery

  publicationConsistent : ∀ identity before proposal delivery → Consistent before →
    Consistent (Outcome.durable (publish identity before proposal delivery))
  publicationConsistent identity before nothing delivery consistent = consistent
  publicationConsistent identity before (just after) C.abortBeforeCommit consistent = consistent
  publicationConsistent identity before (just after) C.commitDeliverReceipt consistent = installConsistent identity after before consistent

  correction : UUID → World → World
  correction identity before = install identity (R.correct (cells before identity)) before

  correctionRetracts : ∀ identity before → contributions (correction identity before) identity ≡ nothing
  correctionRetracts identity before = trans
    (installedContribution identity (R.correct (cells before identity))
     before)
    (cong (mapMaybe materialize)
       (R.stale-contribution-inactive (R.correct (cells before identity))
        (R.correction-is-pending (cells before identity))))

  staleSourcePreserves : ∀ identity before submitted delivery →
    C.Request.source submitted ≢ R.Cell.current (cells before identity) →
    attempt identity before submitted delivery ≡ outcome before C.refused
  staleSourcePreserves identity before submitted delivery stale = cong (λ proposal → publish identity before proposal delivery)
    (R.stale-source-refused (cells before identity)
     (C.Request.owner submitted) (C.Request.source submitted)
     (C.Request.expected submitted) (C.Request.payload submitted)
     (C.Request.validTargets submitted) stale)

  -- This holds for any existing consistent world whose selected cell is the
  -- committed result of the original request.
  exactRetryPlan : ∀ identity before original payload valid →
    cells before identity ≡ R.commit original payload →
    C.planned (cells before identity) (C.originalRequest original payload valid) ≡ just (cells before identity)
  exactRetryPlan identity before original payload valid committed = trans
    (cong
     (λ state →
        C.planned state (C.originalRequest original payload valid))
     committed)
    (trans (C.exactRetryPlan original payload valid)
     (cong just (sym committed)))

  exactRetryPreserves : ∀ identity before original payload valid delivery →
    Consistent before → cells before identity ≡ R.commit original payload →
    ∀ queried → SameAt
      (Outcome.durable (attempt identity before (C.originalRequest original payload valid) delivery))
      before queried
  exactRetryPreserves identity before original payload valid C.abortBeforeCommit consistent committed queried
    rewrite exactRetryPlan identity before original payload valid committed = refl , refl
  exactRetryPreserves identity before original payload valid C.commitDeliverReceipt consistent committed queried
    rewrite exactRetryPlan identity before original payload valid committed = reinstallUnchanged identity before consistent queried

  -- The application supplies the complete proposed-write equality. The
  -- dependency contract supplies atomic publication only. This separation
  -- prevents assuming that the SQL adapter already writes the right data.
  module Native (database : Database.Contract World) where
    module D = Database.Contract database

    publicationPreservesConsistency : ∀ (event : D.Completion) identity after →
      Consistent (D.before event) →
      D.proposed event ≡ install identity after (D.before event) →
      Consistent (D.published event)
    publicationPreservesConsistency event identity after consistent proposedWrites = Database.invariantPreserved Consistent (D.atomicity event)
      consistent
      (subst Consistent (sym proposedWrites)
       (installConsistent identity after (D.before event) consistent))
