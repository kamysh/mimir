{-# OPTIONS --safe #-}
-- Connect the lock/read/write protocol to the existing review classifier,
-- active-evidence publication and immutable journal. Materialization and the
-- native SQL write set remain explicit application obligations.
module Mimir.ReviewTransaction where

open import Data.List using (_∷_; [])
open import Data.Nat using (ℕ)
open import Mimir.UUIDGroups using (UUID)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)
import Mimir.ReviewJournal as Journal
import Mimir.LearningTransaction as Transaction
import Mimir.LearningTransactionReceipt as Receipt
import Mimir.DatabaseTransaction as Database

module Over (Payload Contribution Failure : Set) (equal : DecidableEquality Payload)
  (materialize : Payload → Contribution) (database key : ℕ) (rejection : Failure) where
  module J = Journal.Over Payload Contribution equal materialize
  module T = Transaction.Over J.World J.World Failure database key
  module Receipts = Receipt.Over J.World J.World Failure database key

  fromPlan : ∀ identity before payload {after} → J.P.Plan (J.current before identity) payload after → T.Decision
  fromPlan identity before payload J.P.refused = T.reject rejection
  fromPlan identity before payload J.P.replayed = T.replay before
  fromPlan identity before payload J.P.fresh = T.replace (J.fresh identity before payload) (J.fresh identity before payload)

  plan : UUID → J.C.Request → J.World → T.Decision
  plan identity submitted before = fromPlan identity before (J.C.Request.payload submitted) (J.classify identity before submitted)

  writeSet : J.World → T.Decision → J.World
  writeSet before (T.reject reason) = before
  writeSet before (T.replay value) = before
  writeSet before (T.replace proposed value) = proposed

  fromPlanWrites : ∀ identity before payload {after} (classification : J.P.Plan (J.current before identity) payload after) →
    writeSet before (fromPlan identity before payload classification) ≡ J.apply identity before payload classification
  fromPlanWrites identity before payload J.P.refused = refl
  fromPlanWrites identity before payload J.P.replayed = refl
  fromPlanWrites identity before payload J.P.fresh = refl

  plannedWrites : ∀ identity submitted before → writeSet before (plan identity submitted before) ≡ J.proposed identity before submitted
  plannedWrites identity submitted before = fromPlanWrites identity before (J.C.Request.payload submitted) (J.classify identity before submitted)

  planPreserves : ∀ identity submitted before → J.Consistent before → J.Consistent (writeSet before (plan identity submitted before))
  planPreserves identity submitted before consistent = subst J.Consistent (sym (plannedWrites identity submitted before))
    (J.applyConsistent identity before (J.C.Request.payload submitted)
     (J.classify identity before submitted) consistent)

  classifiedReplay : ∀ identity before payload {after} (classification : J.P.Plan (J.current before identity) payload after) →
    J.P.IsReplay classification → fromPlan identity before payload classification ≡ T.replay before
  classifiedReplay identity before payload J.P.replayed J.P.isReplay = refl

  retryPlan : ∀ identity before original payload valid →
    J.current before identity ≡ J.R.commit original payload →
    plan identity (J.C.originalRequest original payload valid) before ≡ T.replay before
  retryPlan identity before original payload valid committed = classifiedReplay identity before payload
    (J.classify identity before
     (J.C.originalRequest original payload valid))
    (J.P.unchangedMeansReplay (J.current before identity) payload
     (J.classify identity before
      (J.C.originalRequest original payload valid))
     (J.L.exactRetryPlan identity (J.World.active before) original
      payload valid committed))

  retryOnlyRollback : ∀ identity before original payload valid tx events result →
    J.current before identity ≡ J.R.commit original payload →
    T.E.Runs (T.decide tx (plan identity (J.C.originalRequest original payload valid) before)) events result →
    Σ T.Cleanup (λ cleanup → events ≡ ((T.rollback tx , cleanup) ∷ []) × result ≡ T.replayed before cleanup)
  retryOnlyRollback identity before original payload valid tx events result committed execution = T.exactReplayOnlyRollback tx before events result
    (subst (λ decision → T.E.Runs (T.decide tx decision) events result)
     (retryPlan identity before original payload valid committed)
     execution)

  publicationPreserves : ∀ identity submitted before reply published →
    Database.Atomic before (writeSet before (plan identity submitted before)) reply published →
    J.Consistent before → J.Consistent published
  publicationPreserves identity submitted before reply published atomic consistent = Database.invariantPreserved J.Consistent atomic consistent
    (planPreserves identity submitted before consistent)

  module Request (identity : UUID) (submitted : J.C.Request) where
    module Program = T.Plan (plan identity submitted)
    module Scope = T.Laws (plan identity submitted)
    module Confirmation = Receipts.WithPlan (plan identity submitted)

    scoped : ∀ events result → T.E.Runs Program.start events result → T.Trace T.outside events T.finished
    scoped = Scope.completedScope

    acknowledged : ∀ events result → T.E.Runs Program.start events (T.applied result) → Receipts.Receipt events
    acknowledged = Confirmation.successRequiresCommit
