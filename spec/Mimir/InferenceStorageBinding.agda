{-# OPTIONS --safe #-}
-- Read effects observe their own statement snapshots; numerical persistence
-- acknowledges the exact posterior write set; sweep deletion runs the complete
-- deletion transaction. Clock, HashMap iteration and chrono are dependencies.
module Mimir.InferenceStorageBinding where

open import Data.List using (List)
open import Data.Float.Base using (Float)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ)
open import Data.Sum using (inj₁; inj₂)
import Mimir.ApplicationStore as Store
import Mimir.InferenceProtocol as I
import Mimir.StorageSemantics as S
import Mimir.StorageReadBinding as Read
import Mimir.DatabaseReadCommitted as Committed
import Mimir.DatabaseTransaction as DB

module Bound (database : ℕ) (sum : List Float → Float) (reads : Committed.Contract Store.World) where
  private
    module R = Read.Observed reads
    module B = S.Bound database

  data External : I.Effect → Set where
    clock : External I.clock
    chrono : ∀ hours → External (I.convertGraceHours hours)
    iteration : ∀ ids → External (I.hashIteration ids)

  data Receipt : (effect : I.Effect) → I.Reply effect → Set where
    selected : ∀ effect reply → R.SuccessfulInferenceReply sum effect reply → Receipt effect reply
    dependency : ∀ effect → External effect → (reply : I.Reply effect) → Receipt effect reply
    persisted : ∀ writes before receipt after → S.StatementPublication (S.posterior writes) before receipt after →
      Receipt (I.persistBeta writes) (inj₂ receipt)
    deleted : ∀ id value → B.Deleted id value → Receipt (I.deleteBelief id) (inj₂ value)
    beliefFailed : ∀ id error → Receipt (I.getBelief id) (inj₁ error)
    descendantsFailed : ∀ id causal error → Receipt (I.descendants id causal) (inj₁ error)
    reviewsFailed : ∀ error → Receipt I.activeReviews (inj₁ error)
    groundsFailed : ∀ error → Receipt I.groundingMasses (inj₁ error)
    incomingFailed : ∀ ids error → Receipt (I.incomingEdges ids) (inj₁ error)
    listFailed : ∀ scope error → Receipt (I.listBeliefs scope) (inj₁ error)
    contradictionsFailed : ∀ scope error → Receipt (I.contradictionPairs scope) (inj₁ error)
    defeatsFailed : ∀ scope error → Receipt (I.defeatTimes scope) (inj₁ error)
    persistenceFailed : ∀ writes error → Receipt (I.persistBeta writes) (inj₁ error)
    deletionFailed : ∀ id error → Receipt (I.deleteBelief id) (inj₁ error)
