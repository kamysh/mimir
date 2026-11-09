{-# OPTIONS --safe #-}
-- Embedded migration manifest and transaction publication. This
-- specifies Mimir's effects, not an axiom that PostgreSQL executed a request.
-- SQL row/graph semantics and legacy sqlx receipt validation are separate.
module Mimir.Migrations where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Migration : Set where
  initial searchPath beliefEmbeddings evidenceEdges betaBeliefs learningLedger
    reviewCandidates assessments itemOwners postgresItemAllocation reviewQueueNotifications operationReservations operationBindings operationStepReplies operationPlans operationRequestKeys candidateKeyContent embeddingOwners operationCancellations decayAccounting firstDefeatClock backfillChangeEvents : Migration
