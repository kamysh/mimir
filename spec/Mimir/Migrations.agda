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
    reviewCandidates assessments itemOwners postgresItemAllocation reviewQueueNotifications operationReservations operationBindings operationStepReplies operationPlans operationRequestKeys candidateKeyContent embeddingOwners operationCancellations decayAccounting : Migration

name : Migration → String
name initial = "initial"
name searchPath = "database-search-path"
name beliefEmbeddings = "belief-embeddings"
name evidenceEdges = "evidence-edges"
name betaBeliefs = "beta-beliefs"
name learningLedger = "learning-ledger"
name reviewCandidates = "review-candidates"
name assessments = "learning-assessments"
name itemOwners = "learning-item-owners"
name postgresItemAllocation = "postgres-item-allocation"
name reviewQueueNotifications = "review-queue-notifications"
name operationReservations = "operation-reservations"
name operationBindings = "operation-bindings"
name operationStepReplies = "operation-step-replies"
name operationPlans = "operation-plans"
name operationRequestKeys = "operation-request-keys"
name candidateKeyContent = "candidate-key-content"
name embeddingOwners = "embedding-publication-owners"
name operationCancellations = "operation-cancellations"
name decayAccounting = "decay-accounting"

predecessor : Migration → Maybe Migration
predecessor initial = nothing
predecessor searchPath = just initial
predecessor beliefEmbeddings = just searchPath
predecessor evidenceEdges = just beliefEmbeddings
predecessor betaBeliefs = just evidenceEdges
predecessor learningLedger = just betaBeliefs
predecessor reviewCandidates = just learningLedger
predecessor assessments = just reviewCandidates
predecessor itemOwners = just assessments
predecessor postgresItemAllocation = just itemOwners
predecessor reviewQueueNotifications = just postgresItemAllocation
predecessor operationReservations = just reviewQueueNotifications
predecessor operationBindings = just operationReservations
predecessor operationStepReplies = just operationBindings
predecessor operationPlans = just operationStepReplies
predecessor operationRequestKeys = just operationPlans
predecessor candidateKeyContent = just operationRequestKeys
predecessor embeddingOwners = just candidateKeyContent
predecessor operationCancellations = just embeddingOwners
predecessor decayAccounting = just operationCancellations

manifest : List Migration
manifest = initial ∷ searchPath ∷ beliefEmbeddings ∷ evidenceEdges ∷
  betaBeliefs ∷ learningLedger ∷ reviewCandidates ∷ assessments ∷ itemOwners ∷ postgresItemAllocation ∷
  reviewQueueNotifications ∷ operationReservations ∷ operationBindings ∷ operationStepReplies ∷ operationPlans ∷ operationRequestKeys ∷ candidateKeyContent ∷ embeddingOwners ∷ operationCancellations ∷ decayAccounting ∷ []

-- The executable lifecycle is MigrationDriver. The former untyped state
-- table was removed because it conflated queued rollback with acknowledgement
-- and reloaded the applied snapshot for each migration.

-- Per-migration SQL and both receipts belong to one pending transaction.
-- Publishing them is one state change; no intermediate state exposes only a
-- receipt or only the schema. The concrete SQL interpreter supplies Schema.
module AtomicPublication (Schema Receipt : Set) where
  record Database : Set where
    constructor database
    field schema : Schema; receipts : List Receipt
  open Database

  record Pending : Set where
    constructor transaction
    field before : Database; staged : Schema; receipt : Receipt
  open Pending

  commit : Pending → Database
  commit tx = database (staged tx) (receipt tx ∷ receipts (before tx))

  rollback : Pending → Database
  rollback tx = before tx

  atomicReceipt : ∀ tx →
    schema (commit tx) ≡ staged tx × receipts (commit tx) ≡ receipt tx ∷ receipts (before tx)
  atomicReceipt tx = refl , refl

  rollbackPreserves : ∀ tx → rollback tx ≡ before tx
  rollbackPreserves tx = refl
