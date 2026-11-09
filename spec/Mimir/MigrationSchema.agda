{-# OPTIONS --safe #-}
-- The embedded application migrations. This is the concrete DDL/data
-- contract supplied to MigrationDriver.executeOriginalSQL; PostgreSQL executes
-- these operations inside the driver's transaction, before both ledger writes.
-- SQL expression arithmetic, collation and NULL semantics are database
-- dependency contracts, not an invented SQL interpreter.
module Mimir.MigrationSchema where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.String using (String; toList)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.ItemOwnerBackfill as Historical
import Mimir.ItemOwners as Owners
import Mimir.LearningStore as Learning
import Mimir.DatabaseTransaction as Database
open import Mimir.Migrations public
  using (Migration; initial; searchPath; evidenceEdges; betaBeliefs; reviewQueueNotifications; operationReservations; operationBindings; operationStepReplies; operationPlans; operationRequestKeys; candidateKeyContent; embeddingOwners; operationCancellations; decayAccounting; firstDefeatClock; backfillChangeEvents)
