-- USER-APPROVED ASSUMPTION: postgres_transaction_atomicity.
-- Approval: the user selected Approve for the individually presented
-- PostgreSQL transaction-atomicity postulate on 2026-10-30.
--
-- This module intentionally does not use --safe. It is outside the safe
-- specification root, which must never import it. Each postulate below has
-- its own recorded user approval. Atomic publication includes ambiguous
-- acknowledgement loss; advisory-lock ownership is a separate contract.
--
-- No assumption about Mimir's SQL, transaction contents, locking, retries,
-- model behavior, or adapter correspondence is included. The concrete Rust
-- adapter still must map native completed calls into this interface.
module Mimir.Assumptions.PostgreSQL where

import Mimir.DatabaseTransaction as Transaction
import Mimir.DatabaseAdvisoryLock as AdvisoryLock
import Mimir.DatabaseReadCommitted as ReadCommitted

postulate
  atomicTransactions : (State : Set) → Transaction.Contract State

-- Individually approved by the user on 2026-10-30 through the native selector:
-- distinct transactions cannot simultaneously own the same database/key
-- transaction-level exclusive advisory lock; transaction end releases these
-- holdings. This does not assume correct Mimir participation, SQL or progress.
postulate
  transactionAdvisoryLocks : AdvisoryLock.Contract

-- Individually approved by the user on 2026-10-30 through the native selector:
-- each successful ordinary read-only SELECT in READ COMMITTED sees committed
-- row state at statement start plus prior writes in its own transaction.
-- Excludes FOR UPDATE/SHARE, DML, sequences and functions performing writes.
-- SQL correctness, isolation selection, transaction identity, lock coverage
-- and progress remain application proof obligations.
postulate
  readCommittedSnapshots : (State : Set) → ReadCommitted.Contract State
