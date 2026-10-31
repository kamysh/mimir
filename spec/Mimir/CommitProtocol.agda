{-# OPTIONS --safe #-}
-- Database publication versus what the caller can observe. A lost receipt is
-- explicitly ambiguous; it is never reported as a rejection that changed
-- nothing. This connects retry behavior to the existing revision contract.
module Mimir.CommitProtocol where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Mimir.LearningContracts
open import Mimir.Text using (Text)

module ReviewCommit (Payload : Set) (same : DecidableEquality Payload) where
  module R = Revision Payload same
  open R using (Cell; cell)

  record Request : Set where
    constructor request
    field owner : Text; source expected : ℕ; payload : Payload; validTargets : Bool
  open Request

  data Delivery : Set where
    abortBeforeCommit commitLoseReceipt commitDeliverReceipt : Delivery

  data Observation : Set where
    refused : Observation
    uncertain : Observation
    acknowledged : Cell → Observation

  record Outcome : Set where
    constructor outcome
    field durable : Cell; observation : Observation
  open Outcome

  planned : Cell → Request → Maybe Cell
  planned before r = R.submit before (owner r) (source r) (expected r) (payload r) (validTargets r)

  publish : Cell → Maybe Cell → Delivery → Outcome
  publish before nothing delivery = outcome before refused
  publish before (just after) abortBeforeCommit = outcome before uncertain
  publish before (just after) commitLoseReceipt = outcome after uncertain
  publish before (just after) commitDeliverReceipt = outcome after (acknowledged after)

  attempt : Cell → Request → Delivery → Outcome
  attempt before r delivery = publish before (planned before r) delivery

  -- A definite refusal proves the durable cell is unchanged. No such claim
  -- follows from uncertainty, where both pre- and post-commit worlds are valid.
  refusedPreserves : ∀ before proposal delivery →
    observation (publish before proposal delivery) ≡ refused →
    durable (publish before proposal delivery) ≡ before
  refusedPreserves before nothing delivery proof = refl
  refusedPreserves before (just after) abortBeforeCommit ()
  refusedPreserves before (just after) commitLoseReceipt ()
  refusedPreserves before (just after) commitDeliverReceipt ()

  receiptIsDurable : ∀ before proposal delivery receipt →
    observation (publish before proposal delivery) ≡ acknowledged receipt →
    durable (publish before proposal delivery) ≡ receipt
  receiptIsDurable before nothing delivery receipt ()
  receiptIsDurable before (just after) abortBeforeCommit receipt ()
  receiptIsDurable before (just after) commitLoseReceipt receipt ()
  receiptIsDurable before (just after) commitDeliverReceipt .after refl = refl

  lostReceiptAmbiguous : ∀ before after →
    observation (publish before (just after) abortBeforeCommit) ≡
    observation (publish before (just after) commitLoseReceipt)
  lostReceiptAmbiguous before after = refl

  -- A retry after an unobserved commit carries the same source revision,
  -- expected review revision, and payload. It cannot apply evidence twice.
  originalRequest : Cell → Payload → Bool → Request
  originalRequest before p valid = request (R.Cell.project before)
    (R.Cell.current before) (R.Cell.review before) p valid

  exactRetryPlan : ∀ before p valid →
    planned (R.commit before p) (originalRequest before p valid) ≡ just (R.commit before p)
  exactRetryPlan before p valid = R.exact-retry-no-new-commit before p valid

  exactRetryDurable : ∀ before p valid delivery →
    durable (attempt (R.commit before p) (originalRequest before p valid) delivery) ≡
    R.commit before p
  exactRetryDurable before p valid delivery rewrite exactRetryPlan before p valid
    with delivery
  ... | abortBeforeCommit = refl
  ... | commitLoseReceipt = refl
  ... | commitDeliverReceipt = refl

  exactRetryReceipt : ∀ before p valid →
    observation (attempt (R.commit before p) (originalRequest before p valid) commitDeliverReceipt) ≡
    acknowledged (R.commit before p)
  exactRetryReceipt before p valid rewrite exactRetryPlan before p valid = refl

  changedSourceRefused : ∀ before r delivery → source r ≢ R.Cell.current before →
    attempt before r delivery ≡ outcome before refused
  changedSourceRefused before r delivery changed
    rewrite R.stale-source-refused before (owner r) (source r) (expected r)
      (payload r) (validTargets r) changed = refl
