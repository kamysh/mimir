# What happens to a failed review

A queue entry identifies an experience and its source revision. Starting a
turn means reading that revision again and preparing a new review. A failed
attempt contributes its observed cause. Its draft, subprocess and conversation
are never required to start the next turn.

The database decides whether there is anything left to repair. A saved review
ends the turn. A changed source is eligible as a new revision. When Mimir
cannot read the result, it must restore the read before submitting another
write or telling someone that the review failed.

An unexplained exit gets a fresh turn behind the work already ready. If the
fresh attempt also fails, a provider recovery signal takes precedence. In its
absence the operator gets an immediate email with the cause and a choice
they can act on. A request for an actual human decision goes directly to
the operator. A hold belongs to its exact source revision.

```agda
{-# OPTIONS --safe #-}
module Mimir.JudgeRevisionPolicy where

open import Data.String using (toList)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Bool.ListAction using (any)
import Data.Integer.Properties as Integer
open import Relation.Nullary using (does)
open import Mimir.UUIDGroups using (_≟UUID_)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.ReviewObservation as O
open import Mimir.Validation using (Fault)

data Turn : Set where first fresh : Turn

data Signal : Set where
  providerAvailable : Signal
  resetAt : ℕ → Signal

-- Choices refer to the selected review, or to the service that failed.
data Choice : Set where
  editReview chooseBackend restoreClient restoreReadAccess : Text → Choice

data Obstacle : Set where
  backendUnavailable : Text → Obstacle
  modelStopped : Text → Maybe Signal → Obstacle
  toolStopped noSubmission : Text → Obstacle
  userDecision : Text → Obstacle

data Next : Set where
  finished : Next
  readAgain : Next
  enqueueFresh : Next
  onProvider : Signal → Next
  correctBackend : Text → Next
  askOperator : Choice → Next

pending : Turn → Obstacle → Next
pending _ (backendUnavailable detail) = correctBackend detail
pending _ (userDecision detail) = askOperator (editReview detail)
pending _ (modelStopped detail (just signal)) = onProvider signal
pending first (modelStopped detail nothing) = enqueueFresh
pending fresh (modelStopped detail nothing) = askOperator (chooseBackend detail)
pending first (toolStopped detail) = enqueueFresh
pending fresh (toolStopped detail) = askOperator (restoreClient detail)
pending first (noSubmission detail) = enqueueFresh
pending fresh (noSubmission detail) = askOperator (editReview detail)

afterRead : ∀ {selected} → Turn → Obstacle → O.Receipt selected → Next
afterRead turn obstacle O.unavailable = readAgain
afterRead turn obstacle (O.malformed fault) = askOperator (restoreReadAccess (Fault.explanation fault))
afterRead turn obstacle (O.found source valid (O.pending identity revision missing)) = pending turn obstacle
afterRead turn obstacle (O.found source valid (O.corrected identity change)) = finished
afterRead turn obstacle (O.found source valid (O.confirmed acknowledgement)) = finished

-- A failed turn goes behind every entry already waiting. New arrivals
-- join the same end. No sorting of experience IDs is involved.
data Task : Set where
  prepare verifySource : Task
  verifyOutcome : Obstacle → Task

record Entry : Set where
  constructor job
  field selected : O.Pin; turn : Turn; task : Task

entry : O.Pin → Turn → Entry
entry selected turn = job selected turn prepare

data CaseWriteError : Set where
  disconnected refused : Text → CaseWriteError

-- An ordinary scan may discover more work to run before a fresh attempt.
-- A pinned turn already belongs to that finite queue.
data Selection : Set where
  scanQueue : Selection
  runEntry : Entry → Selection

-- The repair command presents the cause together with the choice. Restoring
-- a shared service can release several cases on the same change notification.
instructions : Choice → Text
instructions (editReview detail) = detail ++ toList ". Open this revision in judge repair to correct or supply the review."
instructions (chooseBackend detail) = detail ++ toList ". Choose an available judge backend or restore the configured account in judge repair."
instructions (restoreClient detail) = detail ++ toList ". Restore the configured MCP client or select a compatible client in judge repair."
instructions (restoreReadAccess detail) = detail ++ toList ". Restore access to the identified source, then verify its current revision in judge repair."

record Case : Set where
  constructor repair
  field selected : O.Pin; choice : Choice

-- The action is tied to the case's own pin. Only the matching remedy opens
-- it again. Reviewing or changing the source also retires the old hold.
-- Older hosts could stop before delivering a correction, or refuse a valid
-- explanation request. Evidence that the corrected host handles that exact
-- obstruction releases the hold after rereading its still-pending source.
data RestoredValidation : Set where
  correctionFeedbackRestored explanationAdmissionRestored : RestoredValidation

data RemedyApplied (chosen : O.Pin) : Choice → Set where
  reviewed : ∀ {detail row} → O.SnapshotValid row → O.Ack chosen row → RemedyApplied chosen (editReview detail)
  backendReady : ∀ {detail} → RemedyApplied chosen (chooseBackend detail)
  clientReady : ∀ {detail} → RemedyApplied chosen (restoreClient detail)
  readable : ∀ {detail row} → O.SnapshotValid row → O.IdentityMatches chosen row →
    RemedyApplied chosen (restoreReadAccess detail)
  handlerRestored : ∀ {detail row} → O.SnapshotValid row → O.IdentityMatches chosen row →
    O.StillDeferred (O.deferred (O.Pin.identity chosen) (O.Pin.sourceRevision chosen)) row →
    RestoredValidation → RemedyApplied chosen (editReview detail)

data CaseState (problem : Case) : Set where
  unresolved : CaseState problem
  remedyApplied : RemedyApplied (Case.selected problem) (Case.choice problem) → CaseState problem

-- PostgreSQL rechecks the pin when registering the case. A racing save,
-- source edit or deletion cannot create a stale request for a decision.
data Publication (problem : Case) : Set where
  opened : ∀ row → O.SnapshotValid row → O.IdentityMatches (Case.selected problem) row →
    O.StillDeferred (O.deferred (O.Pin.identity (Case.selected problem))
      (O.Pin.sourceRevision (Case.selected problem))) row → Publication problem
  verificationNeeded : ∀ detail → Case.choice problem ≡ restoreReadAccess detail → Publication problem
  rescued : ∀ row → O.SnapshotValid row → O.Ack (Case.selected problem) row → Publication problem
  superseded : ∀ row → O.SnapshotValid row → O.IdentityMatches (Case.selected problem) row →
    (O.Snapshot.revision row ≡ O.Pin.sourceRevision (Case.selected problem) → ⊥) → Publication problem
  removed : Publication problem

held : O.Pin → List O.Deferred → Bool
held chosen = any (λ d → does (O.Pin.identity chosen ≟UUID O.Deferred.identity d) ∧
  does (O.Pin.sourceRevision chosen Integer.≟ O.Deferred.revision d))

record ObservedCase : Set where
  constructor observedCase
  field problem : Case; state : CaseState problem

exclusions : List ObservedCase → List O.Deferred
exclusions [] = []
exclusions (observedCase problem unresolved ∷ rest) =
  O.deferred (O.Pin.identity chosen) (O.Pin.sourceRevision chosen) ∷ exclusions rest
  where chosen = Case.selected problem
exclusions (observedCase problem (remedyApplied evidence) ∷ rest) = exclusions rest

remedyReleasesCase : ∀ problem evidence rest →
  exclusions (observedCase problem (remedyApplied evidence) ∷ rest) ≡ exclusions rest
remedyReleasesCase problem evidence rest = refl

restoredHandlerReleasesPendingCase : ∀ chosen detail row valid identity pending repaired rest →
  exclusions (observedCase (repair chosen (editReview detail))
    (remedyApplied (handlerRestored {row = row} valid identity pending repaired)) ∷ rest) ≡ exclusions rest
restoredHandlerReleasesPendingCase chosen detail row valid identity pending repaired rest = refl

requeue : List Entry → Entry → List Entry
requeue waiting item = waiting ++ item ∷ []

data BeforeTurn (selected : Entry) : List Entry → List Entry → Set where
  here : ∀ later → BeforeTurn selected [] (selected ∷ later)
  ahead : ∀ item {waiting queue} → BeforeTurn selected waiting queue →
    BeforeTurn selected (item ∷ waiting) (item ∷ queue)

freshBehindWaiting : ∀ waiting selected arrivals →
  BeforeTurn selected waiting (requeue waiting selected ++ arrivals)
freshBehindWaiting [] selected arrivals = here arrivals
freshBehindWaiting (item ∷ waiting) selected arrivals = ahead item (freshBehindWaiting waiting selected arrivals)

appendPreservesTurn : ∀ {selected waiting queue} → BeforeTurn selected waiting queue →
  ∀ arrivals → BeforeTurn selected waiting (queue ++ arrivals)
appendPreservesTurn (here later) arrivals = here (later ++ arrivals)
appendPreservesTurn (ahead item order) arrivals = ahead item (appendPreservesTurn order arrivals)
```
