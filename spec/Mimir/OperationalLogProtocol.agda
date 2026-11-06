{-# OPTIONS --safe #-}
-- Completed native observations for one log write. Successful acquisition and
-- file receipts are supplied by the filesystem adapter, never inferred from
-- a request. The same handle remains owned until unlock/descriptor close.
module Mimir.OperationalLogProtocol where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _≤_; _*_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Mimir.Text using (Text)
import Mimir.OperationalLogRetention as Log
import Mimir.OperationalLogSteps as Steps

module For (limit archives : ℕ) (directory : Text) where
  private
    Files = Log.State limit archives
    Action = Steps.Action (suc archives)

  -- Numbered slots belong to directory; handle is the descriptor that owns
  -- its process-independent lock. Missing/empty slots have no contents.
  data Event : Set where
    acquired : Text → ℕ → Event
    lockFailed : Text → Text → Event
    read : ℕ → Files → Event
    readFailed : ℕ → Text → Event
    changed : ℕ → Action → Event
    changeFailed changeUncertain : ℕ → Action → Text → Event
    appended : ℕ → List Log.Byte → Event
    appendFailed : ℕ → List Log.Byte → ℕ → Text → Event
    released : ℕ → Event

  data ChangeResult : Set where
    complete : Files → ChangeResult
    stopped : Files → Text → ChangeResult

  data Changes (handle : ℕ) : List Action → Files → List Event → ChangeResult → Set where
    done : ∀ files → Changes handle [] files [] (complete files)
    acknowledged : ∀ action remaining before events result →
      Changes handle remaining (Steps.apply action before) events result →
      Changes handle (action ∷ remaining) before (changed handle action ∷ events) result
    failed : ∀ action remaining before error → Changes handle (action ∷ remaining) before
      (changeFailed handle action error ∷ []) (stopped before error)
    uncertain : ∀ action remaining before error → Changes handle (action ∷ remaining) before
      (changeUncertain handle action error ∷ []) (stopped (Steps.apply action before) error)

  changesExact : ∀ handle actions before events after → Changes handle actions before events (complete after) →
    after ≡ Steps.run actions before
  changesExact handle .[] before .[] .before (done .before) = refl
  changesExact handle .(action ∷ remaining) before .(changed handle action ∷ events) after
    (acknowledged action remaining .before events .(complete after) rest) = changesExact handle remaining _ events after rest

  completedRotation : ∀ handle entry before events after →
    Changes handle (Steps.Plan.actions (Steps.prepare entry before)) before events (complete after) →
    after ≡ Steps.Plan.base (Steps.prepare entry before)
  completedRotation handle entry before events after execution = trans (changesExact handle _ before events after execution)
    (Steps.Plan.reachesBase (Steps.prepare entry before))

  -- A failed remove/rename leaves precisely a prefix of the planned changes,
  -- possibly including the interrupted action. No other small file set fits.
  failureReachable : ∀ handle actions before events after error → Changes handle actions before events (stopped after error) →
    Σ (List Action) (λ applied → Σ (List Action) (λ remaining →
      actions ≡ applied ++ remaining × after ≡ Steps.run applied before))
  failureReachable handle actions before events after error (acknowledged action remaining .before restEvents .(stopped after error) execution)
    with failureReachable handle remaining (Steps.apply action before) restEvents after error execution
  ... | applied , pending , same , reached = (action ∷ applied) , pending , cong (action ∷_) same , reached
  failureReachable handle actions before events after error (failed action remaining .before .error) =
    [] , (action ∷ remaining) , refl , refl
  failureReachable handle actions before events after error (uncertain action remaining .before .error) =
    (action ∷ []) , remaining , refl , refl

  data Outcome : Set where
    written : Files → Outcome
    failed : Text → Maybe Files → Outcome

  -- The unlock attempt and descriptor close form released. Close releases
  -- this native lock even if explicit unlock reported an error, as in JudgeLock.
  -- These are completed observations, not a promise of crash durability.
  data Attempt (entry : List Log.Byte) : List Event → Outcome → Set where
    denied : ∀ error → Attempt entry (lockFailed directory error ∷ []) (failed error nothing)
    unread : ∀ handle error → Attempt entry
      (acquired directory handle ∷ readFailed handle error ∷ released handle ∷ []) (failed error nothing)
    rotationFailed : ∀ handle before events after error →
      Changes handle (Steps.Plan.actions (Steps.prepare entry before)) before events (stopped after error) →
      Attempt entry (acquired directory handle ∷ read handle before ∷ (events ++ (released handle ∷ []))) (failed error (just after))
    writeFailed : ∀ handle before events count error →
      Changes handle (Steps.Plan.actions (Steps.prepare entry before)) before events
        (complete (Steps.Plan.base (Steps.prepare entry before))) →
      Attempt entry (acquired directory handle ∷ read handle before ∷ (events ++
        (appendFailed handle (Log.File.bytes (Log.clip limit entry)) count error ∷ released handle ∷ [])))
        (failed error (just (Steps.partial entry before count)))
    saved : ∀ handle before events →
      Changes handle (Steps.Plan.actions (Steps.prepare entry before)) before events
        (complete (Steps.Plan.base (Steps.prepare entry before))) →
      Attempt entry (acquired directory handle ∷ read handle before ∷ (events ++
        (appended handle (Log.File.bytes (Log.clip limit entry)) ∷ released handle ∷ [])))
        (written (Steps.appendCurrent (Steps.Plan.base (Steps.prepare entry before))
          (Log.File.bytes (Log.clip limit entry)) (Steps.Plan.fits (Steps.prepare entry before))))

  -- Success exposes the actual locked read, exact full entry, successful
  -- changes and close. A bounded contents value alone supplies none of these.
  writtenRequiresReceipts : ∀ entry events after → Attempt entry events (written after) →
    Σ ℕ (λ handle → Σ Files (λ before → Σ (List Event) (λ changes →
      Changes handle (Steps.Plan.actions (Steps.prepare entry before)) before changes
        (complete (Steps.Plan.base (Steps.prepare entry before))) ×
      (events ≡ acquired directory handle ∷ read handle before ∷ (changes ++
        (appended handle (Log.File.bytes (Log.clip limit entry)) ∷ released handle ∷ [])) ×
       after ≡ Log.append entry before))))
  writtenRequiresReceipts entry events after (saved handle before changes execution) =
    handle , before , changes , execution , refl , Steps.planExact entry before

  retainedBound : ∀ entry events outcome (execution : Attempt entry events outcome) files →
    ((outcome ≡ written files) ⊎ (Σ Text (λ error → outcome ≡ failed error (just files)))) →
    Log.size files ≤ suc archives * limit
  retainedBound entry events outcome execution files observed = Log.boundedTotal files

  -- Independent access policy: every read/mutation uses the acquired handle,
  -- and descriptor cleanup ends the owned region on success and failure.
  data Scope : Set where outside : Scope; owned : ℕ → Scope

  data Allowed : Scope → Event → Scope → Set where
    lock : ∀ handle → Allowed outside (acquired directory handle) (owned handle)
    refused : ∀ error → Allowed outside (lockFailed directory error) outside
    inspected : ∀ handle files → Allowed (owned handle) (read handle files) (owned handle)
    unreadable : ∀ handle error → Allowed (owned handle) (readFailed handle error) (owned handle)
    altered : ∀ handle action → Allowed (owned handle) (changed handle action) (owned handle)
    unaltered : ∀ handle action error → Allowed (owned handle) (changeFailed handle action error) (owned handle)
    uncertain : ∀ handle action error → Allowed (owned handle) (changeUncertain handle action error) (owned handle)
    wrote : ∀ handle bytes → Allowed (owned handle) (appended handle bytes) (owned handle)
    partial : ∀ handle bytes count error → Allowed (owned handle) (appendFailed handle bytes count error) (owned handle)
    closed : ∀ handle → Allowed (owned handle) (released handle) outside

  data Trace : Scope → List Event → Scope → Set where
    empty : ∀ scope → Trace scope [] scope
    more : ∀ {before middle after event events} → Allowed before event middle → Trace middle events after →
      Trace before (event ∷ events) after

  traceAppend : ∀ {before middle after events rest} → Trace before events middle → Trace middle rest after →
    Trace before (events ++ rest) after
  traceAppend (empty _) suffix = suffix
  traceAppend (more allowed prefix) suffix = more allowed (traceAppend prefix suffix)

  changesOwned : ∀ handle actions before events result → Changes handle actions before events result →
    Trace (owned handle) events (owned handle)
  changesOwned handle actions before events result (done _) = empty _
  changesOwned handle actions before events result (acknowledged action remaining initial rest resultValue execution) =
    more (altered handle action) (changesOwned handle remaining _ rest resultValue execution)
  changesOwned handle actions before events result (failed action remaining initial error) =
    more (unaltered handle action error) (empty _)
  changesOwned handle actions before events result (uncertain action remaining initial error) =
    more (uncertain handle action error) (empty _)

  attemptOwnsEveryFileOperation : ∀ entry events outcome → Attempt entry events outcome → Trace outside events outside
  attemptOwnsEveryFileOperation entry events outcome (denied error) = more (refused error) (empty outside)
  attemptOwnsEveryFileOperation entry events outcome (unread handle error) =
    more (lock handle) (more (unreadable handle error) (more (closed handle) (empty outside)))
  attemptOwnsEveryFileOperation entry events outcome (rotationFailed handle before changes after error execution) =
    more (lock handle) (more (inspected handle before)
      (traceAppend (changesOwned handle _ before changes _ execution) (more (closed handle) (empty outside))))
  attemptOwnsEveryFileOperation entry events outcome (writeFailed handle before changes count error execution) =
    more (lock handle) (more (inspected handle before) (traceAppend (changesOwned handle _ before changes _ execution)
      (more (partial handle _ count error) (more (closed handle) (empty outside)))))
  attemptOwnsEveryFileOperation entry events outcome (saved handle before changes execution) =
    more (lock handle) (more (inspected handle before) (traceAppend (changesOwned handle _ before changes _ execution)
      (more (wrote handle _) (more (closed handle) (empty outside)))))
