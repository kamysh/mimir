{-# OPTIONS --safe #-}
-- Required query semantics inside the digest's explicitly requested read-only
-- REPEATABLE READ transaction. This is an application protocol contract, not
-- a new PostgreSQL axiom or a derivation from READ COMMITTED.
module Mimir.JudgeDigestSnapshot where

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Integer using (ℤ; _+_; +_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (just)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.JudgeDigest as Digest
import Mimir.LearningHistoryWire as Ledger
import Mimir.LocalCalendar as Local
open import Mimir.Text using (Text)

data State : Set where idle closed : State; active : Ledger.Database → State

data Step (connection : ℕ) : State → Digest.Event → State → Set where
  began : ∀ snapshot → Step connection idle (Digest.beginReadOnlyRepeatable connection , inj₂ tt) (active snapshot)
  beginFailed : ∀ error → Step connection idle (Digest.beginReadOnlyRepeatable connection , inj₁ error) idle
  counted : ∀ snapshot start end →
    Digest.I64.InRange (Digest.Counts.newExperiences (Digest.selectedCounts snapshot start end)) →
    Digest.I64.InRange (Digest.Counts.sourceRevisions (Digest.selectedCounts snapshot start end)) →
    Digest.I64.InRange (Digest.Counts.judgeReviews (Digest.selectedCounts snapshot start end)) →
    Step connection (active snapshot) (Digest.countBetween connection start end , inj₂ (Digest.selectedCounts snapshot start end)) (active snapshot)
  countFailed : ∀ snapshot start end error → Step connection (active snapshot)
    (Digest.countBetween connection start end , inj₁ error) (active snapshot)
  pending : ∀ snapshot → Digest.I64.InRange (Digest.backlog snapshot) →
    Step connection (active snapshot) (Digest.countBacklog connection , inj₂ (Digest.backlog snapshot)) (active snapshot)
  pendingFailed : ∀ snapshot error → Step connection (active snapshot) (Digest.countBacklog connection , inj₁ error) (active snapshot)
  committed : ∀ snapshot → Step connection (active snapshot) (Digest.commit connection , inj₂ tt) idle
  uncertainCommit : ∀ snapshot error → Step connection (active snapshot) (Digest.commit connection , inj₁ error) closed
  dropped : ∀ before → Step connection before (Digest.close connection , tt) closed

data Trace (connection : ℕ) : State → List Digest.Event → State → Set where
  empty : ∀ state → Trace connection state [] state
  more : ∀ {before event middle events after} → Step connection before event middle →
    Trace connection middle events after → Trace connection before (event ∷ events) after

-- The digest protocol has no graph/ledger mutation constructor. In particular
-- its successful counts are projections of one retained transaction snapshot.
countedExactly : ∀ connection snapshot start end result after →
  Step connection (active snapshot) (Digest.countBetween connection start end , inj₂ result) after →
  result ≡ Digest.selectedCounts snapshot start end
countedExactly connection snapshot start end result after (counted _ _ _ _ _ _) = refl

-- The displayed date and the exact query interval are justified together,
-- while all count definitions and the retained snapshot remain unchanged.
countedForDisplayedDay : ∀ calendar day (range : Local.Window calendar day)
  connection snapshot result after →
  Step connection (active snapshot)
    (Digest.countBetween connection (Local.Window.start range) (Local.Window.end range) , inj₂ result) after →
  result ≡ Digest.selectedCounts snapshot (Local.Window.start range) (Local.Window.end range) ×
  Digest.Calendar.parse calendar (Digest.Calendar.showDay calendar day) ≡ just day ×
  Local.Local.day (Digest.Calendar.localAt calendar (Local.Window.start range)) ≡ day ×
  Local.Local.day (Digest.Calendar.localAt calendar (Local.Window.end range)) ≡ day + + 1
countedForDisplayedDay calendar day range connection snapshot result after receipt =
  countedExactly connection snapshot (Local.Window.start range) (Local.Window.end range) result after receipt ,
  Local.windowLabel range , Local.windowDates range
