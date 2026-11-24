{-# OPTIONS --safe #-}
-- CLI/watch policy around the existing review controller. Model claims are
-- never accepted as reports here: the runner/receipt composition produces the
-- report, then this module derives process status and watch behavior from it.
module Mimir.JudgeHost where

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.List using (List; _++_)
open import Data.Nat using (ℕ)
open import Data.String using (toList)
open import Relation.Nullary using (does)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.JudgeRevisionPolicy as Recovery
import Mimir.JudgeStateRecords as Records

open import Mimir.UUIDGroups using (UUID)

module State = Records.Over UUID

data Exit : Set where success invalidConfig incomplete alreadyRunning unavailable : Exit

code : Exit → ℕ
code success = 0
code invalidConfig = 2
code incomplete = 3
code alreadyRunning = 4
code unavailable = 5

-- Each case names a correction the operator can make. The observed detail
-- travels with the action all the way to the immediate notification.
data Remedy : Set where
  correctConfiguration restoreStateAccess restoreDatabaseSetup
    restoreToolClient selectWorkingBackend : Text → Remedy

guidance : Remedy → Text
guidance (correctConfiguration detail) = detail ++ toList ". Correct the named setting in the judge configuration and save it."
guidance (restoreStateAccess detail) = detail ++ toList ". Restore access to the state directory or select an accessible one."
guidance (restoreDatabaseSetup detail) = detail ++ toList ". Restore the database prerequisite named above or correct the configured database connection."
guidance (restoreToolClient detail) = detail ++ toList ". Select a working, compatible Mimir MCP command in the judge configuration."
guidance (selectWorkingBackend detail) = detail ++ toList ". Choose an available judge backend or restore access to the configured one."

data Continuation : Set where
  scan whenWorkArrives whenLockReleased whenDatabaseReturns whenProviderAvailable : Continuation
  scheduled : List Recovery.Entry → Continuation
  whenCorrected : Remedy → Continuation
  whenProviderResets : ℕ → Continuation

-- The report is for display. Its producer must also supply the next action.
record Batch : Set where
  constructor batch
  field report : State.Report; continuation : Continuation

record Outcome : Set where
  constructor outcome
  field exit : Exit; continuation : Continuation

is : Text → Text → Bool
is actual expected = does (actual ≟Text expected)

reportExit : State.Report → Exit
reportExit report with is status (toList "idle") ∨ is status (toList "complete")
  where status = State.Report.status report
... | true = success
... | false with is (State.Report.status report) (toList "partial") ∨ is (State.Report.status report) (toList "blocked")
...   | true = incomplete
...   | false = unavailable

outcomeOf : Batch → Outcome
outcomeOf (batch report next) = outcome (reportExit report) next
