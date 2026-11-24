{-# OPTIONS --safe #-}
-- CLI/watch policy around the existing review controller. Model claims are
-- never accepted as reports here: the runner/receipt composition produces the
-- report, then this module derives process status and watch behavior from it.
module Mimir.JudgeHost where

open import Data.Integer.Show using (show)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (Σ; _×_; _,_)
import Mimir.NotificationIncident as Mail
import Mimir.PublicEncoding as Encoding
import Mimir.ReviewObservation as O
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
    restoreToolClient selectWorkingBackend restoreLogAccess restoreMailAccess : Text → Remedy

guidance : Remedy → Text
guidance (correctConfiguration detail) = detail ++ toList ". Correct the named setting in the judge configuration and save it."
guidance (restoreStateAccess detail) = detail ++ toList ". Restore access to the state directory or select an accessible one."
guidance (restoreDatabaseSetup detail) = detail ++ toList ". Restore the database prerequisite named above or correct the configured database connection."
guidance (restoreToolClient detail) = detail ++ toList ". Select a working, compatible Mimir MCP command in the judge configuration."
guidance (restoreLogAccess detail) = detail ++ toList ". Restore write access to the configured log directory or select a writable directory."
guidance (restoreMailAccess detail) = detail ++ toList ". Restore access to the mail outbox or repair the configured mail account. Pending mail uses the corrected settings."
guidance (selectWorkingBackend detail) = detail ++ toList ". Choose an available judge backend or restore access to the configured one."

-- Only an identified remedy can produce a judge failure email. The existing
-- incident queue deduplicates its key and makes a new message due immediately.
data ActionRequired : Set where
  review : Recovery.Case → ActionRequired
  prerequisite : Remedy → ActionRequired

reviewKey : Encoding.Formatting → O.Pin → Text
reviewKey format chosen = Encoding.Formatting.uuidText format (O.Pin.identity chosen) ++
  toList "/" ++ toList (show (O.Pin.sourceRevision chosen))

savedReview : Encoding.Formatting → O.Pin → Mail.Event
savedReview format chosen = Mail.event (toList "judge-review") (reviewKey format chosen)
  Mail.recovery (just (toList "PostgreSQL confirmed this source revision's review."))

alert : Encoding.Formatting → ActionRequired → Mail.Event
alert format (review problem) = Mail.event (toList "judge-review") (reviewKey format chosen)
  (Mail.failure (toList "review_requires_repair") (Recovery.instructions (Recovery.Case.choice problem)))
  (just (toList "Open this review and choose a remedy: mimir judge repair --experience " ++
    identity ++ toList " --revision " ++ revision))
  where
  chosen = Recovery.Case.selected problem
  identity = Encoding.Formatting.uuidText format (O.Pin.identity chosen)
  revision = toList (show (O.Pin.sourceRevision chosen))
alert format (prerequisite remedy) = Mail.event (toList "judge") (codeOf remedy)
  (Mail.failure (codeOf remedy) (guidance remedy)) (just (guidance remedy))
  where
  codeOf : Remedy → Text
  codeOf (correctConfiguration _) = toList "invalid_config"
  codeOf (restoreStateAccess _) = toList "state_unavailable"
  codeOf (restoreDatabaseSetup _) = toList "database_setup"
  codeOf (restoreToolClient _) = toList "mcp_unavailable"
  codeOf (selectWorkingBackend _) = toList "backend_unavailable"
  codeOf (restoreLogAccess _) = toList "logging_unavailable"
  codeOf (restoreMailAccess _) = toList "notification_unavailable"

-- The storage adapter supplies the pre- and post-state of the matching
-- incident. Repeated reports reuse its delivery state.
record Reconciled (event : Mail.Event) : Set where
  field
    identity : Text
    now : ℕ
    before after : Mail.Incident
    sameSource : Mail.Incident.source before ≡ Mail.Event.source event
    sameKey : Mail.Incident.incidentKey before ≡ Mail.Event.incidentKey event
    applied : after ≡ Mail.reconcile identity now before event

Recorded : Encoding.Formatting → ActionRequired → Set
Recorded format action = Reconciled (alert format action)

newActionIsDueNow : ∀ format action (receipt : Recorded format action) →
  Mail.Incident.activeCode (Reconciled.before receipt) ≡ nothing →
  Σ Mail.Alert (λ queued → Mail.Incident.outbox (Reconciled.after receipt) ≡ just queued ×
    Mail.Alert.nextDue queued ≡ Reconciled.now receipt)
newActionIsDueNow format (review problem) receipt inactive
  rewrite Reconciled.applied receipt = Mail.firstFailureAlertIsDueNow _ _ _ _ _ _ _ _ inactive
newActionIsDueNow format (prerequisite remedy) receipt inactive
  rewrite Reconciled.applied receipt = Mail.firstFailureAlertIsDueNow _ _ _ _ _ _ _ _ inactive

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
