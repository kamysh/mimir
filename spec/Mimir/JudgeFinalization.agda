{-# OPTIONS --safe #-}
-- Exact finish_report order: stamp, finalize trace, persist incident, persist
-- status, notify inline or enqueue, then persist status again. Watch mode uses
-- queue admission; an active SMTP/OAuth exchange is not a core prerequisite.
module Mimir.JudgeFinalization where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.String using (toList)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.JudgeStateRecords as Records
import Mimir.Effects as Effects
import Mimir.NotificationConfig as Email
import Mimir.NotificationIncident as Notification
import Mimir.ConfigurationValues as Values
import Mimir.UnixPath as Path
import Mimir.JudgeHost as Host

module R = Records.Over ℕ

data NotificationMode : Set where inlineDelivery queuedDelivery : NotificationMode

-- Jobs capture the admitted settings. Queue admission is independent of an
-- active delivery's completion; cancellation explicitly ends the owned worker.
data Job : Set where
  alertJob : Email.Config → Path.Path → Notification.Event → Job
  digestJob : Email.Config → Values.Database → Path.Path → Host.Outcome → Job

module WorkerQueue where
  data State : Set where
    running : Maybe Job → List Job → State
    stopped : State

  push : Job → State → State
  push job (running active pending) = running active (pending ++ (job ∷ []))
  push job stopped = stopped

  data Accepted (job : Job) : State → State → Set where
    queued : ∀ active pending → Accepted job (running active pending) (push job (running active pending))

  acceptsWhileDeliveryIsStalled : ∀ active pending job →
    Accepted job (running (just active) pending) (push job (running (just active) pending))
  acceptsWhileDeliveryIsStalled active pending job = queued (just active) pending

  data Joined : State → State → Set where
    cancelled : ∀ active pending → Joined (running active pending) stopped
    alreadyStopped : Joined stopped stopped

  shutdownLeavesNoWorker : ∀ before after → Joined before after → after ≡ stopped
  shutdownLeavesNoWorker before .stopped (cancelled active pending) = refl
  shutdownLeavesNoWorker .stopped .stopped alreadyStopped = refl

data Effect : Set where
  clock : Effect
  finishTrace : ℕ → R.Report → Effect
  recordIncident writeStatus : R.Report → Effect
  notify enqueueNotification : R.Report → Effect

Reply : Effect → Set
Reply clock = Maybe ℕ
Reply (finishTrace id report) = Text ⊎ ⊤
Reply (recordIncident report) = Text ⊎ ⊤
Reply (writeStatus report) = Text ⊎ ⊤
Reply (notify report) = Text ⊎ Text -- delivery outcome
Reply (enqueueNotification report) = Text ⊎ Text -- queue admission, no SMTP wait

module E = Effects.Protocol Effect Reply
open E

blocked : Text → R.Report → R.Report
blocked reason report = record report { status = toList "blocked" ; blockReason = just reason }

afterLastWrite : R.Report → Text ⊎ ⊤ → Script R.Report
afterLastWrite report (inj₁ error) = done (blocked (toList "state_write_error") report)
afterLastWrite report (inj₂ tt) = done report

afterNotification : R.Report → Text ⊎ Text → Script R.Report
afterNotification report (inj₁ error) = ask (writeStatus updated) (afterLastWrite updated)
  where updated = record report { notification = toList "unavailable" }
afterNotification report (inj₂ value) = ask (writeStatus updated) (afterLastWrite updated)
  where updated = record report { notification = value }

afterFirstWrite : NotificationMode → R.Report → Text ⊎ ⊤ → Script R.Report
afterFirstWrite mode report (inj₁ error) = done (blocked (toList "state_write_error") report)
afterFirstWrite inlineDelivery report (inj₂ tt) = ask (notify report) (afterNotification report)
afterFirstWrite queuedDelivery report (inj₂ tt) = ask (enqueueNotification report) (afterNotification report)

afterIncident : NotificationMode → R.Report → Text ⊎ ⊤ → Script R.Report
afterIncident mode report (inj₁ error) = ask (writeStatus updated) (afterFirstWrite mode updated)
  where updated = blocked (toList "incident_write_error") report
afterIncident mode report (inj₂ tt) = ask (writeStatus report) (afterFirstWrite mode report)

incident : NotificationMode → R.Report → Script R.Report
incident mode report = ask (recordIncident report) (afterIncident mode report)

afterTrace : NotificationMode → R.Report → Text ⊎ ⊤ → Script R.Report
afterTrace mode report (inj₁ error) = incident mode (record (blocked (toList "diagnostics_write_error") report)
  { failureDetail = just error })
afterTrace mode report (inj₂ tt) with does (R.Report.status report ≟Text toList "complete")
... | true = incident mode (record report { diagnosticsId = nothing })
... | false = incident mode report

afterStamp : NotificationMode → R.Report → Script R.Report
afterStamp mode report with R.Report.diagnosticsId report
... | nothing = incident mode report
... | just id = ask (finishTrace id report) (afterTrace mode report)

finishWith : NotificationMode → R.Report → Script R.Report
finishWith mode report = ask clock (λ observed → afterStamp mode (R.stamp observed report))

finish : R.Report → Script R.Report
finish = finishWith inlineDelivery

counts : R.Report → ℕ × (ℕ × (ℕ × (ℕ × ℕ)))
counts report = R.Report.selected report , R.Report.confirmed report , R.Report.corrected report ,
  R.Report.pending report , R.Report.unavailable report

failureRetainsCounts : ∀ reason report → counts (blocked reason report) ≡ counts report
failureRetainsCounts reason report = refl

firstWriteFailureStops : ∀ mode report error → afterFirstWrite mode report (inj₁ error) ≡
  done (blocked (toList "state_write_error") report)
firstWriteFailureStops mode report error = refl

-- A core finalization on the worker path never requests synchronous delivery.
-- Its completion therefore owes no SMTP/OAuth completion receipt.
NoInlineDelivery : ∀ {A} → Script A → Set
NoInlineDelivery (done value) = ⊤
NoInlineDelivery (ask (notify report) next) = ⊥
NoInlineDelivery (ask effect next) = ∀ reply → NoInlineDelivery (next reply)

lastWriteNoDelivery : ∀ report reply → NoInlineDelivery (afterLastWrite report reply)
lastWriteNoDelivery report (inj₁ error) = tt
lastWriteNoDelivery report (inj₂ tt) = tt

notificationNoDelivery : ∀ report reply → NoInlineDelivery (afterNotification report reply)
notificationNoDelivery report (inj₁ error) = lastWriteNoDelivery _
notificationNoDelivery report (inj₂ result) = lastWriteNoDelivery _

firstWriteNoDelivery : ∀ report reply → NoInlineDelivery (afterFirstWrite queuedDelivery report reply)
firstWriteNoDelivery report (inj₁ error) = tt
firstWriteNoDelivery report (inj₂ tt) = notificationNoDelivery report

incidentReplyNoDelivery : ∀ report reply → NoInlineDelivery (afterIncident queuedDelivery report reply)
incidentReplyNoDelivery report (inj₁ error) = firstWriteNoDelivery _
incidentReplyNoDelivery report (inj₂ tt) = firstWriteNoDelivery _

incidentNoDelivery : ∀ report → NoInlineDelivery (incident queuedDelivery report)
incidentNoDelivery report = incidentReplyNoDelivery report

traceNoDelivery : ∀ report reply → NoInlineDelivery (afterTrace queuedDelivery report reply)
traceNoDelivery report (inj₁ error) = incidentNoDelivery _
traceNoDelivery report (inj₂ tt) with does (R.Report.status report ≟Text toList "complete")
... | true = incidentNoDelivery _
... | false = incidentNoDelivery _

stampNoDelivery : ∀ report → NoInlineDelivery (afterStamp queuedDelivery report)
stampNoDelivery report with R.Report.diagnosticsId report
... | nothing = incidentNoDelivery _
... | just id = traceNoDelivery _

queuedFinalizationNeedsNoDelivery : ∀ report → NoInlineDelivery (finishWith queuedDelivery report)
queuedFinalizationNeedsNoDelivery report observed = stampNoDelivery (R.stamp observed report)
