{-# OPTIONS --safe #-}
-- Exact finish_report order: stamp, finalize trace, persist incident, persist
-- status, notify, persist status again. An early status-write failure prevents
-- mail; mail failure does not erase a confirmed review or change its counts.
module Mimir.JudgeFinalization where

open import Data.Bool using (Bool; true; false)
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
import Mimir.DiagnosticText as Bounded
import Mimir.JudgeStateRecords as Records
import Mimir.Effects as Effects

module R = Records.Over ℕ

data Effect : Set where
  clock : Effect
  finishTrace : ℕ → R.Report → Effect
  recordIncident writeStatus : R.Report → Effect
  notify : R.Report → Effect

Reply : Effect → Set
Reply clock = Maybe ℕ
Reply (finishTrace id report) = Text ⊎ ⊤
Reply (recordIncident report) = Text ⊎ ⊤
Reply (writeStatus report) = Text ⊎ ⊤
Reply (notify report) = Text ⊎ Text -- notification result field, not a replacement report

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

afterFirstWrite : R.Report → Text ⊎ ⊤ → Script R.Report
afterFirstWrite report (inj₁ error) = done (blocked (toList "state_write_error") report)
afterFirstWrite report (inj₂ tt) = ask (notify report) (afterNotification report)

afterIncident : R.Report → Text ⊎ ⊤ → Script R.Report
afterIncident report (inj₁ error) = ask (writeStatus updated) (afterFirstWrite updated)
  where updated = blocked (toList "incident_write_error") report
afterIncident report (inj₂ tt) = ask (writeStatus report) (afterFirstWrite report)

incident : R.Report → Script R.Report
incident report = ask (recordIncident report) (afterIncident report)

afterTrace : R.Report → Text ⊎ ⊤ → Script R.Report
afterTrace report (inj₁ error) = incident (record (blocked (toList "diagnostics_write_error") report)
  { failureDetail = just (Bounded.bounded 512 error) })
afterTrace report (inj₂ tt) with does (R.Report.status report ≟Text toList "complete")
... | true = incident (record report { diagnosticsId = nothing })
... | false = incident report

afterStamp : R.Report → Script R.Report
afterStamp report with R.Report.diagnosticsId report
... | nothing = incident report
... | just id = ask (finishTrace id report) (afterTrace report)

finish : R.Report → Script R.Report
finish report = ask clock (λ observed → afterStamp (R.stamp observed report))

counts : R.Report → ℕ × (ℕ × (ℕ × (ℕ × ℕ)))
counts report = R.Report.selected report , R.Report.confirmed report , R.Report.corrected report ,
  R.Report.pending report , R.Report.unavailable report

failureRetainsCounts : ∀ reason report → counts (blocked reason report) ≡ counts report
failureRetainsCounts reason report = refl

firstWriteFailureStops : ∀ report error → afterFirstWrite report (inj₁ error) ≡
  done (blocked (toList "state_write_error") report)
firstWriteFailureStops report error = refl
