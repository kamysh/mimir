{-# OPTIONS --safe #-}
-- Exact finish_report order: stamp, finalize trace, persist incident, persist
-- status, notify, persist status again. Reporting errors are reported separately
-- and do not replace the observed review outcome.
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
import Mimir.JudgeStateRecords as Records
import Mimir.JudgeAcknowledgement as Acknowledgement
import Mimir.Effects as Effects

open import Mimir.UUIDGroups using (UUID)

module R = Records.Over UUID

data Effect : Set where
  clock : Effect
  finishTrace : UUID → R.Report → Effect
  reportProblem : Text → Text → Effect
  recordIncident : (report : R.Report) →
    Maybe (Acknowledgement.BatchEvidence (R.Report.selectedIds report)) → Effect
  writeStatus : R.Report → Effect
  notify : R.Report → Effect

Reply : Effect → Set
Reply clock = Maybe ℕ
Reply (finishTrace id report) = Text ⊎ ⊤
-- The acknowledgement records an attempt, not successful delivery.
Reply (reportProblem whereFailed detail) = ⊤
Reply (recordIncident report confirmation) = Text ⊎ ⊤
Reply (writeStatus report) = Text ⊎ ⊤
Reply (notify report) = Text ⊎ Text -- notification result field, not a replacement report

module E = Effects.Protocol Effect Reply
open E

blocked : Text → R.Report → R.Report
blocked reason report = record report { status = toList "blocked" ; blockReason = just reason }

afterLastWrite : R.Report → Text ⊎ ⊤ → Script R.Report
afterLastWrite report (inj₁ error) = ask (reportProblem (toList "status") error) (λ _ → done report)
afterLastWrite report (inj₂ tt) = done report

afterNotification : R.Report → Text ⊎ Text → Script R.Report
afterNotification report (inj₁ error) = ask (reportProblem (toList "notification") error) λ _ →
  ask (writeStatus updated) (afterLastWrite updated)
  where updated = record report { notification = toList "unavailable" }
afterNotification report (inj₂ value) = ask (writeStatus updated) (afterLastWrite updated)
  where updated = record report { notification = value }

afterFirstWrite : R.Report → Text ⊎ ⊤ → Script R.Report
afterFirstWrite report (inj₁ error) = ask (reportProblem (toList "status") error) λ _ →
  ask (notify report) (afterNotification report)
afterFirstWrite report (inj₂ tt) = ask (notify report) (afterNotification report)

afterIncident : R.Report → Text ⊎ ⊤ → Script R.Report
afterIncident report (inj₁ error) = ask (reportProblem (toList "incident") error) λ _ →
  ask (writeStatus report) (afterFirstWrite report)
afterIncident report (inj₂ tt) = ask (writeStatus report) (afterFirstWrite report)

incident : (report : R.Report) → Maybe (Acknowledgement.BatchEvidence (R.Report.selectedIds report)) → Script R.Report
incident report confirmation = ask (recordIncident report confirmation) (afterIncident report)

afterTrace : (report : R.Report) → Maybe (Acknowledgement.BatchEvidence (R.Report.selectedIds report)) →
  Text ⊎ ⊤ → Script R.Report
afterTrace report confirmation (inj₁ error) = ask (reportProblem (toList "trace") error) λ _ → incident report confirmation
afterTrace report confirmation (inj₂ tt) with does (R.Report.status report ≟Text toList "complete")
... | true = incident (record report { diagnosticsId = nothing }) confirmation
... | false = incident report confirmation

afterStamp : (report : R.Report) → Maybe (Acknowledgement.BatchEvidence (R.Report.selectedIds report)) → Script R.Report
afterStamp report confirmation with R.Report.diagnosticsId report
... | nothing = incident report confirmation
... | just id = ask (finishTrace id report) (afterTrace report confirmation)

finish : (report : R.Report) → Maybe (Acknowledgement.BatchEvidence (R.Report.selectedIds report)) → Script R.Report
finish report confirmation = ask clock (λ observed → afterStamp (R.stamp observed report) confirmation)

-- Finalization may update notification metadata, but no combination of
-- reporting results may change the review status or reason.
OutcomePreserved : R.Report → R.Report → Set
OutcomePreserved before after = R.Report.status after ≡ R.Report.status before ×
  R.Report.blockReason after ≡ R.Report.blockReason before

lastWritePreserves : ∀ report reply events result →
  Runs (afterLastWrite report reply) events result → OutcomePreserved report result
lastWritePreserves report (inj₁ error) events result (replied _ _ warning (returned .report)) = refl , refl
lastWritePreserves report (inj₂ tt) events result (returned .report) = refl , refl

notificationPreserves : ∀ report reply events result →
  Runs (afterNotification report reply) events result → OutcomePreserved report result
notificationPreserves report (inj₁ error) events result (replied _ _ warning (replied _ _ reply rest)) =
  lastWritePreserves _ reply _ result rest
notificationPreserves report (inj₂ value) events result (replied _ _ reply rest) =
  lastWritePreserves _ reply _ result rest

firstWritePreserves : ∀ report reply events result →
  Runs (afterFirstWrite report reply) events result → OutcomePreserved report result
firstWritePreserves report (inj₁ error) events result (replied _ _ warning (replied _ _ reply rest)) =
  notificationPreserves report reply _ result rest
firstWritePreserves report (inj₂ tt) events result (replied _ _ reply rest) =
  notificationPreserves report reply _ result rest

incidentPreserves : ∀ report reply events result →
  Runs (afterIncident report reply) events result → OutcomePreserved report result
incidentPreserves report (inj₁ error) events result (replied _ _ warning (replied _ _ reply rest)) =
  firstWritePreserves report reply _ result rest
incidentPreserves report (inj₂ tt) events result (replied _ _ reply rest) =
  firstWritePreserves report reply _ result rest

tracePreserves : ∀ report confirmation reply events result →
  Runs (afterTrace report confirmation reply) events result → OutcomePreserved report result
tracePreserves report confirmation (inj₁ error) events result (replied _ _ warning (replied _ _ reply rest)) =
  incidentPreserves report reply _ result rest
tracePreserves report confirmation (inj₂ tt) events result run with does (R.Report.status report ≟Text toList "complete")
... | true with run
...   | replied _ _ reply rest = incidentPreserves _ reply _ result rest
tracePreserves report confirmation (inj₂ tt) events result run | false with run
...   | replied _ _ reply rest = incidentPreserves report reply _ result rest

stampPreserves : ∀ report confirmation events result → Runs (afterStamp report confirmation) events result → OutcomePreserved report result
stampPreserves report confirmation events result run with R.Report.diagnosticsId report
... | nothing with run
...   | replied _ _ reply rest = incidentPreserves report reply _ result rest
stampPreserves report confirmation events result run | just id with run
...   | replied _ _ reply rest = tracePreserves report confirmation reply _ result rest

finalizationPreservesOutcome : ∀ report confirmation events result →
  Runs (finish report confirmation) events result → OutcomePreserved report result
finalizationPreservesOutcome report confirmation events result (replied _ _ observed rest) =
  stampPreserves (R.stamp observed report) confirmation _ result rest
