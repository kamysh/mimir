{-# OPTIONS --safe #-}
-- Exact finish_report order: stamp, persist incident, persist
-- status, read delivery status, persist status again. Reporting errors are reported separately
-- and do not replace the observed review outcome.
module Mimir.JudgeFinalization where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.String using (toList)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.JudgeHost as Host
import Mimir.JudgeStateRecords as Records
import Mimir.JudgeAcknowledgement as Acknowledgement
import Mimir.Effects as Effects

open import Mimir.UUIDGroups using (UUID)

module R = Records.Over UUID

data Effect : Set where
  clock : Effect
  reportProblem : Host.Remedy → Effect
  recordIncident : (report : R.Report) →
    Maybe (Acknowledgement.BatchEvidence (R.Report.selectedIds report)) → Effect
  writeStatus : R.Report → Effect
  -- Synchronize delivery status for the report. Actionable alerts enter the
  -- outbox where their remedy is known; this read cannot create failure mail.
  deliveryStatus : Effect

Reply : Effect → Set
Reply clock = Maybe ℕ
-- The acknowledgement records an attempt, not successful delivery.
Reply (reportProblem remedy) = ⊤
Reply (recordIncident report confirmation) = Text ⊎ ⊤
Reply (writeStatus report) = Text ⊎ ⊤
Reply deliveryStatus = Text ⊎ Text -- notification result field, not a replacement report

module E = Effects.Protocol Effect Reply
open E

blocked : Text → R.Report → R.Report
blocked reason report = record report { status = toList "blocked" ; blockReason = just reason }

afterLastWrite : R.Report → Text ⊎ ⊤ → Script R.Report
afterLastWrite report (inj₁ error) = ask (reportProblem (Host.restoreStateAccess error)) (λ _ → done report)
afterLastWrite report (inj₂ tt) = done report

afterNotification : R.Report → Text ⊎ Text → Script R.Report
afterNotification report (inj₁ error) = ask (reportProblem (Host.restoreMailAccess error)) λ _ →
  ask (writeStatus updated) (afterLastWrite updated)
  where updated = record report { notification = toList "unavailable" }
afterNotification report (inj₂ value) = ask (writeStatus updated) (afterLastWrite updated)
  where updated = record report { notification = value }

afterFirstWrite : R.Report → Text ⊎ ⊤ → Script R.Report
afterFirstWrite report (inj₁ error) = ask (reportProblem (Host.restoreStateAccess error)) λ _ →
  ask deliveryStatus (afterNotification report)
afterFirstWrite report (inj₂ tt) = ask deliveryStatus (afterNotification report)

afterIncident : R.Report → Text ⊎ ⊤ → Script R.Report
afterIncident report (inj₁ error) = ask (reportProblem (Host.restoreStateAccess error)) λ _ →
  ask (writeStatus report) (afterFirstWrite report)
afterIncident report (inj₂ tt) = ask (writeStatus report) (afterFirstWrite report)

incident : (report : R.Report) → Maybe (Acknowledgement.BatchEvidence (R.Report.selectedIds report)) → Script R.Report
incident report confirmation = ask (recordIncident report confirmation) (afterIncident report)

finish : (report : R.Report) → Maybe (Acknowledgement.BatchEvidence (R.Report.selectedIds report)) → Script R.Report
finish report confirmation = ask clock (λ observed → incident (R.stamp observed report) confirmation)

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

finalizationPreservesOutcome : ∀ report confirmation events result →
  Runs (finish report confirmation) events result → OutcomePreserved report result
finalizationPreservesOutcome report confirmation events result
  (replied _ _ observed (replied _ _ receipt rest)) =
  incidentPreserves (R.stamp observed report) receipt _ result rest
