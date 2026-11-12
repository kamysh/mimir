{-# OPTIONS --safe #-}
-- Incident recording is an external operation. Its successful decision is
-- determined by the report and the evidence supplied by review readback.
module Mimir.JudgeStateOperations where

open import Data.Maybe using (Maybe)
open import Data.Product using (proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Mimir.Text using (Text)
import Mimir.JudgeAcknowledgement as Acknowledgement
import Mimir.JudgeIncident as Incident
import Mimir.JudgeStateRecords as Records
import Mimir.UUIDGroups as UUID

module R = Records.Over UUID.UUID
module I = Incident.Over UUID.UUID UUID._≟UUID_ Acknowledgement.BatchEvidence

data IncidentExecution (report : R.Report)
  (confirmation : Maybe (Acknowledgement.BatchEvidence (R.Report.selectedIds report))) : Text ⊎ ⊤ → Set where
  failed : ∀ detail → IncidentExecution report confirmation (inj₁ detail)
  applied : ∀ before after → after ≡ proj₁ (I.decide report before confirmation) →
    IncidentExecution report confirmation (inj₂ tt)
