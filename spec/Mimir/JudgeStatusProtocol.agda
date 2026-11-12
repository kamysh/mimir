{-# OPTIONS --safe #-}
-- Read-only judge status/diagnostics commands. Both status and incident reads
-- occur even if the first fails. Listing diagnostics avoids the incident read;
-- selecting a trace still reads it even when an explicit ID was supplied.
module Mimir.JudgeStatusProtocol where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; reverse; map; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Mimir.UUIDGroups using (UUID; _≟UUID_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.String using (toList)
open import Relation.Nullary using (yes; no)
open import Mimir.Text using (Text)
import Mimir.JudgeStateRecords as Records
import Mimir.Effects as Effects

module R = Records.Over UUID

record Summary : Set where
  constructor summary
  field identity : UUID; status : Text; blockReason : Maybe Text
        startedAt : ℕ; finishedAt : Maybe ℕ; selectedIDs : List UUID

summarize : R.Trace → Summary
summarize trace = summary (R.Trace.identity trace) (R.Trace.status trace) (R.Trace.blockReason trace)
  (R.Trace.startedAt trace) (R.Trace.finishedAt trace) (R.Trace.selectedIds trace)

data Output : Set where
  invalidStatePath stateUnavailable : Output
  snapshot : Maybe R.Report → Maybe R.Incident → Output
  attempts : List Summary → Output
  traceOutput : Maybe R.Trace → Output

data Effect : Set where
  resolve readReport readIncident readDiagnostics : Effect
  stdout : Output → Effect

Reply : Effect → Set
Reply resolve = Bool
Reply readReport = Text ⊎ Maybe R.Report
Reply readIncident = Text ⊎ Maybe R.Incident
Reply readDiagnostics = Text ⊎ R.Diagnostics
Reply (stdout _) = ⊤
module P = Effects.Protocol Effect Reply
open P using (Script; done; ask)

emit : Output → ℕ → Script ℕ
emit output code = ask (stdout output) (λ _ → done code)

statusResult : Reply readReport → Reply readIncident → Script ℕ
statusResult (inj₂ report) (inj₂ savedIncident) = emit (snapshot report savedIncident) 0
statusResult _ _ = emit stateUnavailable 5

status : Script ℕ
status = ask resolve λ where
  false → emit invalidStatePath 2
  true → ask readReport (λ report → ask readIncident (statusResult report))

find : UUID → R.Diagnostics → Maybe R.Trace
find id [] = nothing
find id (trace ∷ rest) with R.Trace.identity trace ≟UUID id
... | yes _ = just trace
... | no _ = find id rest

latest : R.Diagnostics → Maybe R.Trace
latest traces with reverse traces
... | [] = nothing
... | last ∷ _ = just last

firstFailure : Maybe R.Incident → Maybe UUID
firstFailure nothing = nothing
firstFailure (just savedIncident) = R.Report.diagnosticsId (R.Incident.first savedIncident)

select : Maybe UUID → Maybe UUID → R.Diagnostics → Maybe R.Trace
select (just explicit) _ traces = find explicit traces
select nothing (just first) traces = find first traces
select nothing nothing traces = latest traces

afterDiagnostics : Bool → Maybe UUID → Reply readDiagnostics → Script ℕ
afterDiagnostics list id (inj₁ error) = emit stateUnavailable 5
afterDiagnostics true id (inj₂ traces) = emit (attempts (map summarize traces)) 0
afterDiagnostics false id (inj₂ traces) = ask readIncident λ where
  (inj₁ error) → emit stateUnavailable 5
  (inj₂ savedIncident) → emit (traceOutput (select id (firstFailure savedIncident) traces)) 0

diagnostics : Bool → Maybe UUID → Script ℕ
diagnostics list id = ask resolve λ where
  false → emit invalidStatePath 2
  true → ask readDiagnostics (afterDiagnostics list id)
