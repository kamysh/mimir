{-# OPTIONS --safe #-}
-- Judge-to-notifier translation. Only explicitly selected report facts enter
-- mail; raw input excerpts, backend replies and failure details are excluded.
module Mimir.JudgeNotification where

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.List using (List; []; _∷_; _++_; map; length; filterᵇ)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_; _∸_)
import Data.Nat.Show as Nat
open import Data.String using (toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
import Mimir.JudgeFinalization as Finalization
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.DiagnosticText as Labels
import Mimir.OperationalDiagnostics as Diagnostics
import Mimir.NotificationConfig as Config
import Mimir.NotificationIncident as I
import Mimir.NotificationDelivery as Delivery
import Mimir.NotificationRuntime as N
import Mimir.JudgeStateRecords as Records
import Mimir.PublicEncoding as Encoding
import Mimir.Validation as V
import Mimir.UnixPath as Path
import Mimir.Effects as Effects

module R = Records.Over ℕ
number : ℕ → Text
number value = toList (Nat.show value)

reason : R.Report → Text
reason report with R.Report.blockReason report
... | nothing = toList "review incomplete"
... | just value = choose value
  where
  choose : Text → Text
  choose value with does (value ≟Text toList "model_budget_exhausted")
  ... | true = toList "model call limit reached"
  ... | false with does (value ≟Text toList "tool_budget_exhausted")
  ...   | true = toList "tool call limit reached"
  ...   | false with does (value ≟Text toList "backend_timeout")
  ...     | true = toList "model response timed out"
  ...     | false with does (value ≟Text toList "backend_error")
  ...       | true = toList "model backend failed"
  ...       | false with does (value ≟Text toList "review_deferred")
  ...         | true = toList "review deferred after a rejected candidate"
  ...         | false = toList "review incomplete (" ++ Labels.strip value ++ toList ")"

join : Text → List Text → Text
join separator [] = []
join separator (x ∷ []) = x
join separator (x ∷ y ∷ rest) = x ++ separator ++ join separator (y ∷ rest)

projectName : Maybe Text → Text
projectName nothing = toList "all projects"
projectName (just project) = Labels.strip project

-- Every ordinary character in a project label survives, regardless of length.
projectLabelPreserved : ∀ project → All Labels.NonControl project →
  projectName (just project) ≡ project
projectLabelPreserved = Labels.stripIdentity
incidentKey : Maybe Text → Text
incidentKey nothing = toList "all-projects"
incidentKey (just project) = project

status : R.Report → I.Status
status report with does (R.Report.status report ≟Text toList "blocked") ∨
  does (R.Report.status report ≟Text toList "partial")
... | true = I.failure (toList "judge_failure") (toList "Review batch did not complete: " ++ reason report)
... | false with does (R.Report.status report ≟Text toList "idle")
...   | true = I.recovery
...   | false = I.progress

module Details (format : Encoding.Formatting) (localTime : ℕ → Text) where
  -- localTime uses chrono's local zone and "%Y-%m-%d %H:%M:%S %:z";
  -- unrepresentable u64 timestamps use "Unix time <seconds>".
  uuid = Encoding.Formatting.uuidText format
  ids : List ℕ → Text
  ids [] = toList "none"
  ids values@(_ ∷ _) = join (toList ", ") (map uuid values)

  diagnostic : Maybe ℕ → Text
  diagnostic nothing = toList "\nDiagnostic ID: unavailable; inspect mimir judge status"
  diagnostic (just id) = toList "\nDiagnostic ID: " ++ uuid id ++
    toList "\nInspect: mimir judge diagnostics --id " ++ uuid id

  failure : Maybe Text → R.Report → Text
  failure project report = toList "Project: " ++ projectName project ++
    toList "\nObserved: " ++ localTime (R.Report.recordedAt report) ++ toList "\nReason: " ++ reason report ++
    toList "\nSelected: " ++ number (R.Report.selected report) ++ toList "; confirmed: " ++ number (R.Report.confirmed report) ++
    toList "; corrected: " ++ number (R.Report.corrected report) ++ toList "; pending: " ++ number (R.Report.pending report) ++
    toList "; unavailable: " ++ number (R.Report.unavailable report) ++ toList "\nAffected experience IDs: " ++
    ids (R.Report.selectedIds report) ++ diagnostic (R.Report.diagnosticsId report) ++
    toList "\n" ++ Diagnostics.summary (just report)

  find : ℕ → List R.Confirmed → Maybe R.Confirmed
  find id [] = nothing
  find id (item ∷ rest) with id ≟ R.Confirmed.identity item
  ... | yes _ = just item
  ... | no _ = find id rest

  confirmed : List R.Confirmed → ℕ → Bool
  confirmed values id with find id values
  ... | nothing = false
  ... | just _ = true

  itemLine : List R.Confirmed → ℕ → Text
  itemLine values id with find id values
  ... | nothing = toList "\n" ++ uuid id ++ toList ": completion unverified"
  ... | just item = toList "\n" ++ uuid id ++ toList ": confirmed at " ++ localTime (R.Confirmed.recordedAt item)

  previousDiagnostic : Maybe ℕ → Text
  previousDiagnostic nothing = []
  previousDiagnostic (just id) = toList "\nPrevious diagnostic ID: " ++ uuid id

  recovery : Maybe Text → R.Report → R.Incident → Text
  recovery project report savedIncident = toList "Project: " ++ projectName project ++
    toList "\nPrevious failure: " ++ localTime (R.Report.recordedAt first) ++
    toList "\nPrevious reason: " ++ reason first ++ toList "\nQueue: idle at " ++ localTime (R.Report.recordedAt report) ++
    toList "; no pending reviews were selected\nAffected reviews: " ++ number count ++
    toList " confirmed by completed batches; " ++ number (length selected ∸ count) ++ toList " unverified" ++
    previousDiagnostic (R.Report.diagnosticsId first) ++ join [] (map (itemLine reviews) selected)
    where
    first = R.Incident.first savedIncident
    selected = R.Report.selectedIds first
    reviews = R.Incident.confirmedReviews savedIncident
    count = length (filterᵇ (confirmed reviews) selected)

outcomeText : I.Outcome → Text
outcomeText I.disabled = toList "disabled"
outcomeText I.notNeeded = toList "not_needed"
outcomeText I.sent = toList "sent"
outcomeText I.retryPending = toList "retry_pending"
outcomeText I.exhausted = toList "exhausted"
outcomeText I.authRequired = toList "auth_required"
outcomeText I.unavailable = toList "unavailable"

data Effect : Set where readFailure : Effect; enqueue : I.Event → Effect
Reply : Effect → Set
Reply readFailure = Text ⊎ Maybe R.Incident
Reply (enqueue _) = Text ⊎ ⊤
open Effects.Protocol Effect Reply public

module Run (format : Encoding.Formatting) (localTime : ℕ → Text)
  (cfg : Config.Config) (path : Path.Path) (project : Maybe Text) where
  module D = Details format localTime

  submitDetails : Finalization.NotificationMode → R.Report → Maybe Text → Script (Text ⊎ Text)
  submitDetails mode report details =
    ask (enqueue (I.event (toList "judge") (incidentKey project) (status report) details)) λ where
      (inj₁ error) → done (inj₁ error)
      (inj₂ tt) → done (inj₂ (toList "queued"))

  notifyWith : Finalization.NotificationMode → R.Report → Script (Text ⊎ Text)
  notifyWith mode report with V.result (Config.validate cfg) | Path.absolute path
  ... | inj₁ _ | _ = done (inj₁ (toList "invalid notification configuration"))
  ... | _ | false = done (inj₁ (toList "notification state path must be absolute"))
  ... | inj₂ _ | true with status report
  ...   | I.failure _ _ = submitDetails mode report (just (D.failure project report))
  ...   | I.progress = submitDetails mode report nothing
  ...   | I.recovery = ask readFailure λ where
    (inj₁ error) → done (inj₁ error)
    (inj₂ nothing) → submitDetails mode report nothing
    (inj₂ (just savedIncident)) → submitDetails mode report (just (D.recovery project report savedIncident))

  notify : R.Report → Script (Text ⊎ Text)
  notify report with Config.Config.enabled cfg
  ... | false = done (inj₂ (toList "disabled"))
  ... | true = notifyWith Finalization.standaloneDelivery report

  queue : R.Report → Script (Text ⊎ Text)
  queue report with Config.Config.enabled cfg
  ... | false = done (inj₂ (toList "disabled"))
  ... | true = notifyWith Finalization.queuedDelivery report
