{-# OPTIONS --safe #-}
-- Public diagnostics use classified causes and bounded counts, never raw model
-- text, source excerpts, configuration credentials or arbitrary error strings.
module Mimir.OperationalDiagnostics where
open import Data.Bool using (Bool; true; false)
open import Data.List using ([]; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Nat.Show using (show)
open import Data.String using (toList)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.JudgeStateRecords as Records
import Mimir.SourceFailure as Source
module R = Records.Over ℕ

cause : Maybe Text → Text
cause nothing = toList "No failure recorded."
cause (just code) with does (code ≟Text toList "quotation_mismatch")
... | true = toList "The proposed review contained a quotation that does not occur literally in its cited source."
... | false with does (code ≟Text toList "invalid_config")
...   | true = toList "The configuration is incompatible or incomplete; no review can start."
...   | false with does (code ≟Text toList "backend_timeout")
...     | true = toList "The model did not finish within the configured batch deadline."
...     | false with does (code ≟Text toList "model_budget_exhausted")
...       | true = toList "The model used the configured request budget before completing the review."
...       | false with does (code ≟Text toList "tool_error")
...         | true = toList "A database or tool operation failed; its outcome must be read back."
...         | false with does (code ≟Text toList "review_deferred")
...           | true = toList "The review was deferred after incompatible candidate declarations."
...           | false = toList "The batch could not complete. Inspect the local diagnostic report for the exact failure."

classify : Maybe Source.Failure → Maybe Text → Maybe Text
classify nothing reason = reason
classify (just source) reason with does (Source.Failure.stage source ≟Text toList "quotation_mismatch")
... | true = just (toList "quotation_mismatch")
... | false = reason

classified : R.Report → Maybe Text
classified report = classify (R.Report.failureSource report) (R.Report.blockReason report)

advice : Maybe Text → Text
advice nothing = toList "No repair is indicated by this snapshot."
advice (just value) with does (value ≟Text toList "invalid_config")
... | true = toList "Run mimir config check. If required settings are missing, run mimir config upgrade --log-directory /absolute/path/to/logs, then check again."
... | false = toList "Run mimir judge diagnose on this computer. It shows the cause, affected work and private diagnostic location. If failures persist, attach its summary summary to a Mimir issue."

summary : Maybe R.Report → Text
summary nothing = toList "No local run report is available. Run mimir judge diagnose on this computer.\n"
summary (just report) = toList "Cause: " ++ cause (classified report) ++
  toList "\nBatch impact: " ++ toList (show (R.Report.confirmed report)) ++ toList " confirmed; " ++
  toList (show (R.Report.pending report)) ++ toList " pending; " ++ toList (show (R.Report.unavailable report)) ++
  toList " unavailable.\nNext action: " ++ advice (classified report) ++ toList "\n"

-- Changing private failure text cannot change the summary explanation.
privateDetailExcluded : ∀ report detail → summary (just (record report { failureDetail = detail })) ≡ summary (just report)
privateDetailExcluded report detail = refl
