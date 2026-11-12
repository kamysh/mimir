{-# OPTIONS --safe #-}
-- CLI/watch policy around the existing review controller. Model claims are
-- never accepted as reports here: the runner/receipt composition produces the
-- report, then this module derives process status and watch behavior from it.
module Mimir.JudgeHost where

open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≟_; _≤?_; _⊔_; _⊓_)
open import Data.String using (toList)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Relation.Nullary using (does; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.Judge as Judge
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

record Outcome : Set where
  constructor outcome
  field exit : Exit; degraded idle : Bool

is : Text → Text → Bool
is actual expected = does (actual ≟Text expected)

isDeferred : State.Report → Bool
isDeferred report with State.Report.blockReason report
... | nothing = false
... | just reason = is reason (toList "review_deferred")

reportExit : State.Report → Exit
reportExit report with is status (toList "idle") ∨ is status (toList "complete")
  where status = State.Report.status report
... | true = success
... | false with is (State.Report.status report) (toList "partial") ∨ is (State.Report.status report) (toList "blocked")
...   | true = incomplete
...   | false = unavailable

outcomeOf : Bool → State.Report → Outcome
outcomeOf watch report = outcome exit degraded (is status (toList "idle"))
  where
  status = State.Report.status report
  degraded = is status (toList "blocked") ∨ is status (toList "partial")
  exit : Exit
  exit with watch ∧ isDeferred report
  ... | true = success
  ... | false = reportExit report
