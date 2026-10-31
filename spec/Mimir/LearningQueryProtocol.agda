{-# OPTIONS --safe #-}
-- Read protocols use a separate committed snapshot for each successful SELECT.
-- A transaction handle does not imply a repeatable snapshot at READ COMMITTED.
module Mimir.LearningQueryProtocol where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤?_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Mimir.Text using (Text; nonblank)
open import Relation.Nullary using (does)
import Mimir.Effects as Effects
import Mimir.LearningStore as Store
import Mimir.ReviewPreparationPublication as Publication
import Mimir.ReviewLedger as Ledger
import Mimir.ReviewObservation as Observation
import Mimir.ExperienceRead as Experiences
import Mimir.LearningHistory as History
import Mimir.LearningHistoryWire as RawHistory
import Mimir.AssessmentRead as Assessment
import Mimir.AssessmentSelection as Selection
import Mimir.LearningAssessmentQueries as AssessmentView
import Mimir.LearningRecompute as Recompute
import Mimir.LearningTargets as Targets
import Mimir.RevisionBounds as Bounds
import Mimir.Validation as Validation

data Request : Set where
  experience currentReview history : ℕ → Request
  pending : Maybe Text → ℕ → List ℕ → Request
  score : Selection.Query → Request
  assessmentHistory : Selection.Query → ℕ → ℕ → Request

data Statement : Set where
  currentOf reviewOf sourceVersions reviewVersions : ℕ → Statement
  pendingRows : Maybe Text → ℕ → List ℕ → Statement
  scoreTarget scoreRows : Selection.Query → Statement
  historicalScores : Selection.Query → ℕ → ℕ → Statement

data Effect : Set where
  beginRead : Effect
  readReviewHeader : ℕ → Effect
  readHistoryRows : RawHistory.Kind → ℕ → Effect
  select : Maybe ℕ → Statement → Effect
  dropTransaction : ℕ → Effect

Reply : Effect → Set
Reply beginRead = Text ⊎ ℕ
Reply (readReviewHeader _) = Text ⊎ Maybe RawHistory.Current
Reply (readHistoryRows _ _) = Text ⊎ List RawHistory.Entry
Reply (select handle statement) = Text ⊎ Store.World
Reply (dropTransaction tx) = ⊤

module E = Effects.Protocol Effect Reply
open E

data Result : Set where
  failed invalidRequest : Text → Result
  invalidTarget : Validation.Fault → Result
  experienceResult : Maybe Observation.Snapshot → Result
  reviewResult : Maybe History.CurrentReview → Result
  rawReviewResult : ℕ → Maybe RawHistory.Current → Result
  rawHistoryResult : List RawHistory.Entry → List RawHistory.Entry → Result
  historyResult : History.Result → Result
  pendingResult : Experiences.Result → Result
  scoreResult : Assessment.ScoreResult → Result
  assessmentHistoryResult : Assessment.HistoryResult → Result

close : Maybe ℕ → Result → Script Result
close nothing result = done result
close (just tx) result = ask (dropTransaction tx) (λ _ → done result)

read : Maybe ℕ → Statement → (Store.World → Script Result) → Script Result
read handle statement next = ask (select handle statement) receive
  where
  receive : Text ⊎ Store.World → Script Result
  receive (inj₁ failure) = close handle (failed failure)
  receive (inj₂ observed) = next observed

scoreAfterTarget : ℕ → Selection.Query → Store.World → Script Result
scoreAfterTarget tx q first with Targets.validate (Selection.Query.project q)
  (map Recompute.target (Recompute.beliefs (Publication.World.nodes (Store.World.publication first))))
  (Selection.Query.belief q ∷ [])
... | Validation.rejected failure refutation = close (just tx) (invalidTarget failure)
... | Validation.accepted valid = read (just tx) (scoreRows q) (λ second →
  close (just tx) (scoreResult (Assessment.assessed q (Assessment.scores q (AssessmentView.view second)))))

scoreAfterBegin : Selection.Query → Text ⊎ ℕ → Script Result
scoreAfterBegin q (inj₁ failure) = done (failed failure)
scoreAfterBegin q (inj₂ tx) = read (just tx) (scoreTarget q) (scoreAfterTarget tx q)

historyAfterSources : ℕ → Store.World → Store.World → Script Result
historyAfterSources id first second with History.reviewHistory id (Store.World.reviewTimes second)
  (Ledger.World.histories (Publication.World.ledger (Store.World.publication second)) id)
... | nothing = done (historyResult History.inconsistentHistory)
... | just reviews = done (historyResult (History.history
  (History.sourceHistory id (Store.World.sources first)) reviews))

start : Request → Script Result
start (experience id) = read nothing (currentOf id) (λ observed →
  done (experienceResult (Experiences.get id (Store.World.current observed))))
start (currentReview id) = ask (readReviewHeader id) λ where
  (inj₁ error) → done (failed error)
  (inj₂ current) → done (rawReviewResult id current)
start (history id) = ask (readHistoryRows RawHistory.sources id) λ where
  (inj₁ error) → done (failed error)
  (inj₂ sources) → ask (readHistoryRows RawHistory.reviews id) λ where
    (inj₁ error) → done (failed error)
    (inj₂ reviews) → done (rawHistoryResult sources reviews)
start (pending project limit excluded) with does (1 ≤? limit) ∧ does (limit ≤? 100)
... | false = done (pendingResult Experiences.invalidLimit)
... | true with does (length excluded ≤? 1000)
...   | false = done (pendingResult Experiences.tooManyExclusions)
...   | true = read nothing (pendingRows project limit excluded) (λ observed →
  done (pendingResult (Experiences.pendingExperiences project limit excluded (Store.World.current observed))))
start (score q) with nonblank (Selection.Query.project q) ∧
  nonblank (Selection.Query.scope q) ∧ nonblank (Selection.Query.rubric q)
... | false = done (scoreResult Assessment.missingScope)
... | true = ask beginRead (scoreAfterBegin q)
start (assessmentHistory q offset limit) with does (1 ≤? limit) ∧ does (limit ≤? 100) ∧ does (offset ≤? Bounds.i64Maximum)
... | false = done (assessmentHistoryResult Assessment.invalidPage)
... | true with nonblank (Selection.Query.project q)
...   | false = done (assessmentHistoryResult Assessment.missingProject)
...   | true = read nothing (historicalScores q offset limit) (λ observed →
  done (assessmentHistoryResult (AssessmentView.history q observed offset limit)))
