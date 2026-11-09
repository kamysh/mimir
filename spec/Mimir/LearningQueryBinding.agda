{-# OPTIONS --safe #-}
-- Statement-snapshot bindings for learning read APIs. Current-review/history
-- use raw JSONB projections; typed state/assessment queries use decoded views.
-- History's two queries explicitly share a read-only stable snapshot. Raw JSONB
-- belongs to the same complete physical world, not a caller-chosen database.
module Mimir.LearningQueryBinding where

open import Data.Product using (Σ; _×_; _,_)
open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; trans)
import Mimir.ApplicationStore as Physical
import Mimir.LearningQueryProtocol as Query
import Mimir.LearningHistoryWire as Raw
import Mimir.DatabaseReadCommitted as Committed
open import Mimir.Text using (Text)
import Mimir.Recovery as Recovery
import Mimir.PublicEncoding as Encoding
import Mimir.StructuredValue as Wire
import Mimir.LearningStore as Learning
import Mimir.ExperienceRead as Experiences
import Mimir.RetrievalRanking as Ranking
import Mimir.AssessmentRead as Assessment
import Mimir.LearningAssessmentQueries as AssessmentView
import Mimir.AssessmentSelection as Selection
import Mimir.BeliefExplanation as Explanation

module Bind (typed : Committed.Contract Physical.World) where
  module T = Committed.Contract typed

  Reply : (effect : Query.Effect) → Query.Reply effect → Set
  Reply (Query.openScoreTarget q) (inj₁ error) = ⊤
  Reply (Query.openScoreTarget q) (inj₂ (tx , first)) = Σ T.Read (λ event → first ≡ T.snapshot event)
  Reply (Query.scoreSnapshotRows tx first q) (inj₁ error) = ⊤
  Reply (Query.scoreSnapshotRows tx first q) (inj₂ second) = Σ T.Read (λ event →
    T.snapshot event ≡ first × second ≡ T.snapshot event)
  Reply (Query.dropTransaction tx) value = ⊤
  Reply (Query.select tx statement) (inj₁ error) = ⊤
  Reply (Query.select tx statement) (inj₂ value) = Σ T.Read (λ event → value ≡ Physical.learningView (T.snapshot event))
  Reply (Query.readReviewHeader id) (inj₁ error) = ⊤
  Reply (Query.readReviewHeader id) (inj₂ value) = Σ T.Read (λ event →
    value ≡ Raw.readCurrent id (Physical.World.history (T.snapshot event)))
  Reply (Query.openHistory id) (inj₁ error) = ⊤
  Reply (Query.openHistory id) (inj₂ (tx , first , sources)) = Σ T.Read (λ event →
    first ≡ T.snapshot event × sources ≡ Raw.readHistory Raw.sources id (Physical.World.history first))
  Reply (Query.historySnapshotReviews tx first id) (inj₁ error) = ⊤
  Reply (Query.historySnapshotReviews tx first id) (inj₂ reviews) = Σ T.Read (λ event →
    T.snapshot event ≡ first × reviews ≡ Raw.readHistory Raw.reviews id (Physical.World.history (T.snapshot event)))

  historyReviewsUseSourceSnapshot : ∀ tx first id reviews →
    Reply (Query.historySnapshotReviews tx first id) (inj₂ reviews) →
    reviews ≡ Raw.readHistory Raw.reviews id (Physical.World.history first)
  historyReviewsUseSourceSnapshot tx first id reviews (event , stable , selected) =
    trans selected (cong (λ state → Raw.readHistory Raw.reviews id (Physical.World.history state)) stable)

  scoresUseValidatedTargetSnapshot : ∀ tx first q second →
    Reply (Query.scoreSnapshotRows tx first q) (inj₂ second) →
    Assessment.scores q (AssessmentView.view (Physical.learningView second)) ≡
    Assessment.scores q (AssessmentView.view (Physical.learningView first))
  scoresUseValidatedTargetSnapshot tx first q second (event , stable , selected) =
    cong (λ state → Assessment.scores q (AssessmentView.view (Physical.learningView state)))
      (trans selected stable)

module ExperienceReads (format : Encoding.Formatting) where
  module Encode = Encoding.Encode format

  data Request : Set where
    experience currentReview history : ℕ → Request
    pending : Maybe Text → Ranking.Selection → List ℕ → Request

  answer : Request → Physical.World → Wire.Value
  answer (experience id) state = Encoding.optional Encode.snapshot
    (Experiences.get id (Learning.World.current (Physical.learningView state)))
  answer (currentReview id) state = Encoding.optional (Encode.rawCurrent id)
    (Raw.readCurrent id (Physical.World.history state))
  answer (history id) state = Encoding.object
    (("experiences" , Wire.array (map Encode.rawHistoryEntry (Raw.readHistory Raw.sources id stored))) ∷
     ("reviews" , Wire.array (map Encode.rawHistoryEntry (Raw.readHistory Raw.reviews id stored))) ∷ [])
    where stored = Physical.World.history state
  answer (pending project count excluded) state = Wire.array (map Encode.snapshot
    (map Experiences.storedSnapshot (Ranking.cap count
      (Experiences.sort (Experiences.select project true excluded
        (Learning.World.current (Physical.learningView state)))))))

  module Checked = Recovery.ReadOnly answer

  operation : Recovery.Recoverable Physical.World Request
  operation = Checked.operation

  completeReplyAndUnchangedWorld : ∀ request initial interrupted final reply →
    Checked.Checked.X.Interrupted (Checked.Checked.script request) initial interrupted →
    Checked.Checked.X.Completed (Checked.Checked.script request) interrupted final reply →
    final ≡ initial × reply ≡ answer request initial
  completeReplyAndUnchangedWorld = Checked.completedRetryPreservesStateAndAnswer

-- Keep the complete existing semantic result until application projection.
-- Missing targets and malformed stored data cannot disappear as JSON null,
-- nor can a caller supply a desired answer or a successful-world certificate.
module AssessmentReads (format : Encoding.Formatting) where
  module Encode = Encoding.Encode format
  data Request : Set where
    scores : Selection.Query → Request
    history : Selection.Query → ℕ → Ranking.Selection → Request
    explanation : ℕ → ℕ → Ranking.Selection → Request

  data Answer : Set where
    scoreResult : Assessment.ScoreResult → Answer
    historyResult : Assessment.HistoryResult → Answer
    explanationResult : Explanation.Result → Answer

  answer : Request → Physical.World → Answer
  answer (scores selection) state = scoreResult
    (AssessmentView.scores selection (Physical.learningView state))
  answer (history selection offset limit) state = historyResult
    (AssessmentView.history selection (Physical.learningView state) offset limit)
  answer (explanation id offset limit) state = explanationResult
    (Explanation.get id offset limit (Physical.learningView state))

  -- Successful public projections share the application's exact encoders.
  -- An unsuccessful semantic answer remains in Answer; this projection is
  -- not its replacement and cannot be used as a completed-work witness.
  successfulWire : Answer → Maybe Wire.Value
  successfulWire (scoreResult (Assessment.assessed selection evaluated)) with Encode.evaluation evaluated
  ... | nothing = nothing
  ... | just encodedScores = just (Encode.assessmentResult selection encodedScores)
  successfulWire (historyResult (Assessment.found page)) = just (Encode.assessmentPage page)
  successfulWire (explanationResult (Explanation.explained value)) = just (Encode.explanation value)
  successfulWire _ = nothing

  module Checked = Recovery.ReadOnly answer

  operation : Recovery.Recoverable Physical.World Request
  operation = Checked.operation

  completeReplyAndUnchangedWorld : ∀ request initial interrupted final reply →
    Checked.Checked.X.Interrupted (Checked.Checked.script request) initial interrupted →
    Checked.Checked.X.Completed (Checked.Checked.script request) interrupted final reply →
    final ≡ initial × reply ≡ answer request initial
  completeReplyAndUnchangedWorld = Checked.completedRetryPreservesStateAndAnswer
