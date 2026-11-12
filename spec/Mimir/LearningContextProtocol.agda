{-# OPTIONS --safe #-}
-- Learning context combines retrieved beliefs, externally supplied pattern
-- results, and assessment results. Pattern statistics are outside this model.
module Mimir.LearningContextProtocol where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; map; filterᵇ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Mimir.Text using (Text)
import Mimir.RetrievalRanking as R
import Mimir.RetrievalProtocol as Retrieval
import Mimir.LearningContext as Context
import Mimir.CandidateGraph as G
import Mimir.LearningStore as Store
import Mimir.StructuredValue as V
import Mimir.AssessmentEvaluation as Evaluation
import Mimir.AssessmentScores as Scores

record Request : Set where
  constructor contextRequest
  field context project : Text; limit : Maybe ℕ; embeddingsEnabled : Bool

record Output : Set where
  constructor output
  field beliefs : List G.BeliefValues; patterns : List V.Value; assessments : Context.Assessments

data State : Set where
  retrieving : Request → Retrieval.State → State
  patternResults : Request → List G.BeliefValues → State
  assessmentGroups : Request → List G.BeliefValues → List V.Value → State
  invalidInput invalidAssessment : State
  failed : Text → State
  finished : Output → State

Reply : State → Set
Reply (retrieving request phase) = Retrieval.Reply phase
Reply (patternResults request beliefs) = Text ⊎ List V.Value
Reply (assessmentGroups request beliefs patterns) = Text ⊎ Store.World
Reply invalidInput = ⊤
Reply invalidAssessment = ⊤
Reply (failed error) = ⊤
Reply (finished result) = ⊤

validAssessments : List (Context.Key × Evaluation.Result) → Bool
validAssessments [] = true
validAssessments ((_ , Evaluation.invalidStoredNumber) ∷ rest) = false
validAssessments ((_ , Evaluation.scored (Scores.rejected why)) ∷ rest) = false
validAssessments ((_ , Evaluation.scored (Scores.accepted acceptedScores)) ∷ rest) = validAssessments rest

module Run (ops : R.F32) (unicode : R.Unicode) (textBefore : Text → Text → Bool) where
  module Retrieve = Retrieval.Run ops unicode

  begin : Request → State
  begin request with Context.admitted (Request.project request) (Request.limit request)
  ... | false = invalidInput
  ... | true = retrieving request (Retrieval.overlay (Retrieval.request
    (Request.context request) (Request.limit request) (just (Request.project request)) nothing
    (Request.embeddingsEnabled request)))

  afterRetrieval : Request → Retrieval.State → State
  afterRetrieval request (Retrieval.finished beliefs) = patternResults request beliefs
  afterRetrieval request (Retrieval.failed error) = failed error
  afterRetrieval request phase = retrieving request phase

  finishAssessments : Request → List G.BeliefValues → List V.Value → Context.Assessments → State
  finishAssessments request beliefs patterns assessmentValues with validAssessments (Context.Assessments.values assessmentValues)
  ... | false = invalidAssessment
  ... | true = finished (output beliefs patterns assessmentValues)

  advance : (state : State) → Reply state → State
  advance (retrieving request phase) reply = afterRetrieval request (Retrieve.advance phase reply)
  advance (patternResults request beliefs) (inj₁ error) = failed error
  advance (patternResults request beliefs) (inj₂ patterns) = assessmentGroups request beliefs patterns
  advance (assessmentGroups request beliefs patterns) (inj₁ error) = failed error
  advance (assessmentGroups request beliefs patterns) (inj₂ observed) = finishAssessments request beliefs patterns
    (Context.assessmentPage textBefore (Request.project request) (map G.BeliefValues.identity beliefs) observed)
  advance invalidInput reply = invalidInput
  advance invalidAssessment reply = invalidAssessment
  advance (failed error) reply = failed error
  advance (finished result) reply = finished result
