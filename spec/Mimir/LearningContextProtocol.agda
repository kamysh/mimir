{-# OPTIONS --safe #-}
-- Concrete composition with the retrieval machine. One owned read-only
-- snapshot covers retrieval, procedure outcomes/provenance and assessments.
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
import Mimir.GraphRecords as Records
import Mimir.LearningStore as Store
import Mimir.ApplicationStore as App
import Mimir.ReviewPreparationPublication as Publication
import Mimir.PatternOutcomes as Patterns
import Mimir.CandidateProvenance as Provenance
import Mimir.AssessmentEvaluation as Evaluation
import Mimir.AssessmentScores as Scores

record Request : Set where
  constructor contextRequest
  field context project : Text; limit : R.Selection; embeddingsEnabled : Bool

record Output : Set where
  constructor output
  field beliefs : List G.BeliefValues; patterns : List Patterns.Result; assessments : Context.Assessments

data State : Set where
  opening : Request → State
  owned closing : ℕ → State → State
  retrieving : Request → Retrieval.State → State
  listPatterns : Request → List G.BeliefValues → State
  countPattern : Request → List G.BeliefValues → List G.PatternValues →
    List (ℕ × Patterns.Result) → ℕ → G.PatternValues → State
  patternOrigin : Request → List G.BeliefValues → List G.PatternValues →
    List (ℕ × Patterns.Result) → ℕ → Patterns.Result → State
  assessmentGroups : Request → List G.BeliefValues → List Patterns.Result → State
  invalidInput invalidAssessment : State
  failed : Text → State
  finished : Output → State

Reply : State → Set
Reply (opening request) = Text ⊎ ℕ
Reply (owned tx phase) = Reply phase
Reply (closing tx terminal) = ⊤
Reply (retrieving request phase) = Retrieval.Reply phase
Reply (listPatterns request beliefs) = Text ⊎ Store.World
Reply (countPattern request beliefs remaining ranked hits p) = Text ⊎ Store.World
Reply (patternOrigin request beliefs remaining ranked hits p) = Text ⊎ Store.World
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
  ... | true = opening request

  settle : ℕ → State → State
  settle tx phase@(finished _) = closing tx phase
  settle tx phase@(failed _) = closing tx phase
  settle tx invalidInput = closing tx invalidInput
  settle tx invalidAssessment = closing tx invalidAssessment
  settle tx phase = owned tx phase

  afterRetrieval : Request → Retrieval.State → State
  afterRetrieval request (Retrieval.finished beliefs) = listPatterns request beliefs
  afterRetrieval request (Retrieval.failed error) = failed error
  afterRetrieval request phase = retrieving request phase

  nextPattern : Request → List G.BeliefValues → List G.PatternValues → List (ℕ × Patterns.Result) → State
  nextPattern request beliefs [] ranked = assessmentGroups request beliefs (Context.rank (Request.limit request) ranked)
  nextPattern request beliefs (p ∷ remaining) ranked with Context.tokenOverlap unicode (Request.context request) p
  ... | zero = nextPattern request beliefs remaining ranked
  ... | suc hits = countPattern request beliefs remaining ranked (suc hits) p

  finishAssessments : Request → List G.BeliefValues → List Patterns.Result → Context.Assessments → State
  finishAssessments request beliefs patterns assessmentValues with validAssessments (Context.Assessments.values assessmentValues)
  ... | false = invalidAssessment
  ... | true = finished (output beliefs patterns assessmentValues)

  advance : (state : State) → Reply state → State
  advance (opening request) (inj₁ error) = failed error
  advance (opening request) (inj₂ tx) = owned tx (retrieving request (Retrieval.overlay (Retrieval.request
    (Request.context request) (Request.limit request) (just (Request.project request)) nothing
    (Request.embeddingsEnabled request))))
  advance (owned tx phase) reply = settle tx (advance phase reply)
  advance (closing tx terminal) reply = terminal
  advance (retrieving request phase) reply = afterRetrieval request (Retrieve.advance phase reply)
  advance (listPatterns request beliefs) (inj₁ error) = failed error
  advance (listPatterns request beliefs) (inj₂ observed) = nextPattern request beliefs
    (Records.listPatterns (just (Request.project request))
      (App.patterns (Publication.World.nodes (Store.World.publication observed)))) []
  advance (countPattern request beliefs remaining ranked hits p) (inj₁ error) = failed error
  advance (countPattern request beliefs remaining ranked hits p) (inj₂ observed) = patternOrigin request beliefs remaining ranked hits
    (Patterns.query (Request.project request) p observed)
  advance (patternOrigin request beliefs remaining ranked hits p) (inj₁ error) = failed error
  advance (patternOrigin request beliefs remaining ranked hits p) (inj₂ observed) = nextPattern request beliefs remaining
    (ranked ++ ((hits , record p { candidateProvenance = Provenance.get
      (G.PatternValues.identity (Patterns.Result.patternValue p)) observed }) ∷ []))
  advance (assessmentGroups request beliefs patterns) (inj₁ error) = failed error
  advance (assessmentGroups request beliefs patterns) (inj₂ observed) = finishAssessments request beliefs patterns
    (Context.assessmentPage textBefore (Request.project request) (map G.BeliefValues.identity beliefs) observed)
  advance invalidInput reply = invalidInput
  advance invalidAssessment reply = invalidAssessment
  advance (failed error) reply = failed error
  advance (finished result) reply = finished result
