{-# OPTIONS --safe #-}
-- Concrete composition with the retrieval machine. One owned read-only
-- snapshot covers retrieval, procedure outcomes/provenance and assessments.
module Mimir.LearningContextProtocol where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; map; filterᵇ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
import Data.List.Relation.Unary.All as Every
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
import Mimir.Recovery as Recovery
import Mimir.RetrievalReadContract as Reads

record Request : Set where
  constructor contextRequest
  field context project : Text; limit : R.Selection; embeddingsEnabled : Bool

record Output : Set where
  constructor output
  field beliefs : List G.BeliefValues; patterns : List Patterns.Result; assessments : Context.Assessments

validAssessments : List (Context.Key × Evaluation.Result) → Bool
validAssessments [] = true
validAssessments ((_ , Evaluation.invalidStoredNumber) ∷ rest) = false
validAssessments ((_ , Evaluation.scored (Scores.rejected why)) ∷ rest) = false
validAssessments ((_ , Evaluation.scored (Scores.accepted acceptedScores)) ∷ rest) = validAssessments rest

-- This is the response tail AFTER retrieval has selected identities. It is
-- deliberately not the public learning-context operation: the independent
-- retrieval proof must still justify those identities before dispatch.
-- No desired belief rows, procedure counts or assessment answers are inputs.
module Assembly (unicode : R.Unicode) (textBefore : Text → Text → Bool) where
  record Input : Set where
    constructor selected
    field request : Request; beliefIDs : List ℕ

  selectedBeliefs : Input → App.World → List G.BeliefValues
  selectedBeliefs input state = R.materialize (Input.beliefIDs input)
    (filterᵇ (R.eligible (just (Request.project request)) (Reads.retired state)) (App.beliefs state))
    where request = Input.request input

  matchingRows : Text → Text → Store.World → List G.PatternValues → List (ℕ × Patterns.Result)
  matchingRows query project state [] = []
  matchingRows query project state (procedure ∷ rest) with Context.tokenOverlap unicode query procedure
  ... | zero = matchingRows query project state rest
  ... | suc hits = (suc hits , Patterns.query project procedure state) ∷ matchingRows query project state rest

  procedures : Input → App.World → List Patterns.Result
  procedures input state = Context.rank (Request.limit request)
    (matchingRows (Request.context request) (Request.project request) (App.learningView state)
      (Records.listPatterns (just (Request.project request)) (App.patterns (App.nodes state))))
    where request = Input.request input

  assemble : Input → App.World → Output
  assemble input state = output beliefs (procedures input state)
    (Context.assessmentPage textBefore (Request.project (Input.request input))
      (map G.BeliefValues.identity beliefs) (App.learningView state))
    where beliefs = selectedBeliefs input state

  data Result : Set where
    response : Output → Result
    invalidAssessment : Result

  -- The existing protocol rejects corrupt stored assessment values. Keeping
  -- this branch prevents a read proof from relabelling them as a valid reply.
  answer : Input → App.World → Result
  answer input state with validAssessments (Context.Assessments.values (Output.assessments (assemble input state)))
  ... | false = invalidAssessment
  ... | true = response (assemble input state)

  module Checked = Recovery.ReadOnly answer

  operation : Recovery.Recoverable App.World Input
  operation = Checked.operation

  completeReplyAndUnchangedWorld : ∀ input initial interrupted final reply →
    Checked.Checked.X.Interrupted (Checked.Checked.script input) initial interrupted →
    Checked.Checked.X.Completed (Checked.Checked.script input) interrupted final reply →
    final ≡ initial × reply ≡ answer input initial
  completeReplyAndUnchangedWorld = Checked.completedRetryPreservesStateAndAnswer

  noProcedureQuota : ∀ query project state procedures →
    Context.rank nothing (matchingRows query project state procedures) ≡
      map (λ { (_ , value) → value })
        (R.sort Context.before (matchingRows query project state procedures))
  noProcedureQuota query project state procedures = refl

  assessmentsComeFromSelectedBeliefs : ∀ input state →
    Output.assessments (assemble input state) ≡ Context.assessmentPage textBefore
      (Request.project (Input.request input))
      (map G.BeliefValues.identity (selectedBeliefs input state)) (App.learningView state)
  assessmentsComeFromSelectedBeliefs input state = refl

  noAssessmentTruncation : ∀ input state →
    Context.Assessments.truncated (Output.assessments (assemble input state)) ≡ false
  noAssessmentTruncation input state = refl

  invalidAssessmentsAreNotResponses : ∀ input state →
    validAssessments (Context.Assessments.values (Output.assessments (assemble input state))) ≡ false →
    answer input state ≡ invalidAssessment
  invalidAssessmentsAreNotResponses input state rejected rewrite rejected = refl

  -- Ranking and an explicit caller selection may reorder or omit procedures;
  -- neither may replace their counts or provenance with another snapshot.
  private
    insertKeeps : ∀ {A : Set} {P : A → Set} before x xs →
      P x → Every.All P xs → Every.All P (R.insert before x xs)
    insertKeeps before x [] proof Every.[] = proof Every.∷ Every.[]
    insertKeeps before x (y ∷ ys) proof (first Every.∷ rest) with before x y
    ... | true = proof Every.∷ first Every.∷ rest
    ... | false = first Every.∷ insertKeeps before x ys proof rest

    sortKeeps : ∀ {A : Set} {P : A → Set} before xs →
      Every.All P xs → Every.All P (R.sort before xs)
    sortKeeps before [] Every.[] = Every.[]
    sortKeeps before (x ∷ xs) (first Every.∷ rest) =
      insertKeeps before x (R.sort before xs) first (sortKeeps before xs rest)

    takeKeeps : ∀ {A : Set} {P : A → Set} count xs →
      Every.All P xs → Every.All P (Data.List.take count xs)
    takeKeeps zero xs proof = Every.[]
    takeKeeps (suc count) [] Every.[] = Every.[]
    takeKeeps (suc count) (x ∷ xs) (first Every.∷ rest) =
      first Every.∷ takeKeeps count xs rest

    selectionKeeps : ∀ {A : Set} {P : A → Set} limit xs →
      Every.All P xs → Every.All P (R.cap limit xs)
    selectionKeeps nothing xs proof = proof
    selectionKeeps (just count) xs proof = takeKeeps (R.PositiveCount.count count) xs proof

  fromSnapshot : Text → Store.World → Patterns.Result → Set
  fromSnapshot project state observed = observed ≡ Patterns.query project (Patterns.Result.patternValue observed) state

  matchingRowsUseCurrentSnapshot : ∀ query project state procedures →
    Every.All (λ { (_ , observed) → fromSnapshot project state observed })
      (matchingRows query project state procedures)
  matchingRowsUseCurrentSnapshot query project state [] = Every.[]
  matchingRowsUseCurrentSnapshot query project state (procedure ∷ rest)
    with Context.tokenOverlap unicode query procedure
  ... | zero = matchingRowsUseCurrentSnapshot query project state rest
  ... | suc hits = refl Every.∷ matchingRowsUseCurrentSnapshot query project state rest

  private
    extractKeeps : ∀ project state (rows : List (ℕ × Patterns.Result)) →
      Every.All (λ { (_ , observed) → fromSnapshot project state observed }) rows →
      Every.All (fromSnapshot project state) (map (λ { (_ , observed) → observed }) rows)
    extractKeeps project state [] Every.[] = Every.[]
    extractKeeps project state ((_ , value) ∷ rows) (first Every.∷ rest) =
      first Every.∷ extractKeeps project state rows rest

  selectedProceduresUseCurrentSnapshot : ∀ input state →
    Every.All (fromSnapshot (Request.project (Input.request input)) (App.learningView state))
      (Output.patterns (assemble input state))
  selectedProceduresUseCurrentSnapshot input state = extractKeeps project current _
    (selectionKeeps (Request.limit request) _
      (sortKeeps Context.before _ (matchingRowsUseCurrentSnapshot query project current storedProcedures)))
    where
    request = Input.request input
    project = Request.project request
    query = Request.context request
    current = App.learningView state
    storedProcedures = Records.listPatterns (just project) (App.patterns (App.nodes state))

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
