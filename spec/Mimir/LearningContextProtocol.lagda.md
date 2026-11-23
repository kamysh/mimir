# How Mimir retrieves learning context

An agent can ask Mimir for beliefs and procedures that may help with a
situation. The request names the project whose experience counts and lesson
assessments are relevant. The project must contain non-whitespace text. A
missing or blank project asks the caller to supply one.

The optional count applies separately to beliefs and procedures. Omitting
it returns all matches in each group. The reply also includes assessments
associated with the beliefs it returns.

The belief results follow the [belief search contract](RetrievalProtocol.lagda.md).
Its semantic availability report applies to the belief search. Procedure
matching uses text, so a provider failure can leave useful procedures and
lexical belief matches in the same reply.

```agda
{-# OPTIONS --safe #-}
module Mimir.LearningContextProtocol where

open import Data.Bool using (Bool; true; false; not)
open import Data.Bool.ListAction using (any)
open import Data.Float.Base using (Float; _<ᵇ_)
open import Data.List using (List; []; _∷_; map; filterᵇ; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≟_; _≤?_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Relation.Nullary using (does; yes; no)
open import Mimir.SourceReview using (_≟Text_)
open import Mimir.Text using (Text)
import Mimir.RetrievalRanking as R
import Mimir.RetrievalProtocol as Retrieval
import Mimir.LearningContext as Context
import Mimir.CandidateGraph as G
import Mimir.LearningStore as Store
import Mimir.CandidateProvenance as Provenance
import Mimir.AssessmentEvaluation as Evaluation
import Mimir.AssessmentScores as Scores

record Request : Set where
  constructor contextRequest
  field context project : Text; limit : Maybe ℕ; embeddingsEnabled : Bool

record PatternObservation : Set where
  constructor observedPattern
  field
    metadata : G.PatternValues
    successes failures unknown : ℕ
    estimate : Float
    provenance : Maybe Provenance.Provenance

record Output : Set where
  constructor output
  field beliefs : List G.BeliefValues; patterns : List PatternObservation; assessments : Context.Assessments
        semanticSearch : Retrieval.SemanticStatus

data State : Set where
  retrieving : Request → Retrieval.State → State
  patternResults : Request → Retrieval.Report G.BeliefValues → State
  assessmentGroups : Request → Retrieval.Report G.BeliefValues → List PatternObservation → State
  invalidInput invalidAssessment : State
  failed : Text → State
  finished : Output → State

Reply : State → Set
Reply (retrieving request phase) = Retrieval.Reply phase
Reply (patternResults request beliefs) = Text ⊎ List PatternObservation
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
```

## Select procedures by situation

Project procedures and untagged global procedures are eligible. Relevance
counts distinct whole terms shared by the context and the stored situation.
Punctuation separates terms, and case differences are ignored. For example,
“keyboard-layout” can match “Keyboard layout”. A procedure matching only
“board” has zero overlap with “keyboard” and is excluded.

More shared terms rank first. An observed outcome estimate breaks a tie.
Equal scores and estimates preserve the encounter order of the observed
rows. The count is applied after selection and ranking. UUIDs identify
records and carry no ranking information.

Outcome counts and estimates are inputs supplied by the store. They
describe recorded uses in the requested project, using the current
revision of each experience. An agent report is counted as an unknown
outcome. This module constrains how the reported values affect selection
and leaves their statistical computation to the existing store.

```agda

uniqueTerms : List Text → List Text
uniqueTerms [] = []
uniqueTerms (term ∷ rest) with any (λ other → does (term ≟Text other)) rest
... | true = uniqueTerms rest
... | false = term ∷ uniqueTerms rest

terms : R.Unicode → Text → List Text
terms unicode text = uniqueTerms
  (map (R.Unicode.lowercase unicode) (R.split (λ c → not (R.Unicode.alphanumeric unicode c)) text))

sharedTerms : List Text → List Text → ℕ
sharedTerms query situation =
  length (filterᵇ (λ term → any (λ other → does (term ≟Text other)) situation) query)

patternBefore : ℕ × PatternObservation → ℕ × PatternObservation → Bool
patternBefore (n , a) (m , b) with n ≟ m
... | yes _ = not (PatternObservation.estimate a <ᵇ PatternObservation.estimate b)
... | no _ = does (m ≤? n)

selectPatterns : R.Unicode → Request → List PatternObservation → List PatternObservation
selectPatterns unicode request candidates =
  map (λ { (_ , p) → p })
    (R.cap (Request.limit request) (R.sort patternBefore (filterᵇ eligible scored)))
  where
  situation = λ p → G.PatternValues.situation (PatternObservation.metadata p)
  scored = map (λ p → sharedTerms (terms unicode (Request.context request)) (terms unicode (situation p)) , p) candidates
  eligible : ℕ × PatternObservation → Bool
  eligible (zero , _) = false
  eligible (suc _ , p) = R.visible (just (Request.project request))
    (G.PatternValues.project (PatternObservation.metadata p))
```

## Associate assessments with the returned beliefs

The [assessment read](LearningContext.agda) selects active contributions
from the named project for the returned beliefs. It groups them by belief,
scope, and rubric. Groups follow the returned belief order, then scope
and rubric within each belief. The belief and procedure count imposes no
separate assessment count. The reply reports that those assessment groups
were returned in full.

The stages read observations from the store. Each read leaves the stored
state unchanged. Reading a procedure records no use or outcome. A failed
database read or an invalid stored assessment produces an error so it cannot
appear as a successful empty result.

[The dispatcher and its read-only proof](ApplicationProtocol.agda) compose
the stages. [The reply encoder](ApplicationOutput.agda) projects the typed
results. [The Rust service](../../crates/core/src/learning.rs) implements
selection and [the store](../../crates/core/src/store/learning.rs) reads the
underlying outcomes and assessments.

```agda
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

  finishAssessments : Request → Retrieval.Report G.BeliefValues → List PatternObservation → Context.Assessments → State
  finishAssessments request beliefs patterns assessmentValues with validAssessments (Context.Assessments.values assessmentValues)
  ... | false = invalidAssessment
  ... | true = finished (output (Retrieval.Report.beliefs beliefs) patterns assessmentValues
    (Retrieval.Report.semanticSearch beliefs))

  advance : (state : State) → Reply state → State
  advance (retrieving request phase) reply = afterRetrieval request (Retrieve.advance phase reply)
  advance (patternResults request beliefs) (inj₁ error) = failed error
  advance (patternResults request beliefs) (inj₂ patterns) =
    assessmentGroups request beliefs (selectPatterns unicode request patterns)
  advance (assessmentGroups request beliefs patterns) (inj₁ error) = failed error
  advance (assessmentGroups request beliefs patterns) (inj₂ observed) = finishAssessments request beliefs patterns
    (Context.assessmentPage textBefore (Request.project request)
      (map G.BeliefValues.identity (Retrieval.Report.beliefs beliefs)) observed)
  advance invalidInput reply = invalidInput
  advance invalidAssessment reply = invalidAssessment
  advance (failed error) reply = failed error
  advance (finished result) reply = finished result
```
