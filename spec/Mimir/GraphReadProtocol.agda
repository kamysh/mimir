{-# OPTIONS --safe #-}
-- Composite reads use an explicit read-only stable transaction. Paging,
-- statistics and explanations retain their original response snapshot.
module Mimir.GraphReadProtocol where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_; length; filterᵇ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤?_; _≟_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.ApplicationStore as Store
import Mimir.LearningStore as Learning
import Mimir.ReviewPreparationPublication as Publication
import Mimir.CandidateGraph as G
import Mimir.LearningCandidates as C
import Mimir.GraphRecords as Records
import Mimir.RetrievalRanking as Ranking
import Mimir.BeliefExplanation as Explanation
import Mimir.CandidateProvenance as Candidate
import Mimir.IndependentProvenance as Origin
import Mimir.ReviewEdges as Edges
import Mimir.ReviewSchema as R
import Mimir.Effects as Effects

data Request : Set where
  getBelief getPattern : ℕ → Request
  listBeliefs : Maybe Text → Maybe C.Memory → Request
  listPatterns : Maybe Text → Request
  beliefPage : Maybe Text → Maybe C.Memory → ℕ → ℕ → Request -- limit, offset
  explain : ℕ → ℕ → Ranking.Selection → Request -- id, offset, optional positive selection
  stats : Request

data Statement : Set where
  belief patternNode incoming reviews candidate independent : ℕ → Statement
  beliefs countBeliefs : Maybe Text → Maybe C.Memory → Statement
  patterns : Maybe Text → Statement
  countPatterns : Statement
  countEdges : R.Relation → Statement

data Effect : Set where
  openExplanation : ℕ → Effect
  explanationSnapshot : ℕ → Store.World → Statement → Effect
  openPage : Maybe Text → Maybe C.Memory → Effect
  pageSnapshotRows : ℕ → Store.World → Maybe Text → Maybe C.Memory → ℕ → ℕ → Effect
  openStatistics : Effect
  statisticsSnapshot : ℕ → Store.World → Statement → Effect
  select : Maybe ℕ → Statement → Effect
  dropTransaction : ℕ → Effect

Reply : Effect → Set
Reply (openExplanation _) = Text ⊎ (ℕ × Store.World)
Reply (explanationSnapshot _ _ _) = Text ⊎ Store.World
Reply (openPage project memory) = Text ⊎ (ℕ × Store.World)
Reply (pageSnapshotRows tx initial project memory limit offset) = Text ⊎ Store.World
Reply openStatistics = Text ⊎ (ℕ × Store.World)
Reply (statisticsSnapshot tx initial statement) = Text ⊎ Store.World
Reply (select handle statement) = Text ⊎ Store.World
Reply (dropTransaction tx) = ⊤

module E = Effects.Protocol Effect Reply
open E

pageAnswer : Maybe Text → Maybe C.Memory → ℕ → ℕ → Store.World → Records.Page
pageAnswer project memory limit offset snapshot = Records.pageResult project memory limit offset
  (length (Records.listBeliefs project memory (Store.beliefs snapshot))) (Store.beliefs snapshot)

-- The same count/row semantics, with the database's stable-read guarantee
-- supplied at its boundary. No caller-supplied answer or readiness predicate.
pageUsesCountSnapshot : ∀ project memory limit offset first second → second ≡ first →
  Records.pageResult project memory limit offset
    (length (Records.listBeliefs project memory (Store.beliefs first))) (Store.beliefs second) ≡
  pageAnswer project memory limit offset first
pageUsesCountSnapshot project memory limit offset first .first refl = refl

record Statistics : Set where
  constructor statistics
  field beliefCount patternCount supportCount defeatCount causeCount contradictionCount : ℕ

data Result : Set where
  failed : Text → Result
  invalidPage missingBelief invalidProvenance : Result
  beliefResult : Maybe G.BeliefValues → Result
  patternResult : Maybe G.PatternValues → Result
  beliefList : List G.BeliefValues → Result
  patternList : List G.PatternValues → Result
  paged : Records.Page → Result
  explained : Explanation.Explanation → Result
  counted : Statistics → Result

close : Maybe ℕ → Result → Script Result
close nothing result = done result
close (just tx) result = ask (dropTransaction tx) (λ _ → done result)

read : Maybe ℕ → Statement → (Store.World → Script Result) → Script Result
read handle statement next = ask (select handle statement) (λ
  { (inj₁ error) → close handle (failed error)
  ; (inj₂ observed) → next observed })

countRelation : R.Relation → Store.World → ℕ
countRelation relation w = length (filterᵇ (λ e → does (R.relationCode relation ≟ R.relationCode (Edges.Edge.relation e)))
  (Publication.World.edges (Learning.World.publication (Store.World.learning w))))

statisticsFromViews : Store.World → Store.World → Store.World → Store.World → Store.World → Store.World → Statistics
statisticsFromViews beliefView patternView supportView defeatView causeView contradictionView = statistics
  (length (Store.beliefs beliefView)) (length (Store.patterns (Store.nodes patternView)))
  (countRelation R.supports supportView) (countRelation R.defeats defeatView)
  (countRelation R.causes causeView) (countRelation R.contradicts contradictionView)

statisticsAnswer : Store.World → Statistics
statisticsAnswer snapshot = statisticsFromViews snapshot snapshot snapshot snapshot snapshot snapshot

statisticsViewsAgree : ∀ first patternView supportView defeatView causeView contradictionView →
  patternView ≡ first → supportView ≡ first → defeatView ≡ first → causeView ≡ first → contradictionView ≡ first →
  statisticsFromViews first patternView supportView defeatView causeView contradictionView ≡ statisticsAnswer first
statisticsViewsAgree first .first .first .first .first .first refl refl refl refl refl = refl

statisticsRead : ℕ → Store.World → Statement → (Store.World → Script Result) → Script Result
statisticsRead tx first statement next = ask (statisticsSnapshot tx first statement) λ where
  (inj₁ error) → close (just tx) (failed error)
  (inj₂ observed) → next observed

fromExplanation : Explanation.Result → Result
fromExplanation Explanation.beliefMissing = missingBelief
fromExplanation Explanation.invalidStoredProvenance = invalidProvenance
fromExplanation (Explanation.explained value) = explained value

explanationAnswer : ℕ → ℕ → Ranking.Selection → Store.World → Result
explanationAnswer id offset limit state = fromExplanation (Explanation.get id offset limit (Store.World.learning state))

explanationFromViews : ℕ → ℕ → Ranking.Selection → Store.World → Store.World → Store.World → Store.World → Store.World → Result
explanationFromViews id offset limit beliefView parentView reviewView candidateView originView
  with Explanation.findBelief id (Store.nodes beliefView)
... | nothing = missingBelief
... | just b with Explanation.origin id (Store.World.learning originView)
...   | Origin.malformed = invalidProvenance
...   | source = explained (Explanation.explanation b
  (Explanation.parents id (Store.nodes parentView)
    (Publication.World.edges (Learning.World.publication (Store.World.learning parentView))))
  (Explanation.paginate offset limit (Explanation.reviews id
    (Learning.identities (Store.World.learning reviewView))
    (Publication.World.ledger (Learning.World.publication (Store.World.learning reviewView)))))
  (Candidate.get id (Store.World.learning candidateView)) source)

explanationFromOneView : ∀ id offset limit original parentsView reviewsView candidateView originView →
  parentsView ≡ original → reviewsView ≡ original → candidateView ≡ original → originView ≡ original →
  explanationFromViews id offset limit original parentsView reviewsView candidateView originView ≡
  explanationAnswer id offset limit original
explanationFromOneView id offset limit original .original .original .original .original refl refl refl refl
  with Explanation.findBelief id (Store.nodes original)
... | nothing = refl
... | just b with Explanation.origin id (Store.World.learning original)
...   | Origin.malformed = refl
...   | Origin.noProvenance = refl
...   | Origin.found origin = refl

pinnedRead : ℕ → Store.World → Statement → (Store.World → Script Result) → Script Result
pinnedRead tx original statement next = ask (explanationSnapshot tx original statement) λ where
  (inj₁ error) → close (just tx) (failed error)
  (inj₂ observed) → next observed

explainFromBelief : ℕ → ℕ → Ranking.Selection → ℕ → Store.World → Script Result
explainFromBelief id offset limit tx original with Explanation.findBelief id (Store.nodes original)
... | nothing = close (just tx) missingBelief
... | just b = pinnedRead tx original (incoming id) λ parentsView →
  pinnedRead tx original (reviews id) λ reviewsView →
  pinnedRead tx original (candidate id) λ candidateView →
  pinnedRead tx original (independent id) λ originView →
  close (just tx) (explanationFromViews id offset limit original parentsView reviewsView candidateView originView)

start : Request → Script Result
start (getBelief id) = read nothing (belief id) (λ w → done (beliefResult (Ranking.lookup id (Store.beliefs w))))
start (getPattern id) = read nothing (patternNode id) (λ w → done
  (patternResult (Records.getPattern id (Store.patterns (Store.nodes w)))))
start (listBeliefs project memory) = read nothing (beliefs project memory) (λ w → done
  (beliefList (Records.listBeliefs project memory (Store.beliefs w))))
start (listPatterns project) = read nothing (patterns project) (λ w → done
  (patternList (Records.listPatterns project (Store.patterns (Store.nodes w)))))
start (beliefPage project memory limit offset) with Records.pageAdmitted limit offset
... | false = done invalidPage
... | true = ask (openPage project memory) (λ
  { (inj₁ error) → done (failed error)
  ; (inj₂ (tx , first)) → ask (pageSnapshotRows tx first project memory limit offset) (λ
      { (inj₁ error) → close (just tx) (failed error)
      ; (inj₂ second) → close (just tx) (paged (Records.pageResult project memory limit offset
          (length (Records.listBeliefs project memory (Store.beliefs first))) (Store.beliefs second))) }) })
start (explain id offset limit) = ask (openExplanation id) λ where
  (inj₁ error) → done (failed error)
  (inj₂ (tx , original)) → explainFromBelief id offset limit tx original
start stats = ask openStatistics λ where
  (inj₁ error) → done (failed error)
  (inj₂ (tx , first)) → statisticsRead tx first countPatterns (λ patterns →
    statisticsRead tx first (countEdges R.supports) (λ supports →
    statisticsRead tx first (countEdges R.defeats) (λ defeats →
    statisticsRead tx first (countEdges R.causes) (λ causes →
    statisticsRead tx first (countEdges R.contradicts) (λ contradictions → close (just tx)
      (counted (statisticsFromViews first patterns supports defeats causes contradictions)))))))
