{-# OPTIONS --safe #-}
-- Ordinary reads retain independently observed SELECT snapshots. Paging uses
-- an explicit read-only stable transaction: its row query is tied to the
-- original count snapshot by StorageReadBinding, not an unrelated observation.
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
  explain : ℕ → ℕ → ℕ → Request -- id, offset, limit
  stats : Request

data Statement : Set where
  belief patternNode incoming reviews candidate independent : ℕ → Statement
  beliefs countBeliefs : Maybe Text → Maybe C.Memory → Statement
  patterns : Maybe Text → Statement
  countPatterns : Statement
  countEdges : R.Relation → Statement

data Effect : Set where
  beginRead : Effect
  openPage : Maybe Text → Maybe C.Memory → Effect
  pageSnapshotRows : ℕ → Store.World → Maybe Text → Maybe C.Memory → ℕ → ℕ → Effect
  select : Maybe ℕ → Statement → Effect
  dropTransaction : ℕ → Effect

Reply : Effect → Set
Reply beginRead = Text ⊎ ℕ
Reply (openPage project memory) = Text ⊎ (ℕ × Store.World)
Reply (pageSnapshotRows tx initial project memory limit offset) = Text ⊎ Store.World
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

finishExplanation : ℕ → G.BeliefValues → List Explanation.Incoming → Explanation.Page →
  Maybe Candidate.Provenance → Store.World → Script Result
finishExplanation id b parents selectedPage provenance w with Explanation.origin id (Store.World.learning w)
... | Origin.malformed = done invalidProvenance
... | source = done (explained (Explanation.explanation b parents selectedPage provenance source))

afterReviews : ℕ → G.BeliefValues → List Explanation.Incoming → ℕ → ℕ → ℕ → Store.World → Script Result
afterReviews id b parents offset limit tx w = ask (dropTransaction tx) (λ _ →
  read nothing (candidate id) (λ c → read nothing (independent id)
    (finishExplanation id b parents page (Candidate.get id (Store.World.learning c)))))
  where
  learn = Store.World.learning w
  page = Explanation.paginate offset limit (Explanation.reviews id (Learning.identities learn)
    (Publication.World.ledger (Learning.World.publication learn)))

afterParents : ℕ → G.BeliefValues → ℕ → ℕ → Store.World → Script Result
afterParents id b offset limit w with does (1 ≤? limit)
... | false = done invalidPage
... | true = ask beginRead (λ
  { (inj₁ error) → done (failed error)
  ; (inj₂ tx) → read (just tx) (reviews id) (afterReviews id b parents offset limit tx) })
  where parents = Explanation.parents id (Store.nodes w)
          (Publication.World.edges (Learning.World.publication (Store.World.learning w)))

afterBelief : ℕ → ℕ → ℕ → Store.World → Script Result
afterBelief id offset limit w with Ranking.lookup id (Store.beliefs w)
... | nothing = done missingBelief
... | just b = read nothing (incoming id) (afterParents id b offset limit)

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
start (explain id offset limit) = read nothing (belief id) (afterBelief id offset limit)
start stats = read nothing (countBeliefs nothing nothing) (λ b → read nothing countPatterns (λ p →
  read nothing (countEdges R.supports) (λ s → read nothing (countEdges R.defeats) (λ d →
  read nothing (countEdges R.causes) (λ c → read nothing (countEdges R.contradicts) (λ k → done
    (counted (statistics (length (Store.beliefs b)) (length (Store.patterns (Store.nodes p)))
      (countRelation R.supports s) (countRelation R.defeats d) (countRelation R.causes c)
      (countRelation R.contradicts k)))))))))
