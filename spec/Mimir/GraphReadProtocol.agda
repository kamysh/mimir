{-# OPTIONS --safe #-}
-- Concrete projections of independently observed SELECT snapshots. This is
-- deliberately not a single-snapshot fiction for multi-query read operations.
module Mimir.GraphReadProtocol where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_; length; filterᵇ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤?_; _≟_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Relation.Nullary using (does)
open import Mimir.Text using (Text)
open import Mimir.UUIDGroups using (UUID)
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
import Mimir.StructuredValue as V
open import Mimir.Collections using (validSelection)

data Request : Set where
  getBelief getPattern : UUID → Request
  listBeliefs : Maybe Text → Maybe C.Memory → Request
  listPatterns : Maybe Text → Request
  beliefPage : Maybe Text → Maybe C.Memory → ℕ → ℕ → Request -- limit, offset
  explain : UUID → ℕ → Maybe ℕ → Request -- id, offset, optional selection
  stats : Request

data Statement : Set where
  belief patternNode incoming reviews candidate independent : UUID → Statement
  beliefs countBeliefs : Maybe Text → Maybe C.Memory → Statement
  pageRows : Maybe Text → Maybe C.Memory → ℕ → ℕ → Statement
  patterns : Maybe Text → Statement

data Effect : Set where
  beginRead : Effect
  statistics : Effect
  select : Maybe ℕ → Statement → Effect
  dropTransaction : ℕ → Effect

Reply : Effect → Set
Reply beginRead = Text ⊎ ℕ
Reply statistics = Text ⊎ V.Value
Reply (select handle statement) = Text ⊎ Store.World
Reply (dropTransaction tx) = ⊤

module E = Effects.Protocol Effect Reply
open E

data Result : Set where
  failed : Text → Result
  invalidPage missingBelief invalidProvenance : Result
  beliefResult : Maybe G.BeliefValues → Result
  patternResult : Maybe G.PatternValues → Result
  beliefList : List G.BeliefValues → Result
  patternList : List G.PatternValues → Result
  paged : Records.Page → Result
  explained : Explanation.Explanation → Result
  counted : V.Value → Result

close : Maybe ℕ → Result → Script Result
close nothing result = done result
close (just tx) result = ask (dropTransaction tx) (λ _ → done result)

read : Maybe ℕ → Statement → (Store.World → Script Result) → Script Result
read handle statement next = ask (select handle statement) (λ
  { (inj₁ error) → close handle (failed error)
  ; (inj₂ observed) → next observed })

finishExplanation : UUID → G.BeliefValues → List Explanation.Incoming → Explanation.Page →
  Maybe Candidate.Provenance → Store.World → Script Result
finishExplanation id b parents selectedPage provenance w with Explanation.origin id (Store.World.learning w)
... | Origin.malformed = done invalidProvenance
... | source = done (explained (Explanation.explanation b parents selectedPage provenance source))

afterReviews : UUID → G.BeliefValues → List Explanation.Incoming → ℕ → Maybe ℕ → ℕ → Store.World → Script Result
afterReviews id b parents offset limit tx w = ask (dropTransaction tx) (λ _ →
  read nothing (candidate id) (λ c → read nothing (independent id)
    (finishExplanation id b parents page (Candidate.get id (Store.World.learning c)))))
  where
  learn = Store.World.learning w
  page = Explanation.paginate offset limit (Explanation.reviews id (Learning.identities learn)
    (Publication.World.ledger (Learning.World.publication learn)))

afterParents : UUID → G.BeliefValues → ℕ → Maybe ℕ → Store.World → Script Result
afterParents id b offset limit w with validSelection limit
... | false = done invalidPage
... | true = ask beginRead (λ
  { (inj₁ error) → done (failed error)
  ; (inj₂ tx) → read (just tx) (reviews id) (afterReviews id b parents offset limit tx) })
  where parents = Explanation.parents id (Store.nodes w)
          (Publication.World.edges (Learning.World.publication (Store.World.learning w)))

afterBelief : UUID → ℕ → Maybe ℕ → Store.World → Script Result
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
... | true = read nothing (countBeliefs project memory) (λ first →
  read nothing (pageRows project memory limit offset) (λ second → done (paged
    (Records.pageResult project memory limit offset
      (length (Records.listBeliefs project memory (Store.beliefs first))) (Store.beliefs second)))))
start (explain id offset limit) = read nothing (belief id) (afterBelief id offset limit)
start stats = ask statistics λ where
  (inj₁ error) → done (failed error)
  (inj₂ value) → done (counted value)
