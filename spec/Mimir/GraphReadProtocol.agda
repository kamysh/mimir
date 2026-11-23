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
import Mimir.CandidateGraph as G
import Mimir.LearningCandidates as C
import Mimir.GraphRecords as Records
import Mimir.RetrievalRanking as Ranking
import Mimir.BeliefExplanation as Explanation
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
  belief patternNode explanationSnapshot : UUID → Statement
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
start (explain id offset limit) = read nothing (explanationSnapshot id) λ snapshot →
  finish (Explanation.get id offset limit (Store.World.learning snapshot))
  where
  finish : Explanation.Result → Script Result
  finish Explanation.beliefMissing = done missingBelief
  finish Explanation.invalidLimit = done invalidPage
  finish Explanation.invalidStoredProvenance = done invalidProvenance
  finish (Explanation.explained value) = done (explained value)
start stats = ask statistics λ where
  (inj₁ error) → done (failed error)
  (inj₂ value) → done (counted value)
