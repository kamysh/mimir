{-# OPTIONS --safe #-}
-- A read-only retrieval machine. Each database reply is a fresh observation;
-- graph traversal is an explicit transition loop, not an assumed closure
-- callback. The unscoped SQL closure and scoped direct-neighbor query are
-- intentionally distinct commands. Failures do not silently become no hits.
module Mimir.RetrievalProtocol where

open import Data.Bool using (Bool; true; false; not)
open import Data.Float.Base using (Float)
open import Data.List using (List; []; _∷_; _++_; map; filterᵇ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Mimir.UUIDGroups using (UUID)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.CandidateGraph as Graph
import Mimir.LearningCandidates as Candidates
import Mimir.RetrievalRanking as R

-- Semantic retrieval can be unavailable for this particular input. It is not
-- equivalent to a completed search with no matches, and must survive every
-- later lexical/graph/evidence step into the public response.
data UnavailableCause : Set where
  notConfigured unsupportedContent providerFailure invalidProviderReply : UnavailableCause

record Unavailable : Set where
  constructor unavailable
  field
    cause : UnavailableCause
    reason nextAction : Text

data SemanticStatus : Set where
  performed noEligibleBeliefs : SemanticStatus
  notAvailable : Unavailable → SemanticStatus

record Report (A : Set) : Set where
  constructor report
  field
    context : Text
    beliefs : List A
    semanticSearch : SemanticStatus

EmbeddingReply = Unavailable ⊎ List (List Float)

record Request : Set where
  constructor request
  field query : Text; limit : Maybe ℕ; project : Maybe Text
        preference : Maybe Candidates.Memory; embeddingsEnabled : Bool

record Context : Set where
  constructor context
  field requestValue : Request; superseded : List UUID
        token vector : List UUID; matched : List Graph.BeliefValues
        semanticSearch : SemanticStatus

data State : Set where
  overlay : Request → State
  beliefs : Request → List UUID → State
  embedding : Request → List UUID → List Graph.BeliefValues → List UUID → State
  vectorQuery : Request → List UUID → List Graph.BeliefValues → List UUID → List Float → State
  closure : Context → UUID → List UUID → State
  neighbors : Context → Text → UUID → List UUID → List UUID → List UUID → State
  finished : Report Graph.BeliefValues → State
  failed : Text → State

Reply : State → Set
Reply (overlay r) = Text ⊎ List UUID
Reply (beliefs r retired) = Text ⊎ List Graph.BeliefValues
Reply (embedding r retired all token) = EmbeddingReply
Reply (vectorQuery r retired all token vector) = Text ⊎ List UUID
Reply (closure c id seeds) = Text ⊎ List Graph.BeliefValues
Reply (neighbors c project id seeds frontier next) = Text ⊎ List Graph.BeliefValues
Reply (finished result) = ⊤
Reply (failed message) = ⊤

data Command : Set where
  readActiveOverlay : Maybe Text → Command
  listBeliefs : Maybe Text → Command
  embedQuery : Text → Command
  queryVector : List Float → Maybe ℕ → Maybe (List UUID) → Command
  readClosure : UUID → Command
  readNeighbors : UUID → Text → Command

command : State → Maybe Command
command (overlay r) = just (readActiveOverlay (Request.project r))
command (beliefs r retired) = just (listBeliefs (Request.project r))
command (embedding r retired all token) = just (embedQuery (Request.query r))
command (vectorQuery r retired all token v) with Request.project r
... | nothing = just (queryVector v nothing nothing)
... | just _ = just (queryVector v nothing
  (just (map Graph.BeliefValues.identity all)))
command (closure c id seeds) = just (readClosure id)
command (neighbors c project id seeds frontier next) = just (readNeighbors id project)
command (finished result) = nothing
command (failed message) = nothing

last : ∀ {A : Set} → List A → Maybe A
last [] = nothing
last (x ∷ []) = just x
last (x ∷ y ∷ xs) = last (y ∷ xs)

-- Keep first encountered row, preserving the service's append/visited order.
appendNew : List Graph.BeliefValues → List Graph.BeliefValues →
  List Graph.BeliefValues × List UUID
appendNew matched [] = matched , []
appendNew matched (b ∷ bs) with R.member (Graph.BeliefValues.identity b)
  (map Graph.BeliefValues.identity matched)
... | true = appendNew matched bs
... | false with appendNew (matched ++ (b ∷ [])) bs
...   | result , ids = result , (Graph.BeliefValues.identity b ∷ ids)

module Run (ops : R.F32) (unicode : R.Unicode) where
  module F = R.Fusion ops

  finish : Context → State
  finish c = finished (report (Request.query r)
    (F.rank (Context.vector c) (Context.token c)
      (Request.preference r) (Request.limit r) (Context.matched c))
    (Context.semanticSearch c))
    where r = Context.requestValue c

  seed : Context → List UUID → State
  seed c [] = finish c
  seed c (id ∷ seeds) with Request.project (Context.requestValue c)
  ... | nothing = closure c id seeds
  ... | just project = neighbors c project id seeds [] []

  seeded : Request → List UUID → List Graph.BeliefValues → List UUID → List UUID → SemanticStatus → State
  seeded r retired all token vector semantic = seed c (map Graph.BeliefValues.identity matched)
    where
    matched = R.materialize (R.unique (token ++ vector)) all
    c = context r retired token vector matched semantic

  loaded : Request → List UUID → List Graph.BeliefValues → State
  loaded r retired [] = finished (report (Request.query r) [] noEligibleBeliefs)
  loaded r retired all@(_ ∷ _) with Request.embeddingsEnabled r
  ... | true = embedding r retired all (R.tokenRanking unicode (Request.query r) all)
  ... | false = seeded r retired all (R.tokenRanking unicode (Request.query r) all) []
    (notAvailable (unavailable notConfigured
      (toList "Semantic search was not performed because no embedding provider is configured.")
      (toList "These results use lexical and graph retrieval. Configure an embedding provider if semantic search is required.")))

  nextHop : Context → Text → List UUID → List UUID → List UUID → State
  nextHop c project seeds (id ∷ rest) next = neighbors c project id seeds rest next
  nextHop c project seeds [] (id ∷ next) = neighbors c project id seeds next []
  nextHop c project seeds [] [] = seed c seeds

  advance : (s : State) → Reply s → State
  advance (overlay r) (inj₁ error) = failed error
  advance (overlay r) (inj₂ retired) = beliefs r retired
  advance (beliefs r retired) (inj₁ error) = failed error
  advance (beliefs r retired) (inj₂ all) = loaded r retired
    (filterᵇ (R.eligible (Request.project r) retired) all)
  advance (embedding r retired all token) (inj₁ why) = seeded r retired all token [] (notAvailable why)
  advance (embedding r retired all token) (inj₂ vectors) with last vectors
  ... | nothing = seeded r retired all token [] (notAvailable (unavailable invalidProviderReply
    (toList "Semantic search was not performed because the embedding provider returned no query vector.")
    (toList "These results use lexical and graph retrieval. Resolve the embedding provider response before requesting semantic search again.")))
  ... | just v = vectorQuery r retired all token v
  advance (vectorQuery r retired all token v) (inj₁ error) = failed error
  advance (vectorQuery r retired all token v) (inj₂ vector) = seeded r retired all token vector performed
  advance (closure c id seeds) (inj₁ error) = failed error
  advance (closure c id seeds) (inj₂ rows) with appendNew (Context.matched c)
    (filterᵇ (R.eligible nothing (Context.superseded c)) rows)
  ... | matched , ids = seed (record c { matched = matched }) seeds
  advance (neighbors c project id seeds frontier next) (inj₁ error) = failed error
  advance (neighbors c project id seeds frontier next) (inj₂ rows) with
    appendNew (Context.matched c) (filterᵇ (R.eligible (just project) (Context.superseded c)) rows)
  ... | matched , ids = nextHop (record c { matched = matched }) project seeds frontier (next ++ ids)
  advance s@(finished result) reply = s
  advance s@(failed error) reply = s

  vectorFailureIsFailure : ∀ r retired all token v error →
    advance (vectorQuery r retired all token v) (inj₁ error) ≡ failed error
  vectorFailureIsFailure r retired all token v error = refl

  -- Once semantic availability is known, further graph traversal must not
  -- erase it. Database failures remain failures, not fabricated empty hits.
  data Retains : SemanticStatus → State → Set where
    atClosure : ∀ c id seeds → Retains (Context.semanticSearch c) (closure c id seeds)
    atNeighbors : ∀ c project id seeds frontier next →
      Retains (Context.semanticSearch c) (neighbors c project id seeds frontier next)
    atFinished : ∀ result → Retains (Report.semanticSearch result) (finished result)
    atFailure : ∀ status error → Retains status (failed error)

  seedRetains : ∀ c ids → Retains (Context.semanticSearch c) (seed c ids)
  seedRetains c [] = atFinished _
  seedRetains c (id ∷ seeds) with Request.project (Context.requestValue c)
  ... | nothing = atClosure c id seeds
  ... | just project = atNeighbors c project id seeds [] []

  nextHopRetains : ∀ c project seeds frontier next →
    Retains (Context.semanticSearch c) (nextHop c project seeds frontier next)
  nextHopRetains c project seeds (id ∷ rest) next = atNeighbors c project id seeds rest next
  nextHopRetains c project seeds [] (id ∷ next) = atNeighbors c project id seeds next []
  nextHopRetains c project seeds [] [] = seedRetains c seeds

  advanceRetains : ∀ {status state} (reply : Reply state) → Retains status state →
    Retains status (advance state reply)
  advanceRetains (inj₁ error) (atClosure c id seeds) = atFailure _ error
  advanceRetains (inj₂ rows) (atClosure c id seeds)
    with appendNew (Context.matched c) (filterᵇ (R.eligible nothing (Context.superseded c)) rows)
  ... | matched , ids = seedRetains (record c { matched = matched }) seeds
  advanceRetains (inj₁ error) (atNeighbors c project id seeds frontier next) = atFailure _ error
  advanceRetains (inj₂ rows) (atNeighbors c project id seeds frontier next)
    with appendNew (Context.matched c) (filterᵇ (R.eligible (just project) (Context.superseded c)) rows)
  ... | matched , ids = nextHopRetains (record c { matched = matched }) project seeds frontier (next ++ ids)
  advanceRetains reply (atFinished result) = atFinished result
  advanceRetains reply (atFailure status error) = atFailure status error

  data Returns : State → Report Graph.BeliefValues → Set where
    returned : ∀ result → Returns (finished result) result
    stepped : ∀ state (reply : Reply state) {result} →
      Returns (advance state reply) result → Returns state result

  completedRetainsStatus : ∀ {status state result} → Retains status state → Returns state result →
    Report.semanticSearch result ≡ status
  completedRetainsStatus (atFinished result) (returned .result) = refl
  completedRetainsStatus retained (stepped state reply rest) =
    completedRetainsStatus (advanceRetains reply retained) rest

-- Commands contain no graph writes, activations or experience recording.
-- Semantic-search availability is part of the returned report, including
-- successful lexical/graph results obtained while semantic search is absent.
