{-# OPTIONS --safe #-}
-- A read-only retrieval machine. The response binding pins database replies
-- to one stable view while retaining every individual read;
-- graph traversal is an explicit transition loop, not an assumed closure
-- callback. The unscoped SQL closure and scoped direct-neighbor query are
-- intentionally distinct commands. Failures do not silently become no hits.
module Mimir.RetrievalProtocol where

open import Data.Bool using (Bool; true; false; not)
open import Data.Float.Base using (Float)
open import Data.Float.Base using (isNaN; isInfinite; _≡ᵇ_)
open import Data.List using (List; []; _∷_; _++_; map; filterᵇ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.String using (toList)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.CandidateGraph as Graph
import Mimir.LearningCandidates as Candidates
import Mimir.RetrievalRanking as R
import Mimir.StructuredValue as Wire

-- Availability records observations, never a classifier of whether text has
-- semantic meaning. Literal contexts remain valid keyword-search requests.
data Semantic : Set where
  evaluated unconfigured noEligibleBeliefs : Semantic
  embeddingFailed unusableQueryVector : Text → Semantic

record Coverage : Set where
  constructor coverage
  field context : Text; semantic : Semantic

record Report : Set where
  constructor report
  field beliefs : List Graph.BeliefValues; retrieval : Coverage

semanticStatus : Semantic → Text
semanticStatus evaluated = toList "available"
semanticStatus noEligibleBeliefs = toList "not_performed"
semanticStatus _ = toList "unavailable"

semanticReason : Semantic → Text
semanticReason evaluated = toList "evaluated"
semanticReason unconfigured = toList "not_configured"
semanticReason noEligibleBeliefs = toList "no_eligible_beliefs"
semanticReason (embeddingFailed cause) = toList "embedding_failed"
semanticReason (unusableQueryVector cause) = toList "unusable_query_vector"

semanticCause : Semantic → Wire.Value
semanticCause (embeddingFailed cause) = Wire.string cause
semanticCause (unusableQueryVector cause) = Wire.string cause
semanticCause _ = Wire.null

matchingPerformed : Semantic → Text
matchingPerformed evaluated = toList "keyword_and_semantic"
matchingPerformed noEligibleBeliefs = toList "none"
matchingPerformed _ = toList "keyword"

message : Semantic → Text
message evaluated = toList "Semantic search and keyword matching were performed for this context."
message unconfigured = toList "Semantic search was not performed because no embedding backend is configured. These results use keyword matching; semantic similarity was not evaluated."
message noEligibleBeliefs = toList "No eligible stored beliefs exist in the requested scope. Semantic search and keyword matching were not performed."
message (embeddingFailed cause) = toList "Semantic search was not performed because the configured embedding backend failed for this context: " ++ cause ++
  toList ". These results use keyword matching; semantic similarity was not evaluated."
message (unusableQueryVector cause) = toList "Semantic search was not performed because the configured backend did not return a usable query vector: " ++ cause ++
  toList ". These results use keyword matching; semantic similarity was not evaluated."

resultCoverage : Semantic → Text
resultCoverage evaluated = toList "Results combine semantic and literal matches with any graph expansion and ranking."
resultCoverage noEligibleBeliefs = toList "No searchable beliefs were available in this scope; this does not establish that the context has no useful meaning."
resultCoverage _ = toList "Results cover literal matches and any graph connections derived from them. Beliefs related only by semantic similarity may be missing."

nextStep : Semantic → Text
nextStep evaluated = toList "Inspect the returned beliefs and supporting evidence before relying on them."
nextStep unconfigured = toList "Use these results for literal matching. If semantic matching is needed, ask the user to configure an embedding backend and repeat this query."
nextStep noEligibleBeliefs = toList "Check the requested project and the stored belief inventory. Do not infer that no relevant knowledge exists outside this scope."
nextStep (embeddingFailed cause) = toList "Use the stated cause to resolve the backend problem and repeat this query if semantic coverage is needed. Keyword results remain usable for literal matching."
nextStep (unusableQueryVector cause) = toList "Check the backend's response for the complete submitted context and repeat this query if semantic coverage is needed. Do not silently shorten the input."

coverageValue : Coverage → Wire.Value
coverageValue observed = Wire.object
  ((toList "context" , Wire.string (Coverage.context observed)) ∷
   (toList "semantic_search" , Wire.object
     ((toList "status" , Wire.string (semanticStatus semantic)) ∷
      (toList "reason" , Wire.string (semanticReason semantic)) ∷
      (toList "cause" , semanticCause semantic) ∷ [])) ∷
   (toList "matching_performed" , Wire.string (matchingPerformed semantic)) ∷
   (toList "message" , Wire.string (message semantic)) ∷
   (toList "coverage" , Wire.string (resultCoverage semantic)) ∷
   (toList "next_step" , Wire.string (nextStep semantic)) ∷ [])
  where semantic = Coverage.semantic observed

record Request : Set where
  constructor request
  field query : Text; limit : R.Selection; project : Maybe Text
        preference : Maybe Candidates.Memory; embeddingsEnabled : Bool

record Context : Set where
  constructor context
  field requestValue : Request; superseded : List ℕ
        token vector : List ℕ; matched : List Graph.BeliefValues; semantic : Semantic

data State : Set where
  overlay : Request → State
  beliefs : Request → List ℕ → State
  embedding : Request → List ℕ → List Graph.BeliefValues → List ℕ → State
  vectorQuery : Request → List ℕ → List Graph.BeliefValues → List ℕ → List Float → State
  closure : Context → ℕ → List ℕ → State
  neighbors : Context → Text → ℕ → List ℕ → List ℕ → List ℕ → State
  finished : Report → State
  failed : Text → State

Reply : State → Set
Reply (overlay r) = Text ⊎ List ℕ
Reply (beliefs r retired) = Text ⊎ List Graph.BeliefValues
Reply (embedding r retired all token) = Text ⊎ List (List Float)
Reply (vectorQuery r retired all token vector) = Text ⊎ List ℕ
Reply (closure c id seeds) = Text ⊎ List Graph.BeliefValues
Reply (neighbors c project id seeds frontier next) = Text ⊎ List Graph.BeliefValues
Reply (finished result) = ⊤
Reply (failed message) = ⊤

data Command : Set where
  readActiveOverlay : Maybe Text → Command
  listBeliefs : Maybe Text → Command
  embedQuery : Text → Command
  queryVector : List Float → R.Selection → Maybe (List ℕ) → Command
  readClosure : ℕ → Command
  readNeighbors : ℕ → Text → Command

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
  List Graph.BeliefValues × List ℕ
appendNew matched [] = matched , []
appendNew matched (b ∷ bs) with R.member (Graph.BeliefValues.identity b)
  (map Graph.BeliefValues.identity matched)
... | true = appendNew matched bs
... | false with appendNew (matched ++ (b ∷ [])) bs
...   | result , ids = result , (Graph.BeliefValues.identity b ∷ ids)

module Run (ops : R.F32) (unicode : R.Unicode) where
  module F = R.Fusion ops

  finish : Context → State
  finish c = finished (report (F.rank (Context.vector c) (Context.token c)
    (Request.preference r) (Request.limit r) (Context.matched c))
    (coverage (Request.query r) (Context.semantic c)))
    where r = Context.requestValue c

  seed : Context → List ℕ → State
  seed c [] = finish c
  seed c (id ∷ seeds) with Request.project (Context.requestValue c)
  ... | nothing = closure c id seeds
  ... | just project = neighbors c project id seeds [] []

  seeded : Request → List ℕ → List Graph.BeliefValues → List ℕ → List ℕ → Semantic → State
  seeded r retired all token vector semantic = seed c (map Graph.BeliefValues.identity matched)
    where
    matched = R.materialize (R.unique (token ++ vector)) all
    c = context r retired token vector matched semantic

  loaded : Request → List ℕ → List Graph.BeliefValues → State
  loaded r retired [] = finished (report [] (coverage (Request.query r) noEligibleBeliefs))
  loaded r retired all@(_ ∷ _) with Request.embeddingsEnabled r
  ... | true = embedding r retired all (R.tokenRanking unicode (Request.query r) all)
  ... | false = seeded r retired all (R.tokenRanking unicode (Request.query r) all) [] unconfigured

  finiteVector : List Float → Bool
  finiteVector [] = true
  finiteVector (value ∷ rest) with isNaN value
  ... | true = false
  ... | false with isInfinite value
  ...   | true = false
  ...   | false = finiteVector rest

  nonzeroVector : List Float → Bool
  nonzeroVector [] = false
  nonzeroVector (value ∷ rest) with value ≡ᵇ 0.0
  ... | true = nonzeroVector rest
  ... | false = true

  afterEmbedding : Request → List ℕ → List Graph.BeliefValues → List ℕ → List (List Float) → State
  afterEmbedding r retired all token ((value ∷ values) ∷ []) with finiteVector (value ∷ values)
  ... | false = seeded r retired all token [] (unusableQueryVector (toList "The query embedding contains a non-finite value."))
  ... | true with nonzeroVector (value ∷ values)
  ...   | false = seeded r retired all token []
    (unusableQueryVector (toList "The query embedding has zero norm, so cosine similarity is undefined."))
  ...   | true = vectorQuery r retired all token (value ∷ values)
  afterEmbedding r retired all token [] = seeded r retired all token []
    (unusableQueryVector (toList "The backend returned no query embedding."))
  afterEmbedding r retired all token ([] ∷ []) = seeded r retired all token []
    (unusableQueryVector (toList "The query embedding is empty."))
  afterEmbedding r retired all token (_ ∷ _ ∷ _) = seeded r retired all token []
    (unusableQueryVector (toList "The backend returned multiple embeddings for one submitted context."))

  nextHop : Context → Text → List ℕ → List ℕ → List ℕ → State
  nextHop c project seeds (id ∷ rest) next = neighbors c project id seeds rest next
  nextHop c project seeds [] (id ∷ next) = neighbors c project id seeds next []
  nextHop c project seeds [] [] = seed c seeds

  advance : (s : State) → Reply s → State
  advance (overlay r) (inj₁ error) = failed error
  advance (overlay r) (inj₂ retired) = beliefs r retired
  advance (beliefs r retired) (inj₁ error) = failed error
  advance (beliefs r retired) (inj₂ all) = loaded r retired
    (filterᵇ (R.eligible (Request.project r) retired) all)
  advance (embedding r retired all token) (inj₁ error) = seeded r retired all token [] (embeddingFailed error)
  advance (embedding r retired all token) (inj₂ vectors) = afterEmbedding r retired all token vectors
  advance (vectorQuery r retired all token v) (inj₁ error) = failed error
  advance (vectorQuery r retired all token v) (inj₂ vector) = seeded r retired all token vector evaluated
  advance (closure c id seeds) (inj₁ error) = failed error
  advance (closure c id seeds) (inj₂ rows) with appendNew (Context.matched c)
    (R.byIdentity (filterᵇ (R.eligible nothing (Context.superseded c)) rows))
  ... | matched , ids = seed (record c { matched = matched }) seeds
  advance (neighbors c project id seeds frontier next) (inj₁ error) = failed error
  advance (neighbors c project id seeds frontier next) (inj₂ rows) with
    appendNew (Context.matched c) (R.byIdentity (filterᵇ (R.eligible (just project) (Context.superseded c)) rows))
  ... | matched , ids = nextHop (record c { matched = matched }) project seeds frontier (next ++ ids)
  advance s@(finished result) reply = s
  advance s@(failed error) reply = s

  vectorFailureIsFailure : ∀ r retired all token v error →
    advance (vectorQuery r retired all token v) (inj₁ error) ≡ failed error
  vectorFailureIsFailure r retired all token v error = refl

  unconfiguredUsesAnExplicitKeywordPath : ∀ r retired first rest →
    Request.embeddingsEnabled r ≡ false →
    loaded r retired (first ∷ rest) ≡
      seeded r retired (first ∷ rest) (R.tokenRanking unicode (Request.query r) (first ∷ rest)) [] unconfigured
  unconfiguredUsesAnExplicitKeywordPath r retired first rest absent rewrite absent = refl

  backendFailureRetainsItsCause : ∀ r retired all token cause →
    advance (embedding r retired all token) (inj₁ cause) ≡
      seeded r retired all token [] (embeddingFailed cause)
  backendFailureRetainsItsCause r retired all token cause = refl

  nonfiniteQueryVectorIsNotSemanticSearch : ∀ r retired all token first rest →
    finiteVector (first ∷ rest) ≡ false →
    afterEmbedding r retired all token ((first ∷ rest) ∷ []) ≡
      seeded r retired all token []
        (unusableQueryVector (toList "The query embedding contains a non-finite value."))
  nonfiniteQueryVectorIsNotSemanticSearch r retired all token first rest invalid rewrite invalid = refl

  zeroNormQueryVectorIsNotSemanticSearch : ∀ r retired all token first rest →
    finiteVector (first ∷ rest) ≡ true → nonzeroVector (first ∷ rest) ≡ false →
    afterEmbedding r retired all token ((first ∷ rest) ∷ []) ≡
      seeded r retired all token []
        (unusableQueryVector (toList "The query embedding has zero norm, so cosine similarity is undefined."))
  zeroNormQueryVectorIsNotSemanticSearch r retired all token first rest finite zeroNorm
    rewrite finite | zeroNorm = refl

-- Commands contain no graph writes, activations or experience recording.
-- Warnings accompanying embedder fallback are presentation events; the error
-- is available in the transition input and is not mistaken for DB success.
