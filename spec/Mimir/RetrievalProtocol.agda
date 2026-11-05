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
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.CandidateGraph as Graph
import Mimir.LearningCandidates as Candidates
import Mimir.RetrievalRanking as R

record Request : Set where
  constructor request
  field query : Text; limit : ℕ; project : Maybe Text
        preference : Maybe Candidates.Memory; embeddingsEnabled : Bool

record Context : Set where
  constructor context
  field requestValue : Request; superseded : List ℕ
        token vector : List ℕ; matched : List Graph.BeliefValues

data State : Set where
  overlay : Request → State
  beliefs : Request → List ℕ → State
  embedding : Request → List ℕ → List Graph.BeliefValues → List ℕ → State
  vectorQuery : Request → List ℕ → List Graph.BeliefValues → List ℕ → List Float → State
  closure : Context → ℕ → List ℕ → State
  neighbors : Context → Text → ℕ → List ℕ → List ℕ → List ℕ → State
  finished : List Graph.BeliefValues → State
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
  queryVector : List Float → ℕ → Maybe (List ℕ) → Command
  readClosure : ℕ → Command
  readNeighbors : ℕ → Text → Command

command : State → Maybe Command
command (overlay r) = just (readActiveOverlay (Request.project r))
command (beliefs r retired) = just (listBeliefs (Request.project r))
command (embedding r retired all token) = just (embedQuery (Request.query r))
command (vectorQuery r retired all token v) with Request.project r
... | nothing = just (queryVector v (R.poolSize (Request.limit r)) nothing)
... | just _ = just (queryVector v (R.poolSize (Request.limit r))
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
  finish c = finished (F.rank (Context.vector c) (Context.token c)
    (Request.preference r) (Request.limit r) (Context.matched c))
    where r = Context.requestValue c

  seed : Context → List ℕ → State
  seed c [] = finish c
  seed c (id ∷ seeds) with Request.project (Context.requestValue c)
  ... | nothing = closure c id seeds
  ... | just project = neighbors c project id seeds [] []

  seeded : Request → List ℕ → List Graph.BeliefValues → List ℕ → List ℕ → State
  seeded r retired all token vector = seed c (map Graph.BeliefValues.identity matched)
    where
    matched = R.materialize (R.unique (token ++ vector)) all
    c = context r retired token vector matched

  loaded : Request → List ℕ → List Graph.BeliefValues → State
  loaded r retired [] = finished []
  loaded r retired all@(_ ∷ _) with Request.embeddingsEnabled r
  ... | true = embedding r retired all (R.tokenRanking unicode (Request.query r) all)
  ... | false = seeded r retired all (R.tokenRanking unicode (Request.query r) all) []

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
  advance (embedding r retired all token) (inj₁ error) = seeded r retired all token []
  advance (embedding r retired all token) (inj₂ vectors) with last vectors
  ... | nothing = seeded r retired all token []
  ... | just v = vectorQuery r retired all token v
  advance (vectorQuery r retired all token v) (inj₁ error) = failed error
  advance (vectorQuery r retired all token v) (inj₂ vector) = seeded r retired all token vector
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

-- Commands contain no graph writes, activations or experience recording.
-- Warnings accompanying embedder fallback are presentation events; the error
-- is available in the transition input and is not mistaken for DB success.
