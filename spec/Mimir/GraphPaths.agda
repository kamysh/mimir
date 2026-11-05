{-# OPTIONS --safe #-}
-- Required results are specified by reachability, without reimplementing the
-- AGE engine. NativeQuery records current SQL choices separately; those choices
-- must not weaken the existing mixed-edge closure requirement in Graph.agda.
module Mimir.GraphPaths where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Mimir.Text using (Text)
import Mimir.CandidateGraph as G
import Mimir.CandidateRegistry as Registry
import Mimir.ReviewEdges as E
import Mimir.ReviewSchema as Review
import Mimir.RetrievalRanking as R

Live : List G.BeliefValues → ℕ → Set
Live beliefs id = Σ G.BeliefValues (λ b → b ∈ beliefs × G.BeliefValues.identity b ≡ id)

data Mode : Set where propagation causalOnly : Mode

Carries : Mode → Review.Relation → Set
Carries propagation Review.supports = ⊤
Carries propagation Review.defeats = ⊤
Carries propagation Review.causes = ⊤
Carries causalOnly Review.causes = ⊤
Carries _ _ = ⊥

record Hop (mode : Mode) (beliefs : List G.BeliefValues) (edges : List E.Edge) (source target : ℕ) : Set where
  constructor hop
  field
    selected : E.Edge
    present : selected ∈ edges
    sourceMatches : E.Edge.from selected ≡ source
    targetMatches : E.Edge.to selected ≡ target
    carries : Carries mode (E.Edge.relation selected)
    sourceLive : Live beliefs source
    targetLive : Live beliefs target

data Reaches (mode : Mode) (beliefs : List G.BeliefValues) (edges : List E.Edge) : ℕ → ℕ → Set where
  one : ∀ {source target} → Hop mode beliefs edges source target → Reaches mode beliefs edges source target
  more : ∀ {source middle target} → Hop mode beliefs edges source middle →
    Reaches mode beliefs edges middle target → Reaches mode beliefs edges source target

data Query : Set where
  allDownstream causalDownstream : ℕ → Query
  directScoped : ℕ → Text → Query

Eligible : Query → List G.BeliefValues → List E.Edge → G.BeliefValues → Set
Eligible (allDownstream seed) beliefs edges b = b ∈ beliefs × Reaches propagation beliefs edges seed (G.BeliefValues.identity b)
Eligible (causalDownstream seed) beliefs edges b = b ∈ beliefs × Reaches causalOnly beliefs edges seed (G.BeliefValues.identity b)
Eligible (directScoped seed project) beliefs edges b = b ∈ beliefs ×
  (Hop propagation beliefs edges seed (G.BeliefValues.identity b) × R.visible (just project) (G.BeliefValues.project b) ≡ true)

-- There is no ORDER BY here: any order of the complete distinct result set is
-- permitted. Missing reachable beliefs and foreign additions are forbidden.
record Returned (query : Query) (beliefs : List G.BeliefValues) (edges : List E.Edge) (rows : List G.BeliefValues) : Set where
  field
    sound : All (Eligible query beliefs edges) rows
    complete : ∀ b → Eligible query beliefs edges b → b ∈ rows
    unique : Registry.IDs.Unique (map G.BeliefValues.identity rows)

-- Observations of current Rust SQL, not replacement requirements. Standard AGE
-- interpretation is an external dependency; no unproved path axiom is added.
record Arm : Set where
  constructor arm
  field relation : Review.Relation; maximumHops : Maybe ℕ; endpointScope : Maybe Text

record NativeQuery : Set where
  constructor nativeQuery
  field arms : List Arm; unionDistinct : Bool

native : Query → NativeQuery
native (allDownstream seed) = nativeQuery
  (arm Review.supports nothing nothing ∷ arm Review.causes nothing nothing ∷ arm Review.defeats nothing nothing ∷ []) true
native (causalDownstream seed) = nativeQuery (arm Review.causes (just 10) nothing ∷ []) false
native (directScoped seed project) = nativeQuery
  (arm Review.supports (just 1) (just project) ∷ arm Review.causes (just 1) (just project) ∷
   arm Review.defeats (just 1) (just project) ∷ []) true
