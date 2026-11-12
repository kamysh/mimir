{-# OPTIONS --safe #-}
-- Joint registry/node publication. Every live reservation must have a graph
-- node with the correct identity, project, kind and declaration. Retired rows
-- deliberately do not require a surviving node. Existing graph nodes survive.
module Mimir.CandidatePublication where

open import Data.Bool using (false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Mimir.UUIDGroups using (UUID)
open import Data.Integer using (ℤ)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.LearningCandidates using (Candidate; belief; patternCandidate)
import Mimir.CandidateRegistry as Registry
import Mimir.CandidateBatch as Batch
import Mimir.CandidateGraph as Graph
import Mimir.DatabaseTransaction as Database

bodyMatches : Candidate → Graph.Node → Set
bodyMatches (belief name content memory source) (Graph.beliefNode fields) =
  Graph.BeliefValues.content fields ≡ content × Graph.BeliefValues.memory fields ≡ memory
bodyMatches (belief name content memory source) (Graph.patternNode fields) = ⊥
bodyMatches (patternCandidate name situation approach) (Graph.beliefNode fields) = ⊥
bodyMatches (patternCandidate name situation approach) (Graph.patternNode fields) =
  Graph.PatternValues.situation fields ≡ situation × Graph.PatternValues.approach fields ≡ approach

record World : Set where
  constructor world
  field registry : Registry.Registry; nodes : List Graph.Node

module For (projectOf : UUID → Text) (clock : Candidate → ℤ) where
  Represents : Registry.Entry → Graph.Node → Set
  Represents row node = Graph.nodeID node ≡ Registry.Entry.nodeID row ×
    Graph.nodeProject node ≡ just (projectOf (Registry.Entry.experienceID row)) ×
    bodyMatches (Registry.Entry.declaration row) node

  Supported : List Graph.Node → Registry.Entry → Set
  Supported nodes row = Registry.Entry.retired row ≡ false → Any (Represents row) nodes

  Consistent : World → Set
  Consistent before = All (Supported (World.nodes before)) (World.registry before)

  born : ∀ experience identity declaration → Represents (Registry.entry experience declaration identity false)
    (Graph.value (Graph.creation experience identity declaration (projectOf experience) (clock declaration)))
  born experience identity (belief name content memory source) = refl , refl , refl , refl
  born experience identity (patternCandidate name situation approach) = refl , refl , refl , refl

  realize : ∀ {before occupied experience declaration} →
    Registry.Plan before occupied experience declaration → List Graph.Node → List Graph.Node
  realize (Registry.reuse row found valid) nodes = nodes
  realize {experience = experience} {declaration} (Registry.create fresh absent unused) nodes =
    Graph.value (Graph.creation experience fresh declaration (projectOf experience) (clock declaration)) ∷ nodes

  oneConsistent : ∀ {before occupied experience declaration}
    (planned : Registry.Plan before occupied experience declaration) nodes →
    All (Supported nodes) before → All (Supported (realize planned nodes)) (Registry.publish planned)
  oneConsistent (Registry.reuse row found valid) nodes consistent = consistent
  oneConsistent {experience = experience} {declaration} (Registry.create fresh absent unused) nodes consistent = (λ live → here (born experience fresh declaration)) ∷
    All.map (λ prior live → there (prior live)) consistent

  realizeBatch : ∀ {occupied experience before declarations after bindings} →
    Batch.Batch occupied experience before declarations after bindings → List Graph.Node → List Graph.Node
  realizeBatch (Batch.done before) nodes = nodes
  realizeBatch (Batch.next planned remainder) nodes = realizeBatch remainder (realize planned nodes)

  batchConsistent : ∀ {occupied experience before declarations after bindings}
    (batch : Batch.Batch occupied experience before declarations after bindings) nodes →
    All (Supported nodes) before → All (Supported (realizeBatch batch nodes)) after
  batchConsistent (Batch.done before) nodes consistent = consistent
  batchConsistent (Batch.next planned remainder) nodes consistent = batchConsistent remainder (realize planned nodes)
    (oneConsistent planned nodes consistent)

  batchRetains : ∀ {occupied experience before declarations after bindings}
    (batch : Batch.Batch occupied experience before declarations after bindings) nodes (P : Graph.Node → Set) →
    Any P nodes → Any P (realizeBatch batch nodes)
  batchRetains (Batch.done before) nodes P present = present
  batchRetains (Batch.next (Registry.reuse row found valid) remainder) nodes P present = batchRetains remainder nodes P present
  batchRetains (Batch.next (Registry.create fresh absent unused) remainder) nodes P present = batchRetains remainder _ P (there present)

  publicationPreserves : ∀ {occupied experience before declarations after bindings}
    (batch : Batch.Batch occupied experience before declarations after bindings) nodes receipt published →
    Database.Atomic (world before nodes) (world after (realizeBatch batch nodes)) receipt published →
    Consistent (world before nodes) → Consistent published
  publicationPreserves batch nodes receipt published atomic consistent = Database.invariantPreserved Consistent atomic consistent
    (batchConsistent batch nodes consistent)
