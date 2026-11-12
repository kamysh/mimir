{-# OPTIONS --safe #-}
-- Allocation preserves graph identity uniqueness across a complete batch,
-- including earlier creations in that same transaction. IDs already present
-- in the original graph and IDs newly entered in the registry are both tracked.
module Mimir.CandidateGraphUniqueness where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.All.Properties as AllProperties
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Membership.Propositional.Properties as Membership
open import Mimir.UUIDGroups using (UUID)
open import Data.Integer using (ℤ)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Mimir.Text using (Text)
open import Mimir.LearningCandidates using (Candidate)
import Mimir.CandidateRegistry as Registry
import Mimir.CandidateBatch as Batch
import Mimir.CandidateGraph as Graph
import Mimir.CandidatePublication as Publication

Known : List UUID → Registry.Registry → Graph.Node → Set
Known occupied registry node = Registry.IDs.Present (Graph.nodeID node) occupied ⊎
  Registry.IDs.Present (Graph.nodeID node) (map Registry.Entry.nodeID registry)

initiallyKnown : ∀ registry nodes → All (Known (map Graph.nodeID nodes) registry) nodes
initiallyKnown registry nodes = All.tabulate (λ member → inj₁ (Membership.∈-map⁺ Graph.nodeID member))

avoidsKnown : ∀ occupied registry fresh nodes → Registry.IDs.Absent fresh (occupied ++ map Registry.Entry.nodeID registry) →
  All (Known occupied registry) nodes → All (λ node → fresh ≢ Graph.nodeID node) nodes
avoidsKnown occupied registry fresh nodes unused known = All.map (λ { (inj₁ member) → All.lookup (AllProperties.++⁻ˡ occupied unused) member ; (inj₂ member) → All.lookup (AllProperties.++⁻ʳ occupied unused) member }) known

module For (projectOf : UUID → Text) (clock : Candidate → ℤ) where
  module P = Publication.For projectOf clock

  oneKnown : ∀ {before occupied experience declaration}
    (planned : Registry.Plan before occupied experience declaration) nodes →
    All (Known occupied before) nodes → All (Known occupied (Registry.publish planned)) (P.realize planned nodes)
  oneKnown (Registry.reuse row found valid) nodes known = known
  oneKnown {experience = experience} {declaration} (Registry.create fresh absent unused) nodes known = inj₂ (here (Graph.identityExact (Graph.creation experience fresh declaration (projectOf experience) (clock declaration)))) ∷ All.map (λ { (inj₁ member) → inj₁ member ; (inj₂ member) → inj₂ (there member) }) known

  oneUnique : ∀ {before occupied experience declaration}
    (planned : Registry.Plan before occupied experience declaration) nodes →
    All (Known occupied before) nodes → Registry.IDs.Unique (map Graph.nodeID nodes) →
    Registry.IDs.Unique (map Graph.nodeID (P.realize planned nodes))
  oneUnique (Registry.reuse row found valid) nodes known unique = unique
  oneUnique {before} {occupied} {experience} {declaration}
    (Registry.create fresh absent unused) nodes known unique
    rewrite Graph.identityExact (Graph.creation experience fresh declaration (projectOf experience) (clock declaration)) = AllProperties.map⁺ (avoidsKnown occupied before fresh nodes unused known) , unique

  batchUnique : ∀ {occupied experience before declarations after bindings}
    (batch : Batch.Batch occupied experience before declarations after bindings) nodes →
    All (Known occupied before) nodes → Registry.IDs.Unique (map Graph.nodeID nodes) →
    Registry.IDs.Unique (map Graph.nodeID (P.realizeBatch batch nodes))
  batchUnique (Batch.done before) nodes known unique = unique
  batchUnique (Batch.next planned remainder) nodes known unique = batchUnique remainder (P.realize planned nodes) (oneKnown planned nodes known) (oneUnique planned nodes known unique)

  preparedUnique : ∀ {experience before declarations after bindings} nodes →
    (batch : Batch.Batch (map Graph.nodeID nodes) experience before declarations after bindings) →
    Registry.IDs.Unique (map Graph.nodeID nodes) →
    Registry.IDs.Unique (map Graph.nodeID (P.realizeBatch batch nodes))
  preparedUnique {before = before} nodes batch unique = batchUnique batch nodes (initiallyKnown before nodes) unique
