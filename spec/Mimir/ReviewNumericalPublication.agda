{-# OPTIONS --safe #-}
-- Complete review publication includes recomputed posteriors. Failed numeric
-- preparation supplies no proposed world to commit. Replay never recomputes.
module Mimir.ReviewNumericalPublication where

open import Data.Float.Base using (Float)
open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ)
open import Data.Integer using (ℤ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Mimir.ExperienceSchema using (Experience)
open import Mimir.ReviewSchema using (Review; Link; Relation; contradicts; supports; causes; defeats)
open import Mimir.LearningCandidates using (Candidate)
import Mimir.Validation as Validation
import Mimir.CandidateGraph as Graph
import Mimir.CandidateRegistry as Registry
import Mimir.ReviewResolution as Resolution
import Mimir.ReviewLedger as Ledger
import Mimir.ReviewPlanning as Planning
import Mimir.ReviewPreparationPublication as Publication
import Mimir.LearningRecompute as Recompute
import Mimir.PosteriorComputation as Posterior

linkTargets : List Link → List ℕ
linkTargets [] = []
linkTargets (l ∷ ls) with Link.relation l
... | contradicts = linkTargets ls
... | supports = Link.to l ∷ linkTargets ls
... | causes = Link.to l ∷ linkTargets ls
... | defeats = Link.to l ∷ linkTargets ls

targets : Review → List ℕ
targets r = map Mimir.ReviewSchema.Feedback.beliefID (Review.feedbacks r) ++ linkTargets (Review.links r)

oldTargets : Maybe Review → List ℕ
oldTargets nothing = []
oldTargets (just r) = targets r

data NumericFailure : Set where
  foreignTarget invalidInput invalidWrite : NumericFailure
  numericalDecision : Posterior.State → List Posterior.State → NumericFailure

module For (calculator : Posterior.Calculator) (before : Publication.World) (current : Experience) (requested : Review)
  (clock : Candidate → ℤ)
  (unique : Registry.IDs.Unique (map Graph.nodeID (Publication.World.nodes before)))
  (expected : ℕ) (experienceIDs : List ℕ) (ground : List (ℕ × Float)) where

  module P = Planning.For before current requested clock unique expected
  module F = P.F

  data Decision : Set where
    refused : Validation.Fault → Decision
    numericFailure : NumericFailure → Decision
    replay : P.Replayed → Decision
    fresh : (selected : F.Fresh expected) → (nodes : List Graph.Node) →
      (map Graph.nodeID nodes ≡ map Graph.nodeID (Publication.World.nodes (F.publish selected))) →
      Bool → Decision

  -- The identity proof is about the actual calculated node list, not a
  -- caller-supplied assertion that numeric code preserves graph identity.
  complete : (selected : F.Fresh expected) → Decision
  complete selected with Recompute.run calculator project roots
    (Publication.World.nodes staged) (Publication.World.edges staged)
    (Recompute.activeReviews project experienceIDs (Publication.World.ledger staged)) ground
    in calculated
    where
    staged = F.publish selected
    project = Experience.project current
    roots = oldTargets F.prior ++ targets (F.P.materialized (F.Fresh.preparation selected))
  ... | Recompute.foreignTarget = numericFailure foreignTarget
  ... | Recompute.invalidNumericInput = numericFailure invalidInput
  ... | Recompute.invalidNumericWrite = numericFailure invalidWrite
  ... | Recompute.needsDecision counts history = numericFailure (numericalDecision counts history)
  ... | Recompute.recomputed nodes limit = fresh selected nodes (Recompute.runPreservesIdentities calculator (Experience.project current)
     (oldTargets F.prior ++
      targets (F.P.materialized (F.Fresh.preparation selected)))
     (Publication.World.nodes (F.publish selected))
     (Publication.World.edges (F.publish selected))
     (Recompute.activeReviews (Experience.project current) experienceIDs
      (Publication.World.ledger (F.publish selected)))
     ground nodes limit calculated) limit

  plan : (Candidate → ℕ) → Decision
  plan identities with P.plan identities
  ... | P.refused failure = refused failure
  ... | P.replay receipt = replay receipt
  ... | P.fresh selected = complete selected

  proposed : Decision → Publication.World
  proposed (refused failure) = before
  proposed (numericFailure failure) = before
  proposed (replay receipt) = before
  proposed (fresh selected nodes same limit) = record (F.publish selected) { nodes = nodes }

  preservesIdentity : ∀ selected nodes same limit →
    Registry.IDs.Unique (map Graph.nodeID (Publication.World.nodes (proposed (fresh selected nodes same limit))))
  preservesIdentity selected nodes same limit = subst Registry.IDs.Unique (sym same)
    (F.P.proposedUnique (F.P.Prepared.reservation (F.Fresh.preparation selected)))

  numericFailureCannotPublish : ∀ failure → proposed (numericFailure failure) ≡ before
  numericFailureCannotPublish failure = refl

  replayCannotPublish : ∀ receipt → proposed (replay receipt) ≡ before
  replayCannotPublish receipt = refl
