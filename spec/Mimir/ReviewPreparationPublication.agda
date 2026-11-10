{-# OPTIONS --safe #-}
-- Joint publication of checked review rows, candidate identities/nodes and item
-- ownership, immutable assessment write expressions and review edge replacement.
-- Numeric recomputation must still extend it before it represents the complete native
-- transaction. Atomicity is never used to conceal those missing write effects.
module Mimir.ReviewPreparationPublication where

open import Data.Bool using (false)
open import Data.List using (List; map; length; _++_)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Membership.Propositional.Properties as Membership
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.Sum using (_⊎_)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapMaybe)
open import Data.Nat using (ℕ; suc; _<_)
open import Data.Integer using (ℤ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; trans)
open import Mimir.ExperienceSchema using (Experience)
open import Mimir.ReviewSchema using (Review)
import Mimir.ReviewSchema as Reviews
open import Mimir.LearningCandidates using (Candidate)
open import Mimir.RevisionBounds using (i64Maximum)
import Mimir.LearningKeys as Keys
import Mimir.LearningInput as Input
import Mimir.CandidateRegistry as Registry
import Mimir.CandidateReview as Candidates
import Mimir.CandidateGraph as Graph
import Mimir.ItemOwners as Owners
import Mimir.ItemOwnerBatch as Ownership
import Mimir.ReviewLedger as Ledger
import Mimir.ReviewPreparation as Preparation
import Mimir.DatabaseTransaction as Database
import Mimir.AssessmentWrites as Assessments
import Mimir.ReviewEdges as Edges

record World : Set where
  constructor world
  field
    ledger : Ledger.World
    registry : Registry.Registry
    owners : Owners.Registry
    nodes : List Graph.Node
    assessments : List Assessments.Row
    edges : List Edges.Edge

LedgerAndIdentityValid : World → Set
LedgerAndIdentityValid before = Ledger.Consistent (World.ledger before) ×
  Registry.IDs.Unique (map Graph.nodeID (World.nodes before))

module WithOriginal (original : Maybe Input.Review) (before : World) (current : Experience) (requested : Review)
  (clock : Candidate → ℤ)
  (unique : Registry.IDs.Unique (map Graph.nodeID (World.nodes before))) where

  module Submitted = Ledger.Submitted original

  identity = Experience.identity current
  state = Ledger.World.cells (World.ledger before) identity
  prior = mapMaybe Ledger.Version.applied
    (Ledger.head (Ledger.World.histories (World.ledger before) identity))
  input : Preparation.Input
  input = Preparation.input current (Ledger.R.Cell.current state) prior
    (World.registry before) (World.owners before) (World.nodes before) unique
  module P = Preparation.For input requested clock

  -- The caller must obtain current from the locked database snapshot. Source
  -- and request identity are checked inside P; this guard also aligns project,
  -- CAS revision, replay classification and the bounded persistent counter.
  record Fresh (expected : ℕ) : Set where
    constructor fresh
    field
      projectMatches : Experience.project current ≡ Ledger.R.Cell.project state
      expectedMatches : expected ≡ Ledger.R.Cell.review state
      notReplay : Ledger.R.replay state expected (Ledger.submissionKey requested original) ≡ false
      room : expected < i64Maximum
      preparation : P.Prepared

  assessmentRows : ∀ {expected} → Fresh expected → List Assessments.Row
  assessmentRows selected = Assessments.writes identity (suc (Ledger.R.Cell.review state))
    (Review.assessments (P.materialized (Fresh.preparation selected)))
    (P.materializedTargetsResolved (Fresh.preparation selected))

  publish : ∀ {expected} → Fresh expected → World
  publish selected = world
    (Submitted.append identity (World.ledger before) requested (P.materialized (Fresh.preparation selected)))
    (Candidates.Prepared.after (P.Prepared.reservation (Fresh.preparation selected)))
    (P.Prepared.afterOwners (Fresh.preparation selected))
    (P.proposedNodes (P.Prepared.reservation (Fresh.preparation selected)))
    (assessmentRows selected ++ World.assessments before)
    (Edges.replace identity (Review.links (P.materialized (Fresh.preparation selected))) (World.edges before))

  publicationValid : ∀ {expected} (selected : Fresh expected) → Ledger.Consistent (World.ledger before) →
    LedgerAndIdentityValid (publish selected)
  publicationValid selected consistent = Submitted.appendConsistent identity (World.ledger before) requested
    (P.materialized (Fresh.preparation selected)) consistent
    ,
    P.proposedUnique
    (P.Prepared.reservation (Fresh.preparation selected))

  activeIsPrepared : ∀ {expected} (selected : Fresh expected) →
    Ledger.activeApplied (Ledger.World.cells (World.ledger (publish selected)) identity)
      (Ledger.World.histories (World.ledger (publish selected)) identity) ≡
    just (P.materialized (Fresh.preparation selected))
  activeIsPrepared selected = Submitted.appendSelectsApplied identity (World.ledger before)
    requested (P.materialized (Fresh.preparation selected))

  priorOwnershipPreserved : ∀ {expected} (selected : Fresh expected) key old →
    World.owners before key ≡ just old → World.owners (publish selected) key ≡ just old
  priorOwnershipPreserved selected key old original = Ownership.batchPreserves
    (P.Prepared.ownershipPlan (Fresh.preparation selected)) key old
    original

  extractedOwnership : ∀ {expected} (selected : Fresh expected) →
    All (Ownership.Owns (Review.experienceID requested) (World.owners (publish selected))) (Review.extracted requested)
  extractedOwnership selected = P.extractedOwnership (Fresh.preparation selected)

  atomicPublicationValid : ∀ {expected} (selected : Fresh expected) receipt published →
    Database.Atomic before (publish selected) receipt published → LedgerAndIdentityValid before →
    LedgerAndIdentityValid published
  atomicPublicationValid selected receipt published atomic valid = Database.invariantPreserved LedgerAndIdentityValid atomic valid
    (publicationValid selected (proj₁ valid))

  assessmentRowsOwned : ∀ {expected} (selected : Fresh expected) →
    All (Assessments.Owned identity (suc (Ledger.R.Cell.review state))) (assessmentRows selected)
  assessmentRowsOwned selected = Assessments.allOwned identity (suc (Ledger.R.Cell.review state))
    (Review.assessments (P.materialized (Fresh.preparation selected)))
    (P.materializedTargetsResolved (Fresh.preparation selected))

  assessmentCountExact : ∀ {expected} (selected : Fresh expected) →
    length (assessmentRows selected) ≡ length (Review.assessments requested)
  assessmentCountExact selected = trans
    (Assessments.countExact identity (suc (Ledger.R.Cell.review state))
     (Review.assessments (P.materialized (Fresh.preparation selected)))
     (P.materializedTargetsResolved (Fresh.preparation selected)))
    (Candidates.assessmentsPreserved
     (P.Prepared.reservation (Fresh.preparation selected)))

  assessmentPayloadsExact : ∀ {expected} (selected : Fresh expected) →
    map Assessments.Row.payload (assessmentRows selected) ≡ Review.assessments (P.materialized (Fresh.preparation selected))
  assessmentPayloadsExact selected = Assessments.payloadsExact identity
    (suc (Ledger.R.Cell.review state))
    (Review.assessments (P.materialized (Fresh.preparation selected)))
    (P.materializedTargetsResolved (Fresh.preparation selected))

  assessmentKeysUnique : ∀ {expected} (selected : Fresh expected) →
    Reviews.AssessmentKeys.Unique (map Assessments.key (assessmentRows selected))
  assessmentKeysUnique selected = Assessments.uniqueKeys identity (suc (Ledger.R.Cell.review state))
    (Review.assessments (P.materialized (Fresh.preparation selected)))
    (P.materializedTargetsResolved (Fresh.preparation selected))
    (P.materializedKeysUnique (Fresh.preparation selected))

  unrelatedEdgesPreserved : ∀ {expected} (selected : Fresh expected) e →
    e ∈ World.edges before → Edges.Foreign identity e → e ∈ World.edges (publish selected)
  unrelatedEdgesPreserved selected e member foreign = Membership.∈-++⁺ʳ
    (Edges.creations identity
     (Review.links (P.materialized (Fresh.preparation selected))))
    (Edges.foreignPreserved identity (World.edges before) e member
     foreign)

  declaredEdgesPresent : ∀ {expected} (selected : Fresh expected) declaration →
    declaration ∈ Review.links (P.materialized (Fresh.preparation selected)) →
    Edges.forward identity declaration ∈ World.edges (publish selected)
  declaredEdgesPresent selected declaration member = Membership.∈-++⁺ˡ
    (Edges.everyDeclaredLink identity
     (Review.links (P.materialized (Fresh.preparation selected)))
     declaration member)

  contradictionEdgesPresent : ∀ {expected} (selected : Fresh expected) declaration →
    declaration ∈ Review.links (P.materialized (Fresh.preparation selected)) →
    Reviews.Link.relation declaration ≡ Reviews.contradicts →
    Edges.reverse identity declaration ∈ World.edges (publish selected)
  contradictionEdgesPresent selected declaration member relation = Membership.∈-++⁺ˡ
    (Edges.everyContradictionReversed identity
     (Review.links (P.materialized (Fresh.preparation selected)))
     declaration member relation)

  publishedEdgeProvenance : ∀ {expected} (selected : Fresh expected) →
    All (λ e → Any (λ declaration → Edges.Generated identity declaration e)
      (Review.links (P.materialized (Fresh.preparation selected))) ⊎ Edges.Foreign identity e)
      (World.edges (publish selected))
  publishedEdgeProvenance selected = Edges.replacementProvenance identity
    (Review.links (P.materialized (Fresh.preparation selected)))
    (World.edges before)

-- Canonical-only callers keep their existing interface. Registered review
-- publication uses WithOriginal with the actual pre-allocation request.
module For (before : World) (current : Experience) (requested : Review)
  (clock : Candidate → ℤ)
  (unique : Registry.IDs.Unique (map Graph.nodeID (World.nodes before))) where
  open WithOriginal nothing before current requested clock unique public
