{-# OPTIONS --safe #-}
-- Assessment-row foreign keys and cross-revision isolation. Historical rows
-- remain immutable; replacing the active review pointer does not delete them
-- or permit a fresh review to reuse an older assessment primary key.
module Mimir.AssessmentHistory where

open import Data.List using (List; map)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Membership.Propositional.Properties as Membership
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.All.Properties as AllProperties
open import Data.Nat using (ℕ; suc; _≤_; _≟_)
import Data.Nat.Properties as Nat
open import Data.Integer using (ℤ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst; trans)
open import Mimir.ExperienceSchema using (Experience)
open import Mimir.ReviewSchema using (Review)
open import Mimir.LearningCandidates using (Candidate)
import Mimir.AssessmentWrites as Writes
import Mimir.ReviewLedger as Ledger
import Mimir.CandidateRegistry as Registry
import Mimir.CandidateGraph as Graph
import Mimir.ReviewPreparationPublication as Publication

orderedBound : ∀ {revision entries} → Ledger.J.Ordered revision entries → ∀ entry →
  entry ∈ entries → Ledger.J.Entry.revision entry ≤ revision
orderedBound (Ledger.J.newest same previous) entry (here refl) = Nat.≤-reflexive same
orderedBound (Ledger.J.newest same previous) entry (there member) = Nat.m≤n⇒m≤1+n (orderedBound previous entry member)

References : Ledger.World → Writes.Row → Set
References ledger contribution = Σ Ledger.Version (λ entry →
  entry ∈ Ledger.World.histories ledger (Writes.Row.experience contribution) ×
  (Ledger.Version.revision entry ≡ Writes.Row.revision contribution ×
    Writes.Row.payload contribution ∈ Review.assessments (Ledger.Version.applied entry)))

revisionBound : ∀ ledger contribution → Ledger.Consistent ledger → References ledger contribution →
  Writes.Row.revision contribution ≤ Ledger.R.Cell.review (Ledger.World.cells ledger (Writes.Row.experience contribution))
revisionBound ledger contribution consistent (entry , member , same , payload) = subst
  (λ revision →
     revision ≤
     Ledger.R.Cell.review
     (Ledger.World.cells ledger (Writes.Row.experience contribution)))
  same
  (orderedBound
   (proj₁ (consistent (Writes.Row.experience contribution)))
   (Ledger.requestEntry entry)
   (Membership.∈-map⁺ Ledger.requestEntry member))

freshRevisionDifferent : ∀ ledger contribution identity → Ledger.Consistent ledger → References ledger contribution →
  Writes.Row.experience contribution ≡ identity →
  Writes.Row.revision contribution ≢ suc (Ledger.R.Cell.review (Ledger.World.cells ledger identity))
freshRevisionDifferent ledger contribution identity consistent reference owner same = Nat.n≮n (Ledger.R.Cell.review (Ledger.World.cells ledger identity))
  (subst
   (λ revision →
      revision ≤
      Ledger.R.Cell.review (Ledger.World.cells ledger identity))
   same
   (subst
    (λ identity →
       Writes.Row.revision contribution ≤
       Ledger.R.Cell.review (Ledger.World.cells ledger identity))
    owner (revisionBound ledger contribution consistent reference)))

allHistoryRetained : ∀ identity ledger requested applied other entry →
  entry ∈ Ledger.World.histories ledger other →
  entry ∈ Ledger.World.histories (Ledger.append identity ledger requested applied) other
allHistoryRetained identity ledger requested applied other entry member with other ≟ identity
... | yes refl = there member
... | no different = member

oldReferenceRetained : ∀ identity ledger requested applied contribution → References ledger contribution →
  References (Ledger.append identity ledger requested applied) contribution
oldReferenceRetained identity ledger requested applied contribution (entry , member , same , payload) = entry ,
  allHistoryRetained identity ledger requested applied
  (Writes.Row.experience contribution) entry member
  , same , payload

module For (before : Publication.World) (current : Experience) (requested : Review)
  (clock : Candidate → ℤ)
  (unique : Registry.IDs.Unique (map Graph.nodeID (Publication.World.nodes before)))
  {expected : ℕ} (selected : Publication.For.Fresh before current requested clock unique expected) where

  module F = Publication.For before current requested clock unique
  applied = F.P.materialized (F.Fresh.preparation selected)
  after = F.publish selected
  entry = Ledger.next F.identity (Publication.World.ledger before) requested applied

  versionStored : entry ∈ Ledger.World.histories (Publication.World.ledger after) F.identity
  versionStored = subst (λ rows → entry ∈ rows)
    (sym
     (Ledger.installedHistory F.identity
      (Publication.World.ledger before) requested applied))
    (here refl)

  newReference : ∀ contribution → Writes.Owned F.identity (suc (Ledger.R.Cell.review F.state)) contribution →
    Writes.Row.payload contribution ∈ Review.assessments applied → References (Publication.World.ledger after) contribution
  newReference contribution (owner , revision , target , calculated) payload = entry ,
    subst
    (λ identity →
       entry ∈
       Ledger.World.histories (Publication.World.ledger after) identity)
    (sym owner) versionStored
    , sym revision , payload

  newReferences : All (References (Publication.World.ledger after)) (F.assessmentRows selected)
  newReferences = All.tabulate
    (λ {contribution} member →
       newReference contribution
       (All.lookup (F.assessmentRowsOwned selected) member)
       (subst
        (λ assessments → Writes.Row.payload contribution ∈ assessments)
        (F.assessmentPayloadsExact selected)
        (Membership.∈-map⁺ Writes.Row.payload member)))

  allReferences : All (References (Publication.World.ledger before)) (Publication.World.assessments before) →
    All (References (Publication.World.ledger after)) (Publication.World.assessments after)
  allReferences existing = AllProperties.++⁺ newReferences
    (All.map
     (λ {contribution} reference →
        oldReferenceRetained F.identity (Publication.World.ledger before)
        requested applied contribution reference)
     existing)

  newRevisionCannotCollide : ∀ newer older → newer ∈ F.assessmentRows selected →
    older ∈ Publication.World.assessments before →
    Ledger.Consistent (Publication.World.ledger before) →
    All (References (Publication.World.ledger before)) (Publication.World.assessments before) →
    Writes.Row.experience newer ≡ Writes.Row.experience older →
    Writes.Row.revision newer ≢ Writes.Row.revision older
  newRevisionCannotCollide newer older newMember oldMember consistent references sameOwner sameRevision
    with All.lookup (F.assessmentRowsOwned selected) newMember
  ... | (owner , revision , target , calculated) = freshRevisionDifferent (Publication.World.ledger before) older
    F.identity consistent (All.lookup references oldMember)
    (trans (sym sameOwner) owner) (trans (sym sameRevision) revision)
