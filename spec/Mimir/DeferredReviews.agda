{-# OPTIONS --safe #-}
-- Reconcile durable deferrals against fresh, identity-checked database reads.
-- A changed, reviewed, deleted, or out-of-scope record is not excluded again.
module Mimir.DeferredReviews where

open import Data.List using (List; []; _∷_; map; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤_; z≤n; s≤s; _≟_)
open import Data.Nat.Properties using (m≤n⇒m≤1+n; ≤-trans)
open import Data.Integer using (+_)
import Data.Integer.Properties as Integer
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Mimir.Text using (Text)
open import Mimir.UUIDGroups using (UUID; _≟UUID_)
open import Mimir.Validation
open import Mimir.RecordDecoding using (_>>=_)
open import Mimir.Collections using (module Equality; atMost; checkCount)
open import Mimir.RevisionBounds using (i64Maximum)
open import Mimir.ExperienceSchema using (Experience)
import Mimir.ReviewObservation as Observation
open Observation using (Deferred; Snapshot; SnapshotValid; checkSnapshot; InScope; checkScope)

module IDs = Equality UUID _≟UUID_

Valid : Deferred → Set
Valid d = ((+ 0) Data.Integer.< Deferred.revision d) ×
  (Deferred.revision d Data.Integer.≤ (+ i64Maximum))

validate : ∀ d → Checked (Valid d)
validate d = combine
  (check (fault [] staleRevision "deferred source revision must be positive") ((+ 0) Integer.<? Deferred.revision d))
  (check (fault [] staleRevision "deferred source revision exceeds i64") (Deferred.revision d Integer.≤? (+ i64Maximum)))

ListValid : List Deferred → Set
ListValid ds = atMost 1000 ds × (All Valid ds × IDs.Unique (map Deferred.identity ds))

validateList : ∀ ds → Checked (ListValid ds)
validateList ds = combine (checkCount 1000 ds)
  (combine (allChecked validate ds) (IDs.checkUnique (map Deferred.identity ds)))

Identity : Deferred → Snapshot → Set
Identity d s = Deferred.identity d ≡ Experience.identity (Snapshot.experience s)

checkIdentity : ∀ d s → Checked (Identity d s)
checkIdentity d s = check (fault [] wrongIdentity "deferred lookup returned another experience")
  (Deferred.identity d ≟UUID Experience.identity (Snapshot.experience s))

record Keep (scope : Maybe Text) (d : Deferred) (s : Snapshot) : Set where
  constructor keepProof
  field
    valid : SnapshotValid s
    identity : Identity d s
    inScope : InScope scope s
    sameRevision : Snapshot.revision s ≡ Deferred.revision d
    unreviewed : Snapshot.reviewedRevision s Data.Integer.< Snapshot.revision s

data Drop (scope : Maybe Text) (d : Deferred) : Maybe Snapshot → Set where
  deleted : Drop scope d nothing
  outside : ∀ s → SnapshotValid s → Identity d s → ¬ InScope scope s → Drop scope d (just s)
  changed : ∀ s → SnapshotValid s → Identity d s → Snapshot.revision s ≢ Deferred.revision d → Drop scope d (just s)
  reviewed : ∀ s → SnapshotValid s → Identity d s → Snapshot.reviewedRevision s ≡ Snapshot.revision s → Drop scope d (just s)

data Decision (scope : Maybe Text) (d : Deferred) : Maybe Snapshot → Set where
  keep : (s : Snapshot) → Keep scope d s → Decision scope d (just s)
  drop : ∀ {observed} → Drop scope d observed → Decision scope d observed

decideValid : ∀ scope d s → SnapshotValid s → Identity d s → Decision scope d (just s)
decideValid scope d s valid identity with checkScope scope s
... | rejected failure outsideScope = drop (outside s valid identity outsideScope)
... | accepted inScope with Snapshot.revision s Integer.≟ Deferred.revision d
...   | no different = drop (changed s valid identity different)
...   | yes same with Snapshot.reviewedRevision s Integer.<? Snapshot.revision s
...     | yes unreviewed = keep s (keepProof valid identity inScope same unreviewed)
...     | no alreadyReviewed = drop (reviewed s valid identity
  (Integer.≤∧≮⇒≡ (Observation.acknowledgementNotFuture s valid) alreadyReviewed))

reconcileOne : ∀ scope d observed → Fault ⊎ Decision scope d observed
reconcileOne scope d nothing = inj₂ (drop deleted)
reconcileOne scope d (just s) = result (checkSnapshot s) >>= λ valid →
  result (checkIdentity d s) >>= λ identity → inj₂ (decideValid scope d s valid identity)

Reads = Deferred → Fault ⊎ Maybe Snapshot

data Reconciled (scope : Maybe Text) (read : Reads) : List Deferred → List Deferred → Set where
  empty : Reconciled scope read [] []
  held : ∀ {d rest after s} → read d ≡ inj₂ (just s) → Keep scope d s → Reconciled scope read rest after →
    Reconciled scope read (d ∷ rest) (d ∷ after)
  removed : ∀ {d rest after observed} → read d ≡ inj₂ observed → Drop scope d observed → Reconciled scope read rest after →
    Reconciled scope read (d ∷ rest) after

Result : Maybe Text → Reads → List Deferred → Set
Result scope read before = Σ[ after ∈ List Deferred ] Reconciled scope read before after

reconcile : ∀ scope before read → Fault ⊎ Result scope read before
reconcile scope [] read = inj₂ ([] , empty)
reconcile scope (d ∷ rest) read with read d in received
... | inj₁ failure = inj₁ failure
... | inj₂ observed = reconcileOne scope d observed >>= λ decision →
  reconcile scope rest read >>= λ where
    (after , proof) → inj₂ (finish decision after proof)
  where
  finish : Decision scope d observed → (after : List Deferred) → Reconciled scope read rest after → Result scope read (d ∷ rest)
  finish (keep s kept) after proof = d ∷ after , held received kept proof
  finish (drop dropped) after proof = after , removed received dropped proof

countDoesNotGrow : ∀ {scope read before after} → Reconciled scope read before after → length after ≤ length before
countDoesNotGrow empty = z≤n
countDoesNotGrow (held received kept rest) = s≤s (countDoesNotGrow rest)
countDoesNotGrow (removed received dropped rest) = m≤n⇒m≤1+n (countDoesNotGrow rest)

everyExclusionHasEvidence : ∀ {scope read before after} → Reconciled scope read before after →
  All (λ d → Σ[ s ∈ Snapshot ] (read d ≡ inj₂ (just s) × Keep scope d s)) after
everyExclusionHasEvidence empty = []
everyExclusionHasEvidence (held {s = s} received kept rest) = (s , received , kept) ∷ everyExclusionHasEvidence rest
everyExclusionHasEvidence (removed received dropped rest) = everyExclusionHasEvidence rest

retainsAll : ∀ {scope read before after} {P : Deferred → Set} →
  Reconciled scope read before after → All P before → All P after
retainsAll empty [] = []
retainsAll (held received kept rest) (proof ∷ proofs) = proof ∷ retainsAll rest proofs
retainsAll (removed received dropped rest) (proof ∷ proofs) = retainsAll rest proofs

absentIDsPreserved : ∀ {scope read before after identity} → Reconciled scope read before after →
  IDs.Absent identity (map Deferred.identity before) → IDs.Absent identity (map Deferred.identity after)
absentIDsPreserved empty [] = []
absentIDsPreserved (held received kept rest) (different ∷ proofs) = different ∷ absentIDsPreserved rest proofs
absentIDsPreserved (removed received dropped rest) (different ∷ proofs) = absentIDsPreserved rest proofs

uniqueIDsPreserved : ∀ {scope read before after} → Reconciled scope read before after →
  IDs.Unique (map Deferred.identity before) → IDs.Unique (map Deferred.identity after)
uniqueIDsPreserved empty unique = tt
uniqueIDsPreserved (held received kept rest) (absent , unique) = absentIDsPreserved rest absent , uniqueIDsPreserved rest unique
uniqueIDsPreserved (removed received dropped rest) (absent , unique) = uniqueIDsPreserved rest unique

validOutput : ∀ {scope read before after} → Reconciled scope read before after → ListValid before → ListValid after
validOutput proof (bounded , valid , unique) =
  ≤-trans (countDoesNotGrow proof) bounded , retainsAll proof valid , uniqueIDsPreserved proof unique

checkedReconcile : ∀ scope before read →
  Fault ⊎ (Σ[ after ∈ List Deferred ] (Reconciled scope read before after × ListValid after))
checkedReconcile scope before read = result (validateList before) >>= λ valid →
  reconcile scope before read >>= λ where
    (after , proof) → inj₂ (after , proof , validOutput proof valid)

eligibleCannotDrop : ∀ {scope d s} → Keep scope d s → Drop scope d (just s) → ⊥
eligibleCannotDrop kept (outside s valid identity notInScope) = notInScope (Keep.inScope kept)
eligibleCannotDrop kept (changed s valid identity different) = different (Keep.sameRevision kept)
eligibleCannotDrop kept (reviewed s valid identity equality) = Integer.<-irrefl equality (Keep.unreviewed kept)
