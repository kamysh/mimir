{-# OPTIONS --safe #-}
-- Candidate conflict retries and durable exclusion are different decisions.
-- Corrections remain available after every conflict; persisting
-- an exclusion additionally requires a fresh unchanged/unreviewed observation.
module Mimir.CandidateDeferral where

open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Integer using (_<_)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Validation using (Fault)
open import Mimir.ReviewObservation using (Pin; Deferred; deferred; Snapshot)
import Mimir.DeferredReviews as DeferredReviews

data Conflicts : Set where
  none : Conflicts
  conflict : Fault → Conflicts → Conflicts

recordConflict : Conflicts → Fault → Conflicts
recordConflict history detail = conflict detail history

count : Conflicts → ℕ
count none = 0
count (conflict detail history) = suc (count history)

allConflictsCounted : ∀ history detail → count (recordConflict history detail) ≡ suc (count history)
allConflictsCounted history detail = refl

data Seen : Conflicts → Set where
  present : ∀ detail history → Seen (conflict detail history)

data Next : Set where correct : Next
nextConflict : Conflicts → Fault → Next
nextConflict history detail = correct

data End : Set where
  backendFailure modelDone toolFailure traceFailure userStopped resolved : End

canDefer : End → Bool
canDefer backendFailure = true
canDefer modelDone = true
canDefer toolFailure = false
canDefer traceFailure = false
canDefer userStopped = false
canDefer resolved = false

record Request (selected : Pin) (history : Conflicts) (ending : End) : Set where
  constructor request
  field conflictObserved : Seen history; policyAllows : canDefer ending ≡ true

propose : ∀ selected history ending → Maybe (Request selected history ending)
propose selected none ending = nothing
propose selected (conflict detail history) ending with canDefer ending in allowed
... | false = nothing
... | true = just (request (present detail history) allowed)

source : Pin → Deferred
source selected = deferred (Pin.identity selected) (Pin.sourceRevision selected)

record Persistable (selected : Pin) (history : Conflicts) (ending : End) : Set where
  constructor persistable
  field
    proposal : Request selected history ending
    observed : Snapshot
    current : DeferredReviews.Keep (just (Pin.project selected)) (source selected) observed

-- Nothing means that the source was deleted, changed, reviewed, or left this
-- project. A read/decoding failure remains an error and cannot create a hold.
verify : ∀ {selected history ending} → Request selected history ending →
  Fault ⊎ Maybe Snapshot → Fault ⊎ Maybe (Persistable selected history ending)
verify proposal (inj₁ failure) = inj₁ failure
verify {selected} proposal (inj₂ observed) with DeferredReviews.reconcileOne
  (just (Pin.project selected)) (source selected) observed
... | inj₁ failure = inj₁ failure
... | inj₂ (DeferredReviews.drop reason) = inj₂ nothing
... | inj₂ (DeferredReviews.keep current kept) = inj₂ (just (persistable proposal current kept))

persistedRevisionUnchanged : ∀ {selected history ending} (p : Persistable selected history ending) →
  Mimir.ReviewObservation.Snapshot.revision (Persistable.observed p) ≡ Pin.sourceRevision selected
persistedRevisionUnchanged p = DeferredReviews.Keep.sameRevision (Persistable.current p)

persistedStillUnreviewed : ∀ {selected history ending} (p : Persistable selected history ending) →
  Mimir.ReviewObservation.Snapshot.reviewedRevision (Persistable.observed p) <
    Mimir.ReviewObservation.Snapshot.revision (Persistable.observed p)
persistedStillUnreviewed p = DeferredReviews.Keep.unreviewed (Persistable.current p)

noConflictCannotDefer : ∀ selected ending → propose selected none ending ≡ nothing
noConflictCannotDefer selected ending = refl
