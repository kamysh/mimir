{-# OPTIONS --safe #-}
-- Candidate conflict retries and durable exclusion are different decisions.
-- Existing runner policy permits a bounded correction opportunity; persisting
-- an exclusion additionally requires a fresh unchanged/unreviewed observation.
module Mimir.CandidateDeferral where

open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤_; z≤n; s≤s)
open import Data.Integer using (_<_)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Validation using (Fault)
open import Mimir.ReviewObservation using (Pin; Deferred; deferred; Snapshot)
import Mimir.DeferredReviews as DeferredReviews

data Conflicts : Set where
  none : Conflicts
  once : Fault → Conflicts
  twice : Fault → Fault → Conflicts

recordConflict : Conflicts → Fault → Conflicts
recordConflict none detail = once detail
recordConflict (once first) detail = twice first detail
recordConflict (twice first second) detail = twice first second

count : Conflicts → ℕ
count none = 0
count (once first) = 1
count (twice first second) = 2

countBounded : ∀ history → count history ≤ 2
countBounded none = z≤n
countBounded (once first) = s≤s z≤n
countBounded (twice first second) = s≤s (s≤s z≤n)

data Seen : Conflicts → Set where
  one : ∀ detail → Seen (once detail)
  two : ∀ first second → Seen (twice first second)

data Next : Set where correctOnce inspectDeferral : Next

nextConflict : Conflicts → Fault → Next
nextConflict none detail = correctOnce
nextConflict (once first) detail = inspectDeferral
nextConflict (twice first second) detail = inspectDeferral

-- These distinctions reflect current runner behavior. In particular a
-- malformed tool attempt exhausting its budget remains a failure even after
-- a candidate conflict; a provider limit/error after a conflict can defer it.
data End : Set where
  modelLimit toolLimit backendFailure backendTimeout modelDone conflictLimit
    malformedToolLimit toolFailure traceFailure userStopped resolved : End

canDefer : End → Bool
canDefer modelLimit = true
canDefer toolLimit = true
canDefer backendFailure = true
canDefer backendTimeout = true
canDefer modelDone = true
canDefer conflictLimit = true
canDefer malformedToolLimit = false
canDefer toolFailure = false
canDefer traceFailure = false
canDefer userStopped = false
canDefer resolved = false

record Request (selected : Pin) (history : Conflicts) (ending : End) : Set where
  constructor request
  field conflictObserved : Seen history; policyAllows : canDefer ending ≡ true

propose : ∀ selected history ending → Maybe (Request selected history ending)
propose selected none ending = nothing
propose selected (once detail) ending with canDefer ending in allowed
... | false = nothing
... | true = just (request (one detail) allowed)
propose selected (twice first second) ending with canDefer ending in allowed
... | false = nothing
... | true = just (request (two first second) allowed)

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
