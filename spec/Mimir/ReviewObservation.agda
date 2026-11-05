{-# OPTIONS --safe #-}
-- Database observations are the completion authority. A tool result and a
-- model's prose do not inhabit this acknowledgement contract.
module Mimir.ReviewObservation where

open import Data.Bool using (Bool; true; false)
open import Data.Integer using (ℤ; +_; _<_; _≤_)
import Data.Integer.Properties as Integer
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
open import Mimir.ExperienceSchema using (Experience)
open import Mimir.Validation
open import Mimir.Collections using (module Equality; pairEqual; atMost; checkCount)
open import Mimir.RevisionBounds using (i64Maximum)

record Snapshot : Set where
  constructor snapshot
  field
    experience : Experience
    revision reviewRevision reviewedRevision : ℤ
    candidateIDs : List (Text × ℕ)

-- Persistent revision counters are signed i64 values, not arbitrary integers.
-- Acknowledgement may lag, but cannot refer to a future source revision.
SnapshotValid : Snapshot → Set
SnapshotValid s = ((+ 0) < Snapshot.revision s) ×
  (Snapshot.revision s ≤ (+ i64Maximum) ×
  ((+ 0) ≤ Snapshot.reviewRevision s ×
  (Snapshot.reviewRevision s ≤ (+ i64Maximum) ×
  ((+ 0) ≤ Snapshot.reviewedRevision s ×
    Snapshot.reviewedRevision s ≤ Snapshot.revision s))))

checkSnapshot : ∀ s → Checked (SnapshotValid s)
checkSnapshot s = combine
  (at (key "revision") (check (fault [] staleRevision "source revision must be positive")
    ((+ 0) Integer.<? Snapshot.revision s)))
  (combine (at (key "revision") (check (fault [] staleRevision "source revision exceeds i64")
    (Snapshot.revision s Integer.≤? (+ i64Maximum))))
  (combine (at (key "review_revision") (check (fault [] staleRevision "review revision must be nonnegative")
    ((+ 0) Integer.≤? Snapshot.reviewRevision s)))
  (combine (at (key "review_revision") (check (fault [] staleRevision "review revision exceeds i64")
    (Snapshot.reviewRevision s Integer.≤? (+ i64Maximum))))
  (combine (at (key "reviewed_revision") (check (fault [] staleRevision "acknowledgement must be nonnegative")
    ((+ 0) Integer.≤? Snapshot.reviewedRevision s)))
    (at (key "reviewed_revision") (check (fault [] staleRevision "acknowledgement refers to a future source revision")
      (Snapshot.reviewedRevision s Integer.≤? Snapshot.revision s)))))))

acknowledgementNotFuture : ∀ s → SnapshotValid s → Snapshot.reviewedRevision s ≤ Snapshot.revision s
acknowledgementNotFuture s (_ , _ , _ , _ , _ , ordered) = ordered

record Pin : Set where
  constructor pin
  field identity : ℕ; project : Text; sourceRevision reviewRevision : ℤ

pinSnapshot : Snapshot → Pin
pinSnapshot s = pin (Experience.identity (Snapshot.experience s))
  (Experience.project (Snapshot.experience s)) (Snapshot.revision s) (Snapshot.reviewRevision s)

IdentityMatches : Pin → Snapshot → Set
IdentityMatches p s = Pin.identity p ≡ Experience.identity (Snapshot.experience s) ×
  Pin.project p ≡ Experience.project (Snapshot.experience s)

checkIdentity : ∀ p s → Checked (IdentityMatches p s)
checkIdentity p s = combine
  (check (fault [] wrongIdentity "completion read returned another experience")
    (Pin.identity p ≟ Experience.identity (Snapshot.experience s)))
  (check (fault [] wrongIdentity "completion read returned another project")
    (Pin.project p ≟Text Experience.project (Snapshot.experience s)))

Confirmed : Pin → Snapshot → Set
Confirmed p s = IdentityMatches p s ×
  (Snapshot.revision s ≡ Pin.sourceRevision p ×
  (Snapshot.reviewedRevision s ≡ Pin.sourceRevision p × Pin.reviewRevision p < Snapshot.reviewRevision s))

record Ack (p : Pin) (s : Snapshot) : Set where
  constructor ack
  field proof : Confirmed p s

data Observed (p : Pin) (s : Snapshot) : Set where
  confirmed : Ack p s → Observed p s
  corrected : IdentityMatches p s → Snapshot.revision s ≢ Pin.sourceRevision p → Observed p s
  pending : IdentityMatches p s → Snapshot.revision s ≡ Pin.sourceRevision p → ¬ Confirmed p s → Observed p s

inspect : (p : Pin) (s : Snapshot) → Fault ⊎ Observed p s
inspect p s with checkIdentity p s
... | rejected failure invalid = inj₁ failure
... | accepted identity with Snapshot.revision s Integer.≟ Pin.sourceRevision p
...   | no changed = inj₂ (corrected identity changed)
...   | yes same with Snapshot.reviewedRevision s Integer.≟ Pin.sourceRevision p
...     | no notReviewed = inj₂ (pending identity same (λ { (_ , _ , reviewed , _) → notReviewed reviewed }))
...     | yes reviewed with Pin.reviewRevision p Integer.<? Snapshot.reviewRevision s
...       | no notNew = inj₂ (pending identity same (λ { (_ , _ , _ , newer) → notNew newer }))
...       | yes newer = inj₂ (confirmed (ack (identity , same , reviewed , newer)))

data Receipt (p : Pin) : Set where
  unavailable : Receipt p
  malformed : Fault → Receipt p
  found : (s : Snapshot) → SnapshotValid s → Observed p s → Receipt p

observe : (p : Pin) → Maybe Snapshot → Receipt p
observe p nothing = unavailable
observe p (just s) with checkSnapshot s
... | rejected failure invalid = malformed failure
... | accepted valid with inspect p s
...   | inj₁ failure = malformed failure
...   | inj₂ result = found s valid result

confirmationRequiresNewReview : ∀ p s → Ack p s → Pin.reviewRevision p < Snapshot.reviewRevision s
confirmationRequiresNewReview p s (ack (_ , _ , _ , newer)) = newer

confirmationPinsSource : ∀ p s → Ack p s → Snapshot.revision s ≡ Pin.sourceRevision p
confirmationPinsSource p s (ack (_ , same , _)) = same

confirmationPinsIdentity : ∀ p s → Ack p s → IdentityMatches p s
confirmationPinsIdentity p s (ack (identity , _)) = identity

record Deferred : Set where
  constructor deferred
  field identity : ℕ; revision : ℤ

StillDeferred : Deferred → Snapshot → Set
StillDeferred d s = Snapshot.revision s ≡ Deferred.revision d ×
  Snapshot.reviewedRevision s < Snapshot.revision s

stillDeferred? : ∀ d s → Dec (StillDeferred d s)
stillDeferred? d s with Snapshot.revision s Integer.≟ Deferred.revision d |
  Snapshot.reviewedRevision s Integer.<? Snapshot.revision s
... | yes same | yes unreviewed = yes (same , unreviewed)
... | no different | _ = no (λ { (same , _) → different same })
... | _ | no reviewed = no (λ { (_ , unreviewed) → reviewed unreviewed })

InScope : Maybe Text → Snapshot → Set
InScope nothing s = ⊤
InScope (just project) s = Experience.project (Snapshot.experience s) ≡ project

checkScope : ∀ project s → Checked (InScope project s)
checkScope nothing s = accepted tt
checkScope (just project) s = check (fault [] wrongIdentity "pending batch returned another project")
  (Experience.project (Snapshot.experience s) ≟Text project)

BatchEntry : Maybe Text → Snapshot → Set
BatchEntry project s = SnapshotValid s × InScope project s

checkBatchEntry : ∀ project s → Checked (BatchEntry project s)
checkBatchEntry project s = combine (checkSnapshot s) (checkScope project s)

module Identities = Equality ℕ _≟_

BatchValid : ℕ → Maybe Text → List Snapshot → Set
BatchValid limit project batch = atMost limit batch ×
  (Identities.Unique (map (λ s → Experience.identity (Snapshot.experience s)) batch) ×
    All (BatchEntry project) batch)

validateBatch : ∀ limit project batch → Checked (BatchValid limit project batch)
validateBatch limit project batch = combine (checkCount limit batch)
  (combine (Identities.checkUnique (map (λ s → Experience.identity (Snapshot.experience s)) batch))
    (allChecked (checkBatchEntry project) batch))
