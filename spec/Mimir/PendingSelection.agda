{-# OPTIONS --safe #-}
module Mimir.PendingSelection where

open import Data.List using (List; map)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ; _≟_)
open import Data.Integer using (_<_)
import Data.Integer.Properties as Integer
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Mimir.Text using (Text)
open import Mimir.Validation
open import Mimir.Collections using (module Equality)
open import Mimir.ExperienceSchema using (Experience)
import Mimir.ReviewObservation as Observation

module IDs = Equality ℕ _≟_

identity : Observation.Snapshot → ℕ
identity s = Experience.identity (Observation.Snapshot.experience s)

Pending : Observation.Snapshot → Set
Pending s = Observation.Snapshot.reviewedRevision s < Observation.Snapshot.revision s

Eligible : List ℕ → Observation.Snapshot → Set
Eligible excluded s = Pending s × IDs.Absent (identity s) excluded

checkEligible : ∀ excluded s → Checked (Eligible excluded s)
checkEligible excluded s = combine
  (check (fault Data.List.[] staleRevision "pending selection returned an already reviewed source revision")
    (Observation.Snapshot.reviewedRevision s Integer.<? Observation.Snapshot.revision s))
  (check (fault Data.List.[] wrongIdentity "pending selection returned an excluded experience")
    (IDs.absent? (identity s) excluded))

Valid : ℕ → Maybe Text → List ℕ → List Observation.Snapshot → Set
Valid limit scope excluded batch = Observation.BatchValid limit scope batch × All (Eligible excluded) batch

validate : ∀ limit scope excluded batch → Checked (Valid limit scope excluded batch)
validate limit scope excluded batch = combine (Observation.validateBatch limit scope batch)
  (allChecked (checkEligible excluded) batch)

everySelectedIsPending : ∀ {limit scope excluded batch} → Valid limit scope excluded batch → All Pending batch
everySelectedIsPending (batchValid , eligible) = All.map proj₁ eligible

noSelectedIsExcluded : ∀ {limit scope excluded batch} → Valid limit scope excluded batch →
  All (λ s → IDs.Absent (identity s) excluded) batch
noSelectedIsExcluded (batchValid , eligible) = All.map proj₂ eligible

excludedNeverEligible : ∀ excluded s → IDs.Present (identity s) excluded → Eligible excluded s → ⊥
excludedNeverEligible excluded s present (pending , absent) = IDs.presentAbsentContradiction present absent

validSelectionNeverRejected : ∀ limit scope excluded batch → Valid limit scope excluded batch →
  reported (validate limit scope excluded batch) ≡ Data.List.[]
validSelectionNeverRejected limit scope excluded batch = noFalseRejection (validate limit scope excluded batch)
