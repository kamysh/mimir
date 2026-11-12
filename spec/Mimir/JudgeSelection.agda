{-# OPTIONS --safe #-}
-- Reconcile retained deferred revisions before selecting a bounded batch.
-- Selection requires the checked handshake, not a matching binary version.
module Mimir.JudgeSelection where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_; _++_; length; map)
open import Data.List.Relation.Unary.All using (All)
open import Data.Product using (_×_; _,_; proj₂)
import Data.Empty
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤?_)
open import Mimir.UUIDGroups using (UUID)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (does; yes; no)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.ExperienceSchema as Experience
import Mimir.ReviewObservation as Observation
import Mimir.JudgeHandshake as Handshake
import Mimir.Validation as Validation
import Mimir.Effects as Effects
import Mimir.JudgeRevision as Revision
import Mimir.PendingSelection as Pending

data Effect : Set where
  previousDeferred : Effect
  current : UUID → Effect
  pending : Maybe Text → Maybe ℕ → List UUID → Effect

Reply : Effect → Set
Reply previousDeferred = Revision.Error ⊎ List Observation.Deferred
Reply (current id) = Revision.Error ⊎ Maybe Observation.Snapshot
Reply (pending project limit excluded) = Revision.Error ⊎ List Observation.Snapshot

module E = Effects.Protocol Effect Reply
open E

inScope : Maybe Text → Observation.Snapshot → Bool
inScope nothing observed = true
inScope (just project) observed = does (project ≟Text Experience.Experience.project (Observation.Snapshot.experience observed))

module Select (contract model : ℕ) (batchLimit : Maybe ℕ) (project : Maybe Text)
  (handshake : Handshake.Contract.Ready contract model) where

  record Prepared : Set where
    constructor prepared
    field
      batch : List Observation.Snapshot
      deferred : List Observation.Deferred
      valid : Pending.Valid batchLimit project (map Observation.Deferred.identity deferred) batch

  everyPreparedItemIsPending : ∀ chosen → All Pending.Pending (Prepared.batch chosen)
  everyPreparedItemIsPending chosen = Pending.everySelectedIsPending (Prepared.valid chosen)

  noPreparedItemIsExcluded : ∀ chosen →
    All (λ s → Pending.IDs.Absent (Pending.identity s) (map Observation.Deferred.identity (Prepared.deferred chosen)))
      (Prepared.batch chosen)
  noPreparedItemIsExcluded chosen = Pending.noSelectedIsExcluded (Prepared.valid chosen)

  data Result : Set where
    failed : Revision.Error → Result
    malformed : Validation.Fault → Result
    selected : Prepared → Result

  admit : List Observation.Deferred → List Observation.Snapshot → Script Result
  admit deferred batch with Pending.validate batchLimit project (map Observation.Deferred.identity deferred) batch
  ... | Validation.rejected fault invalid = done (malformed fault)
  ... | Validation.accepted valid = done (selected (prepared batch deferred valid))

  invalidReplyCannotPrepare : ∀ deferred batch →
    (Pending.Valid batchLimit project (map Observation.Deferred.identity deferred) batch → Data.Empty.⊥) →
    Data.Product.Σ Validation.Fault (λ fault → admit deferred batch ≡ done (malformed fault))
  invalidReplyCannotPrepare deferred batch invalid
    with Pending.validate batchLimit project (map Observation.Deferred.identity deferred) batch
  ... | Validation.rejected fault refuted = fault , refl
  ... | Validation.accepted valid = Data.Empty.⊥-elim (invalid valid)

  admittedReplyPreserved : ∀ deferred batch events chosen → Runs (admit deferred batch) events (selected chosen) →
    Prepared.batch chosen ≡ batch × Prepared.deferred chosen ≡ deferred
  admittedReplyPreserved deferred batch events chosen execution
    with Pending.validate batchLimit project (map Observation.Deferred.identity deferred) batch
  ... | Validation.rejected fault invalid with execution
  ...   | ()
  admittedReplyPreserved deferred batch events chosen execution | Validation.accepted valid with execution
  ... | E.returned _ = refl , refl

  validReplyPrepared : ∀ deferred batch → Pending.Valid batchLimit project (map Observation.Deferred.identity deferred) batch →
    Data.Product.Σ Prepared (λ chosen → admit deferred batch ≡ done (selected chosen) ×
      (Prepared.batch chosen ≡ batch × Prepared.deferred chosen ≡ deferred))
  validReplyPrepared deferred batch valid
    with Pending.validate batchLimit project (map Observation.Deferred.identity deferred) batch
  ... | Validation.rejected fault invalid = Data.Empty.⊥-elim (invalid valid)
  ... | Validation.accepted checked = prepared batch deferred checked , refl , refl , refl

  fetch : List Observation.Deferred → Script Result
  fetch deferred = ask (pending project batchLimit (map Observation.Deferred.identity deferred)) (λ
    { (inj₁ failureValue) → done (failed failureValue) ; (inj₂ batch) → admit deferred batch })

  mutual
    reconcile : List Observation.Deferred → List Observation.Deferred → Script Result
    reconcile [] retained = fetch retained
    reconcile (item ∷ remaining) retained = ask (current (Observation.Deferred.identity item))
      (afterCurrent item remaining retained)

    afterCurrent : Observation.Deferred → List Observation.Deferred → List Observation.Deferred →
      Revision.Error ⊎ Maybe Observation.Snapshot → Script Result
    afterCurrent item remaining retained (inj₁ failureValue) = done (failed failureValue)
    afterCurrent item remaining retained (inj₂ nothing) = reconcile remaining retained
    afterCurrent item remaining retained (inj₂ (just observed)) with Observation.checkSnapshot observed
    ... | Validation.rejected fault invalid = done (malformed fault)
    ... | Validation.accepted valid with inScope project observed ∧ does (Observation.stillDeferred? item observed)
    ...   | true = reconcile remaining (retained ++ (item ∷ []))
    ...   | false = reconcile remaining retained

  start : Script Result
  start = ask previousDeferred (λ
    { (inj₁ failureValue) → done (failed failureValue) ; (inj₂ retained) → reconcile retained [] })

  completedSelectionIsEligible : ∀ events chosen → Runs start events (selected chosen) →
    All (Pending.Eligible (map Observation.Deferred.identity (Prepared.deferred chosen))) (Prepared.batch chosen)
  completedSelectionIsEligible events chosen execution = proj₂ (Prepared.valid chosen)

  pins : Prepared → List Observation.Pin
  pins chosen = map Observation.pinSnapshot (Prepared.batch chosen)

  data Disposition : Set where idle held review : Disposition

  disposition : Prepared → Disposition
  disposition chosen with Prepared.batch chosen | Prepared.deferred chosen
  ... | [] | [] = idle
  ... | [] | _ ∷ _ = held
  ... | _ ∷ _ | _ = review

  -- Model execution is available only for review. Both empty-queue outcomes
  -- finish before trace allocation, backend.next or provider budget spending.

  unchangedPendingRevisionRemainsDeferred : ∀ item remaining retained observed →
    Observation.SnapshotValid observed → inScope project observed ≡ true → Observation.StillDeferred item observed →
    afterCurrent item remaining retained (inj₂ (just observed)) ≡ reconcile remaining (retained ++ (item ∷ []))
  unchangedPendingRevisionRemainsDeferred item remaining retained observed valid scoped deferred
    with Observation.checkSnapshot observed
  ... | Validation.rejected fault invalid = ⊥-elim (invalid valid)
  ... | Validation.accepted checked with Observation.stillDeferred? item observed
  ...   | yes still rewrite scoped = refl
  ...   | no impossible = ⊥-elim (impossible deferred)

  changedOrReviewedRevisionIsReleased : ∀ item remaining retained observed →
    Observation.SnapshotValid observed → (Observation.StillDeferred item observed → Data.Empty.⊥) →
    afterCurrent item remaining retained (inj₂ (just observed)) ≡ reconcile remaining retained
  changedOrReviewedRevisionIsReleased item remaining retained observed valid released
    with Observation.checkSnapshot observed
  ... | Validation.rejected fault invalid = ⊥-elim (invalid valid)
  ... | Validation.accepted checked with Observation.stillDeferred? item observed
  ...   | yes still = ⊥-elim (released still)
  ...   | no different with inScope project observed
  ...     | false = refl
  ...     | true = refl
