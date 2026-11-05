{-# OPTIONS --safe #-}
-- Reconcile retained deferred revisions before selecting a bounded batch.
-- Selection requires the checked handshake, not a matching binary version.
module Mimir.JudgeSelection where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_; _++_; length; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤?_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (does; yes; no)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.ExperienceSchema as Experience
import Mimir.ReviewObservation as Observation
import Mimir.JudgeHandshake as Handshake
import Mimir.Validation as Validation
import Mimir.Effects as Effects
import Mimir.JudgeRevision as Revision

data Effect : Set where
  previousDeferred : Effect
  current : ℕ → Effect
  pending : Maybe Text → ℕ → List ℕ → Effect

Reply : Effect → Set
Reply previousDeferred = Revision.Error ⊎ List Observation.Deferred
Reply (current id) = Revision.Error ⊎ Maybe Observation.Snapshot
Reply (pending project limit excluded) = Revision.Error ⊎ List Observation.Snapshot

module E = Effects.Protocol Effect Reply
open E

inScope : Maybe Text → Observation.Snapshot → Bool
inScope nothing observed = true
inScope (just project) observed = does (project ≟Text Experience.Experience.project (Observation.Snapshot.experience observed))

module Select (contract model batchLimit : ℕ) (project : Maybe Text)
  (handshake : Handshake.Contract.Ready contract model) where

  record Prepared : Set where
    constructor prepared
    field
      batch : List Observation.Snapshot
      deferred : List Observation.Deferred
      valid : Observation.BatchValid batchLimit project batch

  data Result : Set where
    failed : Revision.Error → Result
    malformed : Validation.Fault → Result
    selected : Prepared → Result

  admit : List Observation.Deferred → List Observation.Snapshot → Script Result
  admit deferred batch with Observation.validateBatch batchLimit project batch
  ... | Validation.rejected fault invalid = done (malformed fault)
  ... | Validation.accepted valid = done (selected (prepared batch deferred valid))

  fetch : List Observation.Deferred → Script Result
  fetch deferred = ask (pending project batchLimit (map Observation.Deferred.identity deferred)) (λ
    { (inj₁ error) → done (failed error) ; (inj₂ batch) → admit deferred batch })

  mutual
    reconcile : List Observation.Deferred → List Observation.Deferred → Script Result
    reconcile [] retained = fetch retained
    reconcile (item ∷ remaining) retained = ask (current (Observation.Deferred.identity item))
      (afterCurrent item remaining retained)

    afterCurrent : Observation.Deferred → List Observation.Deferred → List Observation.Deferred →
      Revision.Error ⊎ Maybe Observation.Snapshot → Script Result
    afterCurrent item remaining retained (inj₁ error) = done (failed error)
    afterCurrent item remaining retained (inj₂ nothing) = reconcile remaining retained
    afterCurrent item remaining retained (inj₂ (just observed)) with Observation.checkSnapshot observed
    ... | Validation.rejected fault invalid = done (malformed fault)
    ... | Validation.accepted valid with inScope project observed ∧ does (Observation.stillDeferred? item observed)
    ...   | true = reconcile remaining (retained ++ (item ∷ []))
    ...   | false = reconcile remaining retained

  start : Script Result
  start = ask previousDeferred (λ
    { (inj₁ error) → done (failed error) ; (inj₂ retained) → reconcile retained [] })

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
