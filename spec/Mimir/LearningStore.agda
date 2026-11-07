{-# OPTIONS --safe #-}
-- Learning storage state shared by record, review and read operations.
-- Physical timestamps and current experience rows are represented explicitly;
-- immutable review payloads and assessment rows live in Publication.World.
module Mimir.LearningStore where

open import Data.Float.Base using (Float)
open import Data.Bool using (Bool; true; false; not; _∨_)
open import Data.List using (List; []; _∷_; map)
open import Data.Bool.ListAction using (any)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_)
open import Data.Integer using (ℤ)
import Data.Integer.Properties as Integer
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Mimir.ExperienceSchema using (Experience)
import Mimir.ReviewObservation as Observation
import Mimir.ExperienceRead as Read
import Mimir.ReviewPreparationPublication as Publication
import Mimir.IndependentProvenance as Independent
import Mimir.ItemAllocation as Allocation
import Mimir.DatabaseTransaction as Database
open import Mimir.SourceReview using (_≟Text_)

record SourceVersion : Set where
  constructor sourceVersion
  field payload : Experience; revision : ℕ; createdAt : ℤ

record ReviewTime : Set where
  constructor reviewTime
  field experience revision : ℕ; createdAt : ℤ

record World : Set where
  constructor world
  field
    publication : Publication.World
    current : List Read.Row
    sources : List SourceVersion
    reviewTimes : List ReviewTime
    grounding : List (ℕ × Float)
    independentOrigins : List (ℕ × Independent.Stored)
    itemKeys : Allocation.Keys

identities : World → List ℕ
identities w = map Read.identity (World.current w)

put : Observation.Snapshot → ℤ → List Read.Row → List Read.Row
put value timestamp [] = Read.row value timestamp ∷ []
put value timestamp (r ∷ rs) with Experience.identity (Observation.Snapshot.experience value) ≟ Read.identity r
... | yes same = Read.row value timestamp ∷ rs
... | no different = r ∷ put value timestamp rs

-- A review changes counters/returned candidate IDs without changing the
-- source update time used for pending queue ordering.
reviewed : Observation.Snapshot → List Read.Row → List Read.Row
reviewed value [] = []
reviewed value (r ∷ rs) with Experience.identity (Observation.Snapshot.experience value) ≟ Read.identity r
... | yes same = Read.row value (Read.Row.updatedAt r) ∷ rs
... | no different = r ∷ reviewed value rs

timestamp : ℕ → ℕ → List ReviewTime → Maybe ℤ
timestamp experience revision [] = nothing
timestamp experience revision (r ∷ rs) with experience ≟ ReviewTime.experience r | revision ≟ ReviewTime.revision r
... | yes sameExperience | yes sameRevision = just (ReviewTime.createdAt r)
... | _ | _ = timestamp experience revision rs

newSource : Experience → ℕ → ℤ → World → World
newSource payload revision now w = record w
  { sources = sourceVersion payload revision now ∷ World.sources w }

sourceHistoryPreserved : ∀ payload revision now w →
  World.sources (newSource payload revision now w) ≡ sourceVersion payload revision now ∷ World.sources w
sourceHistoryPreserved payload revision now w = refl

-- The database trigger emits an empty queue-change hint, never experience
-- content. PostgreSQL delivers transactional NOTIFY only on publication and
-- can coalesce identical hints within a transaction. The durable queue, rather
-- than a count of hints, remains the authority after a wake or reconnect.
data ReviewQueueSignal : Set where
  reviewQueueChanged : ReviewQueueSignal

pending : Observation.Snapshot → Bool
pending value = does (Observation.Snapshot.reviewedRevision value Integer.<?
  Observation.Snapshot.revision value)

needsWake : Maybe Observation.Snapshot → Observation.Snapshot → Bool
needsWake old value with pending value
... | false = false
... | true with old
...   | nothing = true
...   | just previous = not (pending previous) ∨
  (not (does (Observation.Snapshot.revision previous Integer.≟ Observation.Snapshot.revision value)) ∨
   not (does (Experience.project (Observation.Snapshot.experience previous) ≟Text
     Experience.project (Observation.Snapshot.experience value))))

queueChanged : World → World → Bool
queueChanged before after = any (λ row → needsWake
  (Read.get (Read.identity row) (World.current before)) (Read.Row.snapshot row)) (World.current after)

queueSignals : World → World → List ReviewQueueSignal
queueSignals before after with queueChanged before after
... | false = []
... | true = reviewQueueChanged ∷ []

-- Model the native commit boundary, including both real possibilities after
-- acknowledgement loss. This is not a claim that a transient NOTIFY is a
-- durable receipt, nor a reimplementation of PostgreSQL's delivery mechanism.
publishedSignals : ∀ {before proposed receipt actual} →
  Database.Atomic before proposed receipt actual → List ReviewQueueSignal
publishedSignals {before} {proposed} Database.committedAll = queueSignals before proposed
publishedSignals Database.abortedNone = []
publishedSignals Database.unknownBefore = []
publishedSignals {before} {proposed} Database.unknownAfter = queueSignals before proposed

publicationAndSignalTogether : ∀ {before proposed receipt actual}
  (commit : Database.Atomic before proposed receipt actual) →
  (actual ≡ before × publishedSignals commit ≡ []) ⊎
  (actual ≡ proposed × publishedSignals commit ≡ queueSignals before proposed)
publicationAndSignalTogether Database.committedAll = inj₂ (refl , refl)
publicationAndSignalTogether Database.abortedNone = inj₁ (refl , refl)
publicationAndSignalTogether Database.unknownBefore = inj₁ (refl , refl)
publicationAndSignalTogether Database.unknownAfter = inj₂ (refl , refl)

rollbackSendsNoSignal : ∀ before proposed →
  publishedSignals {before} {proposed} Database.abortedNone ≡ []
rollbackSendsNoSignal before proposed = refl

lostAcknowledgementKeepsCommittedSignal : ∀ before proposed →
  publishedSignals {before} {proposed} Database.unknownAfter ≡
  publishedSignals {before} {proposed} Database.committedAll
lostAcknowledgementKeepsCommittedSignal before proposed = refl

newPendingSourceWakes : ∀ value → pending value ≡ true → needsWake nothing value ≡ true
newPendingSourceWakes value eligible rewrite eligible = refl

completedSourceDoesNotWake : ∀ old value → pending value ≡ false → needsWake old value ≡ false
completedSourceDoesNotWake old value complete rewrite complete = refl

restoredEligibilityWakes : ∀ old value → pending old ≡ false → pending value ≡ true →
  needsWake (just old) value ≡ true
restoredEligibilityWakes old value complete eligible rewrite eligible | complete = refl
