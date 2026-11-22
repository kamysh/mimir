{-# OPTIONS --safe #-}
-- Learning storage state shared by record, review and read operations.
-- Physical timestamps and current experience rows are represented explicitly;
-- immutable review payloads and assessment rows live in Publication.World.
module Mimir.LearningStore where

open import Data.Float.Base using (Float)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_)
open import Mimir.UUIDGroups using (UUID; _≟UUID_)
open import Data.Integer using (ℤ)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Mimir.ExperienceSchema using (Experience)
import Mimir.ReviewObservation as Observation
import Mimir.ExperienceRead as Read
import Mimir.ReviewPreparationPublication as Publication
import Mimir.IndependentProvenance as Independent
import Mimir.ItemAllocation as Allocation

record SourceVersion : Set where
  constructor sourceVersion
  field payload : Experience; revision : ℕ; createdAt : ℤ

record ReviewTime : Set where
  constructor reviewTime
  field experience : UUID; revision : ℕ; createdAt : ℤ

record World : Set where
  constructor world
  field
    publication : Publication.World
    current : List Read.Row
    sources : List SourceVersion
    reviewTimes : List ReviewTime
    grounding : List (UUID × Float)
    independentOrigins : List (UUID × Independent.Stored)
    itemKeys : Allocation.Keys

identities : World → List UUID
identities w = map Read.identity (World.current w)

put : Observation.Snapshot → ℤ → List Read.Row → List Read.Row
put value timestamp [] = Read.row value timestamp ∷ []
put value timestamp (r ∷ rs) with Experience.identity (Observation.Snapshot.experience value) ≟UUID Read.identity r
... | yes same = Read.row value timestamp ∷ rs
... | no different = r ∷ put value timestamp rs

-- A review changes counters/returned candidate IDs without changing the
-- source update time used for pending queue ordering.
reviewed : Observation.Snapshot → List Read.Row → List Read.Row
reviewed value [] = []
reviewed value (r ∷ rs) with Experience.identity (Observation.Snapshot.experience value) ≟UUID Read.identity r
... | yes same = Read.row value (Read.Row.updatedAt r) ∷ rs
... | no different = r ∷ reviewed value rs

timestamp : UUID → ℕ → List ReviewTime → Maybe ℤ
timestamp experience revision [] = nothing
timestamp experience revision (r ∷ rs) with experience ≟UUID ReviewTime.experience r | revision ≟ ReviewTime.revision r
... | yes sameExperience | yes sameRevision = just (ReviewTime.createdAt r)
... | _ | _ = timestamp experience revision rs

newSource : Experience → ℕ → ℤ → World → World
newSource payload revision now w = record w
  { sources = sourceVersion payload revision now ∷ World.sources w }

sourceHistoryPreserved : ∀ payload revision now w →
  World.sources (newSource payload revision now w) ≡ sourceVersion payload revision now ∷ World.sources w
sourceHistoryPreserved payload revision now w = refl
