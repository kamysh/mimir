{-# OPTIONS --safe #-}
-- Immutable history and current-review read projections, with explicit
-- missing-row and inconsistent timestamp outcomes.
module Mimir.LearningHistory where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_; _≤?_)
open import Data.Integer using (ℤ; +_; ∣_∣)
import Data.Integer.Properties as Integer
open import Relation.Nullary using (yes; no)
open import Mimir.ExperienceSchema using (Experience)
open import Mimir.ReviewSchema using (Review)
import Mimir.LearningStore as Store
import Mimir.ExperienceRead as Read
import Mimir.ReviewObservation as Observation
import Mimir.ReviewLedger as Ledger
import Mimir.ReviewPreparationPublication as Publication
import Mimir.AssessmentRead as Assessment

record CurrentReview : Set where
  constructor currentReview
  field state : Observation.Snapshot; applied : Maybe Review

matchingReview : Observation.Snapshot → Maybe Ledger.Version → Maybe Review
matchingReview current nothing = nothing
matchingReview current (just v) with (+ Ledger.Version.source v) Integer.≟ Observation.Snapshot.revision current
... | yes same = just (Ledger.Version.applied v)
... | no stale = nothing

learningReview : ℕ → Store.World → Maybe CurrentReview
learningReview id w with Read.get id (Store.World.current w)
... | nothing = nothing
... | just current = just (currentReview current
  (matchingReview current (Assessment.version ∣ Observation.Snapshot.reviewRevision current ∣
    (Ledger.World.histories (Publication.World.ledger (Store.World.publication w)) id))))

record Entry (Payload : Set) : Set where
  constructor entry
  field revision : ℕ; payload : Payload; createdAt : ℤ

insert : ∀ {A} → Entry A → List (Entry A) → List (Entry A)
insert e [] = e ∷ []
insert e (f ∷ fs) with Entry.revision e ≤? Entry.revision f
... | yes earlier = e ∷ f ∷ fs
... | no later = f ∷ insert e fs

sourceHistory : ℕ → List Store.SourceVersion → List (Entry Experience)
sourceHistory id [] = []
sourceHistory id (v ∷ vs) with id ≟ Experience.identity (Store.SourceVersion.payload v)
... | no different = sourceHistory id vs
... | yes same = insert (entry (Store.SourceVersion.revision v)
  (Store.SourceVersion.payload v) (Store.SourceVersion.createdAt v)) (sourceHistory id vs)

reviewHistory : ℕ → List Store.ReviewTime → List Ledger.Version → Maybe (List (Entry Review))
reviewHistory id times [] = just []
reviewHistory id times (v ∷ vs) with Store.timestamp id (Ledger.Version.revision v) times
  | reviewHistory id times vs
... | just created | just rest = just (insert (entry (Ledger.Version.revision v) (Ledger.Version.applied v) created) rest)
... | _ | _ = nothing

data Result : Set where
  inconsistentHistory : Result
  history : List (Entry Experience) → List (Entry Review) → Result

getHistory : ℕ → Store.World → Result
getHistory id w with reviewHistory id (Store.World.reviewTimes w)
  (Ledger.World.histories (Publication.World.ledger (Store.World.publication w)) id)
... | nothing = inconsistentHistory
... | just reviews = history (sourceHistory id (Store.World.sources w)) reviews
