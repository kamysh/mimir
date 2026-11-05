{-# OPTIONS --safe #-}
-- Current experience lookup and pending queue selection. Physical input rows
-- are coherent decoded snapshots; decoding errors are handled by the caller.
module Mimir.ExperienceRead where

import Data.Empty

open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.List using (List; []; _∷_; length; take; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_; _≤?_; _<?_)
open import Data.Integer using (ℤ)
import Data.Integer.Properties as Integer
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Mimir.Text using (Text; member)
open import Mimir.SourceReview using (_≟Text_)
open import Mimir.ExperienceSchema using (Experience)
import Mimir.ReviewObservation as Observation

record Row : Set where
  constructor row
  field snapshot : Observation.Snapshot; updatedAt : ℤ

identity : Row → ℕ
identity r = Experience.identity (Observation.Snapshot.experience (Row.snapshot r))

storedSnapshot : Row → Observation.Snapshot
storedSnapshot r = record (Row.snapshot r) { candidateIDs = [] }

get : ℕ → List Row → Maybe Observation.Snapshot
get id [] = nothing
get id (r ∷ rs) with id ≟ identity r
... | yes same = just (storedSnapshot r)
... | no different = get id rs

lookupIdentity : ∀ id rows actual → get id rows ≡ just actual →
  Experience.identity (Observation.Snapshot.experience actual) ≡ id
lookupIdentity id [] actual ()
lookupIdentity id (r ∷ rs) actual found with id ≟ identity r
... | yes same with found
...   | refl = sym same
lookupIdentity id (r ∷ rs) actual found | no different = lookupIdentity id rs actual found

scopeMatches : Maybe Text → Row → Bool
scopeMatches nothing r = true
scopeMatches (just project) r = does (project ≟Text Experience.project
  (Observation.Snapshot.experience (Row.snapshot r)))

pending : Row → Bool
pending r = does (Observation.Snapshot.reviewedRevision (Row.snapshot r)
  Integer.<? Observation.Snapshot.revision (Row.snapshot r))

select : Maybe Text → Bool → List ℕ → List Row → List Row
select project onlyPending excluded [] = []
select project onlyPending excluded (r ∷ rs)
  with scopeMatches project r ∧ not (member (identity r) excluded)
... | false = select project onlyPending excluded rs
... | true with onlyPending
...   | false = r ∷ select project onlyPending excluded rs
...   | true with pending r
...     | false = select project onlyPending excluded rs
...     | true = r ∷ select project onlyPending excluded rs

before : Row → Row → Bool
before a b with Row.updatedAt a Integer.<? Row.updatedAt b
... | yes earlier = true
... | no notEarlier with Row.updatedAt a Integer.≟ Row.updatedAt b
...   | no different = false
...   | yes same = does (identity a ≤? identity b)

insert : Row → List Row → List Row
insert a [] = a ∷ []
insert a (b ∷ bs) with before a b
... | true = a ∷ b ∷ bs
... | false = b ∷ insert a bs

sort : List Row → List Row
sort [] = []
sort (r ∷ rs) = insert r (sort rs)

data Result : Set where
  invalidLimit : Result
  selected : List Observation.Snapshot → Result

list : Maybe Text → Bool → ℕ → List ℕ → List Row → Result
list project onlyPending limit excluded rows with does (1 ≤? limit)
... | false = invalidLimit
... | true = selected
  (map storedSnapshot (take limit (sort (select project onlyPending excluded rows))))

-- Existing public pending operation is a specialization of the same ordering
-- and exclusion rules; no selected item is acknowledged by this read.
pendingExperiences : Maybe Text → ℕ → List ℕ → List Row → Result
pendingExperiences project limit excluded rows = list project true limit excluded rows

lookupOwn : ∀ r rs → get (identity r) (r ∷ rs) ≡ just (storedSnapshot r)
lookupOwn r rs with identity r ≟ identity r
... | yes same = refl
... | no different = Data.Empty.⊥-elim (different refl)

lookupOther : ∀ id r rs → id ≡ identity r → get id (r ∷ rs) ≡ just (storedSnapshot r)
lookupOther id r rs same rewrite same = lookupOwn r rs
