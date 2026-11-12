{-# OPTIONS --safe #-}
module Mimir.CandidateProvenance where

open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Mimir.UUIDGroups using (UUID; _≟UUID_)
open import Relation.Nullary using (does; yes; no)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
open import Mimir.LearningCandidates using (Candidate; belief; patternCandidate) renaming (candidateKey to declarationKey)
import Mimir.CandidateRegistry as Registry
import Mimir.ReviewSchema as Review
import Mimir.ReviewLedger as Ledger
import Mimir.ReviewPreparationPublication as Publication
import Mimir.LearningStore as Store
import Mimir.ExperienceRead as Read

data Kind : Set where beliefKind patternKind : Kind

kindOf : Candidate → Kind
kindOf (belief key content memory) = beliefKind
kindOf (patternCandidate key situation approach) = patternKind

declares : Text → List Candidate → Bool
declares key [] = false
declares key (c ∷ cs) with key ≟Text declarationKey c
... | yes same = true
... | no different = declares key cs

record Provenance : Set where
  constructor provenance
  field experienceID : UUID; candidateKey : Text; kind : Kind; retired active : Bool

active : Registry.Entry → Ledger.World → Bool
active e ledger with Ledger.activeApplied (Ledger.World.cells ledger (Registry.Entry.experienceID e))
  (Ledger.World.histories ledger (Registry.Entry.experienceID e))
... | nothing = false
... | just applied = not (Registry.Entry.retired e) ∧
  declares (declarationKey (Registry.Entry.declaration e)) (Review.Review.candidates applied)

lookup : UUID → Registry.Registry → Store.World → Maybe Provenance
lookup id [] w = nothing
lookup id (e ∷ es) w with id ≟UUID Registry.Entry.nodeID e
... | no different = lookup id es w
... | yes same with Read.get (Registry.Entry.experienceID e) (Store.World.current w)
...   | nothing = nothing
...   | just current = just (provenance (Registry.Entry.experienceID e)
  (declarationKey (Registry.Entry.declaration e)) (kindOf (Registry.Entry.declaration e))
  (Registry.Entry.retired e) (active e (Publication.World.ledger (Store.World.publication w))))

get : UUID → Store.World → Maybe Provenance
get id w = lookup id (Publication.World.registry (Store.World.publication w)) w
