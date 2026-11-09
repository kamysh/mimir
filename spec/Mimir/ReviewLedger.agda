{-# OPTIONS --safe #-}
-- Typed requested/applied review rows. Retry comparison uses the submitted
-- request key, while active effects use the stored applied review. No global
-- request-to-effects function is assumed: each append receives the result of
-- the state-dependent preparation. ReviewWriteSet connects that preparation.
module Mimir.ReviewLedger where

import Data.Empty
open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _≟_)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; subst; sym)
open import Mimir.ReviewSchema using (Review)
open import Mimir.SemanticKey using (Key; equal; fields)
import Mimir.LearningKeys as Keys
import Mimir.LearningInput as Input
import Mimir.LearningContracts as Contracts
import Mimir.ReviewJournal as Journal

module J = Journal.Over Key Key equal (λ key → key)
module R = J.R

record Version : Set where
  constructor storedVersion
  field
    source revision : ℕ
    requested applied : Review
    original : Maybe Input.Review

-- Existing canonical-only models retain their constructor surface. Complete
-- registered reviews store the original pre-allocation input as well.
version : ℕ → ℕ → Review → Review → Version
version source revision requested applied = storedVersion source revision requested applied nothing

submissionKey : Review → Maybe Input.Review → Key
submissionKey requested nothing = Keys.review requested
submissionKey requested (just original) = Keys.reviewInput original

versionKey : Version → Key
versionKey row = submissionKey (Version.requested row) (Version.original row)

requestEntry : Version → J.Entry
requestEntry row = J.version (Version.source row) (Version.revision row)
  (versionKey row) (versionKey row)

head : List Version → Maybe Version
head [] = nothing
head (row ∷ rest) = just row

-- A live request pointer must refer to precisely the newest row, at the same
-- source/review revisions. Stale histories may remain after source correction.
Matches : R.Cell → Maybe Key → Maybe Version → Set
Matches state nothing row = ⊤
Matches state (just key) nothing = Data.Empty.⊥
Matches state (just key) (just row) = key ≡ versionKey row ×
  (R.Cell.current state ≡ Version.source row × R.Cell.review state ≡ Version.revision row)

record World : Set where
  constructor world
  field
    cells : ℕ → R.Cell
    histories : ℕ → List Version

module Cells = Contracts.Ownership R.Cell
module Histories = Contracts.Ownership (List Version)

ConsistentAt : World → ℕ → Set
ConsistentAt before identity =
  J.Ordered (R.Cell.review (World.cells before identity)) (map requestEntry (World.histories before identity)) ×
  Matches (World.cells before identity) (R.Cell.contribution (World.cells before identity))
    (head (World.histories before identity))

Consistent : World → Set
Consistent before = ∀ identity → ConsistentAt before identity

activeApplied : R.Cell → List Version → Maybe Review
activeApplied state rows with R.active state
... | nothing = nothing
... | just key with rows
...   | [] = nothing
...   | row ∷ rest = just (Version.applied row)

module Submitted (original : Maybe Input.Review) where
  next : ℕ → World → Review → Review → Version
  next identity before requested applied = storedVersion
    (R.Cell.current (World.cells before identity)) (suc (R.Cell.review (World.cells before identity))) requested applied original

  append : ℕ → World → Review → Review → World
  append identity before requested applied = world
    (Cells.write identity (R.commit (World.cells before identity) (submissionKey requested original)) (World.cells before))
    (Histories.write identity (next identity before requested applied ∷ World.histories before identity) (World.histories before))

  appendConsistent : ∀ identity before requested applied → Consistent before → Consistent (append identity before requested applied)
  appendConsistent identity before requested applied consistent queried with queried ≟ identity
  ... | yes refl = J.newest refl (proj₁ (consistent identity)) , refl , refl , refl
  ... | no different = consistent queried

  installedHistory : ∀ identity before requested applied →
    World.histories (append identity before requested applied) identity ≡
      next identity before requested applied ∷ World.histories before identity
  installedHistory identity before requested applied = Histories.write-own identity
    (next identity before requested applied ∷
     World.histories before identity)
    (World.histories before)

  originalInputRetained : ∀ identity before requested applied →
    head (World.histories (append identity before requested applied) identity) ≡
      just (storedVersion (R.Cell.current (World.cells before identity))
        (suc (R.Cell.review (World.cells before identity))) requested applied original)
  originalInputRetained identity before requested applied
    rewrite installedHistory identity before requested applied = refl

  historyRetained : ∀ identity before requested applied row → row ∈ World.histories before identity →
    row ∈ World.histories (append identity before requested applied) identity
  historyRetained identity before requested applied row member = subst (λ rows → row ∈ rows)
    (sym (installedHistory identity before requested applied))
    (there member)

  unrelatedUnchanged : ∀ identity before requested applied other → other ≢ identity →
    World.cells (append identity before requested applied) other ≡ World.cells before other ×
    World.histories (append identity before requested applied) other ≡ World.histories before other
  unrelatedUnchanged identity before requested applied other different = Cells.write-other identity other
    (R.commit (World.cells before identity) (submissionKey requested original))
    (World.cells before) different
    ,
    Histories.write-other identity other
    (next identity before requested applied ∷
     World.histories before identity)
    (World.histories before) different

  appendSelectsApplied : ∀ identity before requested applied →
    activeApplied (World.cells (append identity before requested applied) identity)
      (World.histories (append identity before requested applied) identity) ≡ just applied
  appendSelectsApplied identity before requested applied
    rewrite Cells.write-own identity (R.commit (World.cells before identity) (submissionKey requested original)) (World.cells before)
          | installedHistory identity before requested applied
          | R.committed-contribution-active (World.cells before identity) (submissionKey requested original) = refl


open Submitted nothing public

-- Correction retracts the live request pointer and preserves every immutable
-- requested/applied row. Active effects must follow this pointer, not history
-- presence alone.
correct : ℕ → World → World
correct identity before = world
  (Cells.write identity (R.correct (World.cells before identity)) (World.cells before)) (World.histories before)

correctionConsistent : ∀ identity before → Consistent before → Consistent (correct identity before)
correctionConsistent identity before consistent queried with queried ≟ identity
... | yes refl = proj₁ (consistent identity) , tt
... | no different = consistent queried

correctionRetracts : ∀ identity before →
  activeApplied (World.cells (correct identity before) identity) (World.histories (correct identity before) identity) ≡ nothing
correctionRetracts identity before
  rewrite Cells.write-own identity (R.correct (World.cells before identity)) (World.cells before)
        | R.stale-contribution-inactive (R.correct (World.cells before identity))
            (R.correction-is-pending (World.cells before identity)) = refl
