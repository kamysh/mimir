{-# OPTIONS --safe #-}
-- Project observations may update only durable beliefs in that exact project.
-- Global beliefs are readable context, but are not implicit learning targets.
module Mimir.LearningTargets where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
open import Mimir.LearningCandidates using (Memory; Persistent; checkPersistent)
open import Mimir.Validation

record Belief : Set where
  constructor belief
  field identity : ℕ; project : Maybe Text; memory : Memory

lookup : ℕ → List Belief → Maybe Belief
lookup id [] = nothing
lookup id (b ∷ rest) with id ≟ Belief.identity b
... | yes _ = just b
... | no _ = lookup id rest

ExactProject : Text → Maybe Text → Set
ExactProject project nothing = ⊥
ExactProject project (just actual) = actual ≡ project

checkProject : ∀ project actual → Checked (ExactProject project actual)
checkProject project nothing = rejected
  (fault [] wrongIdentity "global belief is not a project learning target") (λ p → p)
checkProject project (just actual) = check
  (fault [] wrongIdentity "belief must belong to the experience project") (actual ≟Text project)

Allowed : Text → Maybe Belief → Set
Allowed project nothing = ⊥
Allowed project (just b) = ExactProject project (Belief.project b) × Persistent (Belief.memory b)

checkAllowed : ∀ project found → Checked (Allowed project found)
checkAllowed project nothing = rejected (fault [] missingReference "belief was not found") (λ p → p)
checkAllowed project (just b) = combine (checkProject project (Belief.project b)) (checkPersistent (Belief.memory b))

Valid : Text → List Belief → List ℕ → Set
Valid project beliefs = All (λ id → Allowed project (lookup id beliefs))

validate : ∀ project beliefs ids → Checked (Valid project beliefs ids)
validate project beliefs = allChecked (λ id → checkAllowed project (lookup id beliefs))

globalCannotBeChanged : ∀ project id memory → Allowed project (just (belief id nothing memory)) → ⊥
globalCannotBeChanged project id memory (impossible , persistent) = impossible

missingCannotBeChanged : ∀ project → Allowed project nothing → ⊥
missingCannotBeChanged project proof = proof

validTargetsNeverRejected : ∀ project beliefs ids → Valid project beliefs ids →
  reported (validate project beliefs ids) ≡ []
validTargetsNeverRejected project beliefs ids = noFalseRejection (validate project beliefs ids)
