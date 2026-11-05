{-# OPTIONS --safe #-}
-- Ordered lookup/update boundary used by diagnostic trace operations. No
-- uniqueness assumption is needed: the first matching entry is selected.
module Mimir.FirstListMatch where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Nat using (suc)
open import Data.Nat.Properties using (+-suc)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)

module Over (A : Set) (P : A → Set) (decide : ∀ value → Dec (P value)) where
  data Selected : List A → List A → A → List A → Set where
    first : ∀ value rest → P value → Selected (value ∷ rest) [] value rest
    later : ∀ value source prefix selected rest → ¬ P value → Selected source prefix selected rest →
      Selected (value ∷ source) (value ∷ prefix) selected rest

  exact : ∀ {source prefix selected rest} → Selected source prefix selected rest → source ≡ prefix ++ (selected ∷ rest)
  exact (first value rest matches) = refl
  exact (later value source prefix selected rest skipped child) = cong (value ∷_) (exact child)

  prefixAbsent : ∀ {source prefix selected rest} → Selected source prefix selected rest → All (λ value → ¬ P value) prefix
  prefixAbsent (first value rest matches) = []
  prefixAbsent (later value source prefix selected rest skipped child) = skipped ∷ prefixAbsent child

  matches : ∀ {source prefix selected rest} → Selected source prefix selected rest → P selected
  matches (first value rest accepted) = accepted
  matches (later value source prefix selected rest skipped child) = matches child

  record Focus (source : List A) : Set where
    constructor focus
    field prefix : List A; value : A; rest : List A; meaning : Selected source prefix value rest

  data Result (source : List A) : Set where
    missing : All (λ value → ¬ P value) source → Result source
    found : Focus source → Result source

  find : ∀ source → Result source
  find [] = missing []
  find (value ∷ source) with decide value
  ... | yes accepted = found (focus [] value source (first value source accepted))
  ... | no skipped with find source
  ...   | missing absent = missing (skipped ∷ absent)
  ...   | found (focus prefix selected rest child) = found
    (focus (value ∷ prefix) selected rest (later value source prefix selected rest skipped child))

  selectedUnique : ∀ {source prefix firstValue firstRest otherPrefix secondValue secondRest} →
    Selected source prefix firstValue firstRest → Selected source otherPrefix secondValue secondRest →
    prefix ≡ otherPrefix × (firstValue ≡ secondValue × firstRest ≡ secondRest)
  selectedUnique (first value rest accepted) (first .value .rest secondAccepted) = refl , refl , refl
  selectedUnique (first value rest accepted) (later .value .rest prefix selected remaining skipped child) = ⊥-elim (skipped accepted)
  selectedUnique (later value source prefix selected rest skipped child) (first .value .source accepted) = ⊥-elim (skipped accepted)
  selectedUnique (later value source prefix selected rest skipped child)
    (later .value .source otherPrefix otherValue otherRest otherSkipped otherChild) with selectedUnique child otherChild
  ... | samePrefix , sameValue , sameRest = cong (value ∷_) samePrefix , sameValue , sameRest

  replace : ∀ {source} → Focus source → A → List A
  replace selected value = Focus.prefix selected ++ (value ∷ Focus.rest selected)

  remove : ∀ {source} → Focus source → List A
  remove selected = Focus.prefix selected ++ Focus.rest selected

  replaceLength : ∀ {source} (selected : Focus source) value → length (replace selected value) ≡ length source
  replaceLength (focus prefix selected rest meaning) value = trans (length-++ prefix)
    (sym (trans (cong length (exact meaning)) (length-++ prefix)))

  removeLength : ∀ {source} (selected : Focus source) → suc (length (remove selected)) ≡ length source
  removeLength (focus prefix selected rest meaning) = trans (cong suc (length-++ prefix))
    (trans (sym (+-suc (length prefix) (length rest)))
      (sym (trans (cong length (exact meaning)) (length-++ prefix))))

  removeOther : ∀ {source prefix selected rest} {Q : A → Set} →
    Selected source prefix selected rest → ¬ Q selected → Any Q source → Any Q (prefix ++ rest)
  removeOther (first value rest accepted) excluded (here proof) = ⊥-elim (excluded proof)
  removeOther (first value rest accepted) excluded (there proof) = proof
  removeOther (later value source prefix selected rest skipped child) excluded (here proof) = here proof
  removeOther (later value source prefix selected rest skipped child) excluded (there proof) = there (removeOther child excluded proof)
