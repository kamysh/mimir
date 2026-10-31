{-# OPTIONS --safe #-}
-- Later complete batches add each affected identity at most once, retaining
-- previous timestamps and input order. Loaded duplicates are not silently fixed.
module Mimir.JudgeConfirmationLedger where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (++-assoc; ++-identityʳ; map-++)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
import Mimir.Collections as Collections
import Mimir.JudgeStateRecords as Records

module Over (Id : Set) (equal : (x y : Id) → Dec (x ≡ y)) where
  module R = Records.Over Id
  module IDs = Collections.Equality Id equal

  identities : List R.Confirmed → List Id
  identities = map R.Confirmed.identity

  data Updates (affected : List Id) (at : ℕ) : List Id → List R.Confirmed → List R.Confirmed → List R.Confirmed → Set where
    finished : ∀ before → Updates affected at [] before before []
    outside : ∀ identity rest before after additions → ¬ IDs.Present identity affected →
      Updates affected at rest before after additions → Updates affected at (identity ∷ rest) before after additions
    existing : ∀ identity rest before after additions → IDs.Present identity (identities before) →
      Updates affected at rest before after additions → Updates affected at (identity ∷ rest) before after additions
    added : ∀ identity rest before after additions → IDs.Present identity affected → IDs.Absent identity (identities before) →
      Updates affected at rest (before ++ (R.confirmedValue identity at ∷ [])) after additions →
      Updates affected at (identity ∷ rest) before after (R.confirmedValue identity at ∷ additions)

  record Result (affected : List Id) (at : ℕ) (selected : List Id) (before : List R.Confirmed) : Set where
    constructor result
    field after additions : List R.Confirmed; meaning : Updates affected at selected before after additions

  absentFromNotPresent : ∀ identity ids → ¬ IDs.Present identity ids → IDs.Absent identity ids
  absentFromNotPresent identity [] missing = []
  absentFromNotPresent identity (head ∷ tail) missing =
    (λ same → missing (here same)) ∷ absentFromNotPresent identity tail (λ found → missing (there found))

  collect : ∀ affected at selected before → Result affected at selected before
  collect affected at [] before = result before [] (finished before)
  collect affected at (identity ∷ rest) before with IDs.present? identity affected
  ... | no notAffected with collect affected at rest before
  ...   | result after additions proof = result after additions (outside identity rest before after additions notAffected proof)
  collect affected at (identity ∷ rest) before | yes affectedIdentity with IDs.present? identity (identities before)
  ... | no missing with collect affected at rest (before ++ (R.confirmedValue identity at ∷ []))
  ...   | result after additions proof = result after (R.confirmedValue identity at ∷ additions)
    (added identity rest before after additions affectedIdentity (absentFromNotPresent identity (identities before) missing) proof)
  collect affected at (identity ∷ rest) before | yes affectedIdentity | yes present with collect affected at rest before
  ...   | result after additions proof = result after additions (existing identity rest before after additions present proof)

  appendedExactly : ∀ {affected at selected before after additions} → Updates affected at selected before after additions →
    after ≡ before ++ additions
  appendedExactly (finished before) = sym (++-identityʳ before)
  appendedExactly (outside identity rest before after additions notAffected later) = appendedExactly later
  appendedExactly (existing identity rest before after additions present later) = appendedExactly later
  appendedExactly (added identity rest before after additions affected absent later) =
    trans (appendedExactly later) (++-assoc before (R.confirmedValue identity _ ∷ []) additions)

  Eligible : List Id → List Id → ℕ → R.Confirmed → Set
  Eligible affected selected at entry = IDs.Present (R.Confirmed.identity entry) affected ×
    (IDs.Present (R.Confirmed.identity entry) selected × R.Confirmed.recordedAt entry ≡ at)

  liftEligible : ∀ {affected selected at additions} identity → All (Eligible affected selected at) additions →
    All (Eligible affected (identity ∷ selected) at) additions
  liftEligible identity [] = []
  liftEligible identity ((affected , selected , timestamp) ∷ later) =
    (affected , there selected , timestamp) ∷ liftEligible identity later

  onlyEligibleAdded : ∀ {affected at selected before after additions} → Updates affected at selected before after additions →
    All (Eligible affected selected at) additions
  onlyEligibleAdded (finished before) = []
  onlyEligibleAdded (outside identity rest before after additions notAffected later) = liftEligible identity (onlyEligibleAdded later)
  onlyEligibleAdded (existing identity rest before after additions present later) = liftEligible identity (onlyEligibleAdded later)
  onlyEligibleAdded (added identity rest before after additions affected absent later) =
    (affected , here refl , refl) ∷ liftEligible identity (onlyEligibleAdded later)

  appendAll : ∀ {P : Id → Set} {first second} → All P first → All P second → All P (first ++ second)
  appendAll [] second = second
  appendAll (proof ∷ first) second = proof ∷ appendAll first second

  snocUnique : ∀ identity ids → IDs.Absent identity ids → IDs.Unique ids → IDs.Unique (ids ++ (identity ∷ []))
  snocUnique identity [] [] unique = [] , tt
  snocUnique identity (head ∷ tail) (different ∷ absent) (headAbsent , tailUnique) =
    appendAll headAbsent ((λ same → different (sym same)) ∷ []) , snocUnique identity tail absent tailUnique

  uniquePreserved : ∀ {affected at selected before after additions} → Updates affected at selected before after additions →
    IDs.Unique (identities before) → IDs.Unique (identities after)
  uniquePreserved (finished before) unique = unique
  uniquePreserved (outside identity rest before after additions notAffected later) unique = uniquePreserved later unique
  uniquePreserved (existing identity rest before after additions present later) unique = uniquePreserved later unique
  uniquePreserved (added identity rest before after additions affected absent later) unique = uniquePreserved later
    (subst IDs.Unique (sym (map-++ R.Confirmed.identity before (R.confirmedValue identity _ ∷ [])))
      (snocUnique identity (identities before) absent unique))
