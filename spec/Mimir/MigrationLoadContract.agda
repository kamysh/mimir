{-# OPTIONS --safe #-}
-- Successful loading accounts for every file in order; an error identifies
-- the first failed file after a completely successful prefix.
module Mimir.MigrationLoadContract where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import Mimir.MigrationFileParsing
open import Mimir.MigrationLedger using (Migration)

Succeeded : File → Set
Succeeded entry = Σ (List Migration) λ migrations → readFile (File.label entry) (File.contents entry) ≡ inj₂ migrations

data Loading : List File → Error Data.Sum.⊎ List Migration → Set where
  empty : Loading [] (inj₂ [])
  failedHere : ∀ {entry rest problem} → readFile (File.label entry) (File.contents entry) ≡ inj₁ problem → Loading (entry ∷ rest) (inj₁ problem)
  failedLater : ∀ {entry rest first problem} → readFile (File.label entry) (File.contents entry) ≡ inj₂ first →
    Loading rest (inj₁ problem) → Loading (entry ∷ rest) (inj₁ problem)
  loaded : ∀ {entry rest first remaining} → readFile (File.label entry) (File.contents entry) ≡ inj₂ first →
    Loading rest (inj₂ remaining) → Loading (entry ∷ rest) (inj₂ (first ++ remaining))

sound : ∀ entries → Loading entries (loadOrdered entries)
sound [] = empty
sound (entry ∷ rest) with readFile (File.label entry) (File.contents entry) in observed
... | inj₁ problem = failedHere observed
... | inj₂ first with loadOrdered rest | sound rest
...   | inj₁ problem | recursive = failedLater observed recursive
...   | inj₂ remaining | recursive = loaded observed recursive

complete : ∀ {entries result} → Loading entries result → loadOrdered entries ≡ result
complete empty = refl
complete (failedHere observed) rewrite observed = refl
complete (failedLater observed recursive) rewrite observed | complete recursive = refl
complete (loaded observed recursive) rewrite observed | complete recursive = refl

allFilesSucceeded : ∀ {entries migrations} → Loading entries (inj₂ migrations) → All Succeeded entries
allFilesSucceeded empty = []
allFilesSucceeded (loaded {first = first} observed recursive) = (first , observed) ∷ allFilesSucceeded recursive

record FirstFailure (entries : List File) (problem : Error) : Set where
  constructor firstFailure
  field
    before : List File
    failed : File
    after : List File
    exact : entries ≡ before ++ failed ∷ after
    successfulPrefix : All Succeeded before
    failureObserved : readFile (File.label failed) (File.contents failed) ≡ inj₁ problem

firstFailureWitness : ∀ {entries problem} → Loading entries (inj₁ problem) → FirstFailure entries problem
firstFailureWitness (failedHere {entry} {rest} observed) = firstFailure [] entry rest refl [] observed
firstFailureWitness (failedLater {entry} {first = first} observed recursive) with firstFailureWitness recursive
... | firstFailure before failed after exact prefix actualFailure =
  firstFailure (entry ∷ before) failed after (cong (entry ∷_) exact) ((first , observed) ∷ prefix) actualFailure

acceptedFiles : ∀ entries migrations → loadOrdered entries ≡ inj₂ migrations → All Succeeded entries
acceptedFiles entries migrations observed = allFilesSucceeded (subst (Loading entries) observed (sound entries))

reportedFailure : ∀ entries problem → loadOrdered entries ≡ inj₁ problem → FirstFailure entries problem
reportedFailure entries problem observed = firstFailureWitness (subst (Loading entries) observed (sound entries))
