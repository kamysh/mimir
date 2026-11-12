{-# OPTIONS --safe #-}
-- Stable candidate reservations. PostgreSQL supplies record UUIDs; successful
-- allocation is observed rather than assumed.
module Mimir.CandidateRegistry where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.Any using (Any; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Mimir.UUIDGroups using (UUID; _≟UUID_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Mimir.Text using (Text)
open import Mimir.Validation
open import Mimir.Collections using (module Equality; pairEqual)
open import Mimir.SourceReview using (_≟Text_; false?)
open import Mimir.LearningCandidates using (Candidate; candidateKey; candidateEqual)

record Entry : Set where
  constructor entry
  field
    experienceID : UUID
    declaration : Candidate
    nodeID : UUID
    retired : Bool

Key = UUID × Text
Registry = List Entry

entryKey : Entry → Key
entryKey e = Entry.experienceID e , candidateKey (Entry.declaration e)

keyEqual = pairEqual _≟UUID_ _≟Text_

lookup : Key → Registry → Maybe Entry
lookup name [] = nothing
lookup name (e ∷ rest) with keyEqual name (entryKey e)
... | yes _ = just e
... | no _ = lookup name rest

module IDs = Equality UUID _≟UUID_

ExistingValid : Candidate → Entry → Set
ExistingValid c e = c ≡ Entry.declaration e × Entry.retired e ≡ false

checkExisting : ∀ c e → Checked (ExistingValid c e)
checkExisting c e = combine
  (check (fault [] wrongIdentity "candidate key has a different declaration")
    (candidateEqual c (Entry.declaration e)))
  (check (fault [] wrongIdentity "candidate identity was deleted") (false? (Entry.retired e)))

data Plan (registry : Registry) (occupied : List UUID) (experience : UUID) (c : Candidate) : Set where
  reuse : (e : Entry) → lookup (experience , candidateKey c) registry ≡ just e → ExistingValid c e →
    Plan registry occupied experience c
  create : (fresh : UUID) → lookup (experience , candidateKey c) registry ≡ nothing →
    IDs.Absent fresh (occupied ++ map Entry.nodeID registry) → Plan registry occupied experience c

reserve : ∀ registry occupied experience c fresh → Fault ⊎ Plan registry occupied experience c
reserve registry occupied experience c fresh with lookup (experience , candidateKey c) registry in found
... | just e with checkExisting c e
...   | rejected failure invalid = inj₁ failure
...   | accepted valid = inj₂ (reuse e found valid)
reserve registry occupied experience c fresh | nothing with IDs.absent? fresh (occupied ++ map Entry.nodeID registry)
... | no collision = inj₁ (fault [] wrongIdentity "generated candidate identity is already occupied")
... | yes absent = inj₂ (create fresh found absent)

assigned : ∀ {registry occupied experience c} → Plan registry occupied experience c → UUID
assigned (reuse e found valid) = Entry.nodeID e
assigned (create fresh found absent) = fresh

publish : ∀ {registry occupied experience c} → Plan registry occupied experience c → Registry
publish {registry} (reuse e found valid) = registry
publish {registry} {experience = experience} {c} (create fresh found absent) =
  entry experience c fresh false ∷ registry

data TransactionOutcome : Set where aborted committed : TransactionOutcome

finish : ∀ {registry occupied experience c} → Plan registry occupied experience c → TransactionOutcome → Registry
finish {registry} plan aborted = registry
finish plan committed = publish plan

abortPreservesRegistry : ∀ {registry occupied experience c} (p : Plan registry occupied experience c) →
  finish p aborted ≡ registry
abortPreservesRegistry p = refl

originalEntriesSurvive : ∀ {registry occupied experience c}
  (p : Plan registry occupied experience c) old → Any (old ≡_) registry → Any (old ≡_) (publish p)
originalEntriesSurvive (reuse e found valid) old present = present
originalEntriesSurvive (create fresh found absent) old present = there present

lookupInserted : ∀ experience c fresh registry →
  lookup (experience , candidateKey c) (entry experience c fresh false ∷ registry) ≡
    just (entry experience c fresh false)
lookupInserted experience c fresh registry with keyEqual (experience , candidateKey c) (experience , candidateKey c)
... | yes _ = refl
... | no impossible = ⊥-elim (impossible refl)

createdCannotCollide : ∀ {registry occupied experience c} fresh absent unused →
  IDs.Absent (assigned (create {registry} {occupied} {experience} {c} fresh absent unused))
    (occupied ++ map Entry.nodeID registry)
createdCannotCollide fresh absent unused = unused

reuseKeepsIdentity : ∀ {registry occupied experience c} e found valid →
  assigned (reuse {registry} {occupied} {experience} {c} e found valid) ≡ Entry.nodeID e
reuseKeepsIdentity e found valid = refl

retiredCannotBeReused : ∀ c e → Entry.retired e ≡ true → ExistingValid c e → Data.Empty.⊥
retiredCannotBeReused c e retired (same , live) with
  Relation.Binary.PropositionalEquality.trans (Relation.Binary.PropositionalEquality.sym retired) live
... | ()
