{-# OPTIONS --safe #-}
-- Per-file predecessor insertion. Existing dependencies keep their order;
-- the predecessor is appended only when absent. All other metadata survives.
module Mimir.MigrationImplicit where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
open import Mimir.Collections using (module Equality)
open import Mimir.MigrationLedger using (Migration; Metadata; migrationRecord; metadata)
import Mimir.ExactBytes as Bytes

module Names = Equality Text _≟Text_

dependencies : Migration → List Text
dependencies migration = Metadata.requires (Migration.payload migration)

add : Text → Migration → Migration
add previous migration with Names.present? previous (dependencies migration)
... | yes present = migration
... | no absent = migrationRecord (Migration.name migration)
  (metadata (Metadata.description (Migration.payload migration))
    (dependencies migration ++ previous ∷ [])
    (Metadata.checksum (Migration.payload migration)) (Metadata.script (Migration.payload migration)))

lastPresent : ∀ previous requirements → Names.Present previous (requirements ++ previous ∷ [])
lastPresent previous [] = here refl
lastPresent previous (name ∷ rest) = there (lastPresent previous rest)

leftPresent : ∀ query requirements suffix → Names.Present query requirements → Names.Present query (requirements ++ suffix)
leftPresent query (name ∷ rest) suffix (here same) = here same
leftPresent query (name ∷ rest) suffix (there found) = there (leftPresent query rest suffix found)

includesPrevious : ∀ previous migration → Names.Present previous (dependencies (add previous migration))
includesPrevious previous migration with Names.present? previous (dependencies migration)
... | yes present = present
... | no absent = lastPresent previous (dependencies migration)

keepsDependencies : ∀ previous migration query → Names.Present query (dependencies migration) →
  Names.Present query (dependencies (add previous migration))
keepsDependencies previous migration query present with Names.present? previous (dependencies migration)
... | yes already = present
... | no absent = leftPresent query (dependencies migration) (previous ∷ []) present

namePreserved : ∀ previous migration → Migration.name (add previous migration) ≡ Migration.name migration
namePreserved previous migration with Names.present? previous (dependencies migration)
... | yes present = refl
... | no absent = refl

fingerprint : Migration → Text × Text × Bytes.Bytes 32 × Text
fingerprint migration = Migration.name migration , Metadata.description (Migration.payload migration) ,
  Metadata.checksum (Migration.payload migration) , Metadata.script (Migration.payload migration)

metadataPreserved : ∀ previous migration → fingerprint (add previous migration) ≡ fingerprint migration
metadataPreserved previous migration with Names.present? previous (dependencies migration)
... | yes present = refl
... | no absent = refl

alreadyPresent : ∀ previous migration → Names.Present previous (dependencies migration) → add previous migration ≡ migration
alreadyPresent previous migration present with Names.present? previous (dependencies migration)
... | yes found = refl
... | no absent = ⊥-elim (absent present)

addIdempotent : ∀ previous migration → add previous (add previous migration) ≡ add previous migration
addIdempotent previous migration = alreadyPresent previous (add previous migration) (includesPrevious previous migration)

chain : Maybe Text → List Migration → List Migration
chain previous [] = []
chain nothing (migration ∷ rest) = migration ∷ chain (just (Migration.name migration)) rest
chain (just previous) (migration ∷ rest) = add previous migration ∷ chain (just (Migration.name migration)) rest

file : List Migration → List Migration
file = chain nothing

fingerprintsPreserved : ∀ previous migrations → map fingerprint (chain previous migrations) ≡ map fingerprint migrations
fingerprintsPreserved previous [] = refl
fingerprintsPreserved nothing (migration ∷ rest) =
  cong (fingerprint migration ∷_) (fingerprintsPreserved (just (Migration.name migration)) rest)
fingerprintsPreserved (just previous) (migration ∷ rest) = cong₂ _∷_
  (metadataPreserved previous migration) (fingerprintsPreserved (just (Migration.name migration)) rest)

Chained : Maybe Text → List Migration → Set
Chained previous [] = ⊤
Chained nothing (migration ∷ rest) = Chained (just (Migration.name migration)) rest
Chained (just previous) (migration ∷ rest) =
  Names.Present previous (dependencies migration) × Chained (just (Migration.name migration)) rest

chainSatisfies : ∀ previous migrations → Chained previous (chain previous migrations)
chainSatisfies previous [] = tt
chainSatisfies nothing (migration ∷ rest) = chainSatisfies (just (Migration.name migration)) rest
chainSatisfies (just previous) (migration ∷ rest) rewrite namePreserved previous migration =
  includesPrevious previous migration , chainSatisfies (just (Migration.name migration)) rest

chainIdempotent : ∀ previous migrations → chain previous (chain previous migrations) ≡ chain previous migrations
chainIdempotent previous [] = refl
chainIdempotent nothing (migration ∷ rest) =
  cong (migration ∷_) (chainIdempotent (just (Migration.name migration)) rest)
chainIdempotent (just previous) (migration ∷ rest)
  rewrite namePreserved previous migration | addIdempotent previous migration =
    cong (add previous migration ∷_) (chainIdempotent (just (Migration.name migration)) rest)
