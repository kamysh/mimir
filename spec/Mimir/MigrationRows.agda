{-# OPTIONS --safe #-}
-- Successful PostgreSQL row extraction is an input here. This module covers
-- the byte-length rejection and HashMap insertion/validation after extraction.
module Mimir.MigrationRows where

open import Data.List using (List; []; _∷_; length; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.ExactBytes as Bytes
import Mimir.FiniteTable as Finite
import Mimir.MigrationLedger as Ledger
import Mimir.MigrationValidation as Validation

Checksum = Bytes.Bytes 32
RawRow = Text × List Bytes.Byte
module Checksums = Finite.Tables Text Checksum _≟Text_
module Validate = Validation.Validate Text Checksum _≟Text_ Bytes.equal

data Error : Set where corruptChecksum : Text → ℕ → Error

load : Checksums.Table → List RawRow → Error ⊎ Checksums.Table
load before [] = inj₂ before
load before ((name , bytes) ∷ rest) with Bytes.read 32 bytes
... | Bytes.wrongLength different = inj₁ (corruptChecksum name (length bytes))
... | Bytes.accepted value exact = load (Checksums.put name value before) rest

loadApplied : List RawRow → Error ⊎ Checksums.Table
loadApplied = load Checksums.empty

RowsValid : List RawRow → Set
RowsValid rows = All (λ row → length (proj₂ row) ≡ 32) rows

loadSound : ∀ before rows after → load before rows ≡ inj₂ after → RowsValid rows
loadSound before [] after accepted = []
loadSound before ((name , bytes) ∷ rest) after accepted with Bytes.read 32 bytes
... | Bytes.wrongLength different with accepted
...   | ()
loadSound before ((name , bytes) ∷ rest) after accepted | Bytes.accepted value exact =
  Bytes.acceptedLength 32 bytes value exact ∷ loadSound (Checksums.put name value before) rest after accepted

data Complete (rows : List RawRow) (before : Checksums.Table) : Set where
  loaded : (after : Checksums.Table) → load before rows ≡ inj₂ after → Complete rows before

loadAccepted : ∀ before name bytes rest value exact →
  Bytes.read 32 bytes ≡ Bytes.accepted value exact →
  load before ((name , bytes) ∷ rest) ≡ load (Checksums.put name value before) rest
loadAccepted before name bytes rest value exact observed rewrite observed = refl

loadComplete : ∀ before rows → RowsValid rows → Complete rows before
loadComplete before [] [] = loaded before refl
loadComplete before ((name , bytes) ∷ rest) (valid ∷ remaining) with Bytes.read 32 bytes in observed
... | Bytes.wrongLength different with different valid
...   | ()
loadComplete before ((name , bytes) ∷ rest) (valid ∷ remaining) | Bytes.accepted value exact
  with loadComplete (Checksums.put name value before) rest remaining
... | loaded after accepted = loaded after
  (trans (loadAccepted before name bytes rest value exact observed) accepted)

loadDomain : ∀ before rows after → load before rows ≡ inj₂ after → ∀ query →
  Checksums.Contains after query → Checksums.Contains before query ⊎ (query ∈ map proj₁ rows)
loadDomain before [] .before refl query found = inj₁ found
loadDomain before ((name , bytes) ∷ rest) after accepted query found with Bytes.read 32 bytes
... | Bytes.wrongLength different with accepted
...   | ()
loadDomain before ((name , bytes) ∷ rest) after accepted query found | Bytes.accepted value exact
  with loadDomain (Checksums.put name value before) rest after accepted query found
... | inj₂ inRest = inj₂ (there inRest)
... | inj₁ prior with Checksums.putDomain name value before query prior
...   | inj₁ same = inj₂ (here same)
...   | inj₂ original = inj₁ original

loadDomainBack : ∀ before rows after → load before rows ≡ inj₂ after → ∀ query →
  Checksums.Contains before query ⊎ (query ∈ map proj₁ rows) → Checksums.Contains after query
loadDomainBack before [] .before refl query (inj₁ found) = found
loadDomainBack before [] .before refl query (inj₂ ())
loadDomainBack before ((name , bytes) ∷ rest) after accepted query included with Bytes.read 32 bytes
... | Bytes.wrongLength different with accepted
...   | ()
loadDomainBack before ((name , bytes) ∷ rest) after accepted query (inj₁ found) | Bytes.accepted value exact =
  loadDomainBack (Checksums.put name value before) rest after accepted query
    (inj₁ (Checksums.putDomainBack name value before query (inj₂ found)))
loadDomainBack before ((name , bytes) ∷ rest) after accepted query (inj₂ (here same)) | Bytes.accepted value exact =
  loadDomainBack (Checksums.put name value before) rest after accepted query
    (inj₁ (Checksums.putDomainBack name value before query (inj₁ same)))
loadDomainBack before ((name , bytes) ∷ rest) after accepted query (inj₂ (there found)) | Bytes.accepted value exact =
  loadDomainBack (Checksums.put name value before) rest after accepted query (inj₂ found)

loadedNamesComplete : ∀ rows after → loadApplied rows ≡ inj₂ after → ∀ query →
  query ∈ map proj₁ rows → Checksums.Contains after query
loadedNamesComplete rows after accepted query found =
  loadDomainBack Checksums.empty rows after accepted query (inj₂ found)

loadedNamesSound : ∀ rows after → loadApplied rows ≡ inj₂ after → ∀ query →
  Checksums.Contains after query → query ∈ map proj₁ rows
loadedNamesSound rows after accepted query found with loadDomain Checksums.empty rows after accepted query found
... | inj₂ present = present
... | inj₁ (stored , ())

entry : Ledger.Migration → Validate.Entry
entry migration = Ledger.Migration.name migration , Ledger.Metadata.checksum (Ledger.Migration.payload migration)

checkNames : List Ledger.Migration → Text ⊎ ⊤
checkNames migrations = Validate.checkNames (map Ledger.Migration.name migrations)

checkChecksums : List Ledger.Migration → Checksums.Table → Text ⊎ ⊤
checkChecksums migrations stored = Validate.checkChecksums (Checksums.lookup stored) (map entry migrations)

allNamesAdmitted : ∀ migrations → checkNames migrations ≡ inj₂ tt →
  Validate.Fresh [] (map Ledger.Migration.name migrations)
allNamesAdmitted migrations = Validate.namesSound (map Ledger.Migration.name migrations)

allChecksumsAdmitted : ∀ migrations stored → checkChecksums migrations stored ≡ inj₂ tt →
  All (Validate.Compatible (Checksums.lookup stored)) (map entry migrations)
allChecksumsAdmitted migrations stored =
  Validate.checksumsSound (Checksums.lookup stored) (map entry migrations)
