{-# OPTIONS --safe #-}
-- Concrete data projection and reconstruction for the legacy receipt. The
-- SHA-384 hex from sqlx is used for admission; the reconstructed canonical
-- row retains the embedded migration's SHA-256 checksum and original script.
module Mimir.MigrationImportValues where

open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Integer using (ℤ; _≟_; _<_; _<?_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.ExactBytes as Bytes
import Mimir.MigrationLedger as Ledger
import Mimir.MigrationHistory as History
import Mimir.MigrationImport as Import

record EntryMetadata : Set where
  constructor entryMetadata
  field sqlxDescription : Text; filename : Text

module H = History.History ℤ Text Text EntryMetadata _≟_ _≟Text_ _<_ _<?_

record Receipt : Set where
  constructor receipt
  field entries : List H.Entry; newlyConverted : ℕ; alreadyImported : Bool

-- The PostgreSQL/library adapter supplies the lowercase hex checksum.
-- Its byte-to-hex conversion is external; equality/admission stays below.
record DatabaseRow : Set where
  constructor databaseRow
  field version : ℤ; description : Text; checksum : Text

row : DatabaseRow → H.Row
row observed = H.row (DatabaseRow.version observed) (DatabaseRow.checksum observed)

rows : List DatabaseRow → List H.Row
rows = map row

description : H.Entry → Text
description entry with EntryMetadata.sqlxDescription (H.Entry.payload entry)
... | [] = H.Entry.name entry
... | text@(_ ∷ _) = text

requirements : Maybe Text → List Text
requirements nothing = []
requirements (just previous) = previous ∷ []

prepare : H.Entry → Maybe Text → Ledger.Migration → Ledger.Migration
prepare entry previous original = Ledger.migrationRecord (H.Entry.name entry)
  (Ledger.metadata (description entry) (requirements previous)
    (Ledger.Metadata.checksum (Ledger.Migration.payload original))
    (Ledger.Metadata.script (Ledger.Migration.payload original)))

find : Text → List Ledger.Migration → Maybe Ledger.Migration
find query [] = nothing
find query (migration ∷ rest) with query ≟Text Ledger.Migration.name migration
... | yes same = just migration
... | no different = find query rest

originalChecksumPreserved : ∀ entry previous original →
  Ledger.Metadata.checksum (Ledger.Migration.payload (prepare entry previous original)) ≡
    Ledger.Metadata.checksum (Ledger.Migration.payload original)
originalChecksumPreserved entry previous original = refl

originalScriptPreserved : ∀ entry previous original →
  Ledger.Metadata.script (Ledger.Migration.payload (prepare entry previous original)) ≡
    Ledger.Metadata.script (Ledger.Migration.payload original)
originalScriptPreserved entry previous original = refl

predecessorIsReconstructed : ∀ entry previous original →
  Ledger.Metadata.requires (Ledger.Migration.payload (prepare entry previous original)) ≡ requirements previous
predecessorIsReconstructed entry previous original = refl

databaseDescriptionDoesNotAffectAdmission : ∀ version firstDescription secondDescription checksum →
  row (databaseRow version firstDescription checksum) ≡ row (databaseRow version secondDescription checksum)
databaseDescriptionDoesNotAffectAdmission version firstDescription secondDescription checksum = refl

module Concrete (Problem : Set) where
  module I = Import.Import Problem ℤ Text Text Text Ledger.Migration EntryMetadata
    _≟_ _≟Text_ _≟Text_ _<_ _<?_

  pure : List Ledger.Migration → I.Pure
  pure migrations = record { lookupMigration = λ name → find name migrations ; prepareImported = prepare }

  module Run (migrations : List Ledger.Migration) where
    module Program = I.Run (pure migrations)
