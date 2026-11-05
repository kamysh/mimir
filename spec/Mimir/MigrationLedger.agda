{-# OPTIONS --safe #-}
-- Finite row semantics of the two INSERT ... ON CONFLICT DO NOTHING
-- statements. SQL execution/encoding correspondence is a separate obligation.
module Mimir.MigrationLedger where

open import Data.List using (List)
open import Data.Maybe using (just)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
open import Mimir.Collections using (pairEqual)
import Mimir.FiniteTable as Finite
import Mimir.ExactBytes as Bytes

record Metadata : Set where
  constructor metadata
  field
    description : Text
    requires : List Text
    checksum : Bytes.Bytes 32
    script : Text

record Migration : Set where
  constructor migrationRecord
  field name : Text; payload : Metadata
open Migration

module Canonical = Finite.Tables Text Metadata _≟Text_
associationEqual = pairEqual _≟Text_ _≟Text_
module Association = Finite.Tables (Text × Text) ⊤ associationEqual

record Ledger : Set where
  constructor ledger
  field canonical : Canonical.Table; associations : Association.Table
open Ledger public

WellFormed : Ledger → Set
WellFormed state = ∀ name schema →
  Association.lookup (associations state) (name , schema) ≡ just tt →
  Σ Metadata λ payload → Canonical.lookup (canonical state) name ≡ just payload

insertBoth : Migration → Text → Ledger → Ledger
insertBoth migration schema old = ledger
  (Canonical.insertAbsent (name migration) (payload migration) (canonical old))
  (Association.insertAbsent (name migration , schema) tt (associations old))

retainsCanonical : ∀ migration schema old query previous →
  Canonical.lookup (canonical old) query ≡ just previous →
  Canonical.lookup (canonical (insertBoth migration schema old)) query ≡ just previous
retainsCanonical migration schema old query previous =
  Canonical.insertRetainsLookup (name migration) (payload migration) (canonical old) query previous

-- Existing canonical rows are deliberately not overwritten, even if a new
-- caller supplies a different checksum. The separate admission pass must
-- reject mismatches; insertion itself is not checksum validation.
oldChecksumSurvives : ∀ migration schema old previous →
  Canonical.lookup (canonical old) (name migration) ≡ just previous →
  Canonical.lookup (canonical (insertBoth migration schema old)) (name migration) ≡ just previous
oldChecksumSurvives migration schema old previous =
  retainsCanonical migration schema old (name migration) previous

newAssociationHasCanonical : ∀ migration schema old →
  Σ Metadata λ stored →
    Canonical.lookup (canonical (insertBoth migration schema old)) (name migration) ≡ just stored
newAssociationHasCanonical migration schema old =
  Canonical.insertSome (name migration) (payload migration) (canonical old)

foreignKeysPreserved : ∀ migration schema old → WellFormed old → WellFormed (insertBoth migration schema old)
foreignKeysPreserved migration schema old valid query target present
  with associationEqual (query , target) (name migration , schema)
... | yes refl = newAssociationHasCanonical migration schema old
... | no different with valid query target
  (trans (Relation.Binary.PropositionalEquality.sym
    (Association.insertOther (name migration , schema) tt (associations old) (query , target) different)) present)
...   | previous , found = previous , retainsCanonical migration schema old query previous found

Equivalent : Ledger → Ledger → Set
Equivalent left right = Canonical.Equivalent (canonical left) (canonical right) ×
  Association.Equivalent (associations left) (associations right)

recordingIdempotent : ∀ migration schema old →
  Equivalent (insertBoth migration schema (insertBoth migration schema old)) (insertBoth migration schema old)
recordingIdempotent migration schema old =
  Canonical.insertIdempotent (name migration) (payload migration) (canonical old) ,
  Association.insertIdempotent (name migration , schema) tt (associations old)
