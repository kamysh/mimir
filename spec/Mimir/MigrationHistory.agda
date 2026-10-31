{-# OPTIONS --safe #-}
-- Legacy sqlx history admission in Kryzhen: row checksum checks precede the
-- prefix check. Receipt lookup uses last-wins insertion, as HashMap::collect
-- does. Description text is not consulted by this validation.
module Mimir.MigrationHistory where

open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.FiniteTable as Finite
import Mimir.MigrationValidation as Validation

module History (Version Checksum Name Payload : Set)
  (versionEqual : DecidableEquality Version) (checksumEqual : DecidableEquality Checksum)
  (_<_ : Version → Version → Set) (before? : ∀ left right → Dec (left < right)) where

  record Entry : Set where
    constructor receiptEntryRecord
    field version : Version; name : Name; checksum : Checksum; payload : Payload
  open Entry

  record Row : Set where
    constructor row
    field version : Version; checksum : Checksum

  module Index = Finite.Tables Version Entry versionEqual
  module Versions = Validation.Validate Version Checksum versionEqual checksumEqual

  collect : Index.Table → List Entry → Index.Table
  collect index [] = index
  collect index (entry ∷ rest) = collect (Index.put (version entry) entry index) rest

  receiptIndex : List Entry → Index.Table
  receiptIndex = collect Index.empty

  data Error : Set where
    unknownMigration : Version → Error
    receiptMismatch : Name → Checksum → Checksum → Error
    inconsistentHistory : Version → Version → Error

  Matches : Index.Table → Row → Set
  Matches index observed = Σ Entry λ entry →
    Index.lookup index (Row.version observed) ≡ just entry × Row.checksum observed ≡ checksum entry

  data Checked (P : Set) : Set where
    accepted : P → Checked P
    rejected : Error → ¬ P → Checked P

  inspectRow : ∀ index observed → Checked (Matches index observed)
  inspectRow index observed with Index.lookup index (Row.version observed) in found
  ... | nothing = rejected (unknownMigration (Row.version observed)) λ where
    (entry , () , matches)
  ... | just receiptEntry with checksumEqual (Row.checksum observed) (checksum receiptEntry)
  ...   | yes same = accepted (receiptEntry , refl , same)
  ...   | no different = rejected
    (receiptMismatch (name receiptEntry) (checksum receiptEntry) (Row.checksum observed)) λ where
      (entry , refl , same) → different same

  inspectRows : ∀ index rows → Checked (All (Matches index) rows)
  inspectRows index [] = accepted []
  inspectRows index (observed ∷ rest) with inspectRow index observed
  ... | rejected error invalid = rejected error (λ { (head ∷ tail) → invalid head })
  ... | accepted head with inspectRows index rest
  ...   | rejected error invalid = rejected error (λ { (head ∷ tail) → invalid tail })
  ...   | accepted tail = accepted (head ∷ tail)

  PriorPresent : List Version → Version → Entry → Set
  PriorPresent versions present earlier = version earlier < present → version earlier ∈ versions

  inspectPrior : ∀ versions present earlier → Checked (PriorPresent versions present earlier)
  inspectPrior versions present earlier with before? (version earlier) present
  ... | no notBefore = accepted (λ before → ⊥-elim (notBefore before))
  ... | yes before with Versions.member? (version earlier) versions
  ...   | yes found = accepted (λ _ → found)
  ...   | no absent = rejected (inconsistentHistory (version earlier) present)
    (λ admitted → absent (admitted before))

  inspectPriors : ∀ versions present entries → Checked (All (PriorPresent versions present) entries)
  inspectPriors versions present [] = accepted []
  inspectPriors versions present (entry ∷ rest) with inspectPrior versions present entry
  ... | rejected error invalid = rejected error (λ { (head ∷ tail) → invalid head })
  ... | accepted head with inspectPriors versions present rest
  ...   | rejected error invalid = rejected error (λ { (head ∷ tail) → invalid tail })
  ...   | accepted tail = accepted (head ∷ tail)

  inspectPrefix : ∀ versions entries present →
    Checked (All (λ version → All (PriorPresent versions version) entries) present)
  inspectPrefix versions entries [] = accepted []
  inspectPrefix versions entries (present ∷ rest) with inspectPriors versions present entries
  ... | rejected error invalid = rejected error (λ { (head ∷ tail) → invalid head })
  ... | accepted head with inspectPrefix versions entries rest
  ...   | rejected error invalid = rejected error (λ { (head ∷ tail) → invalid tail })
  ...   | accepted tail = accepted (head ∷ tail)

  Admitted : List Entry → List Row → Set
  Admitted receipt rows = All (Matches (receiptIndex receipt)) rows ×
    All (λ present → All (PriorPresent (map Row.version rows) present) receipt) (map Row.version rows)

  validate : ∀ receipt rows → Checked (Admitted receipt rows)
  validate receipt rows with inspectRows (receiptIndex receipt) rows
  ... | rejected error invalid = rejected error (λ { (matches , prefix) → invalid matches })
  ... | accepted matches with inspectPrefix (map Row.version rows) receipt (map Row.version rows)
  ...   | rejected error invalid = rejected error (λ { (matches , prefix) → invalid prefix })
  ...   | accepted prefix = accepted (matches , prefix)

  result : ∀ receipt rows → Error ⊎ ⊤
  result receipt rows with validate receipt rows
  ... | rejected error invalid = inj₁ error
  ... | accepted admitted = inj₂ tt

  sound : ∀ receipt rows → result receipt rows ≡ inj₂ tt → Admitted receipt rows
  sound receipt rows with validate receipt rows
  ... | rejected error invalid = λ ()
  ... | accepted admitted = λ _ → admitted

  complete : ∀ receipt rows → Admitted receipt rows → result receipt rows ≡ inj₂ tt
  complete receipt rows admitted with validate receipt rows
  ... | rejected error invalid = ⊥-elim (invalid admitted)
  ... | accepted valid = refl
