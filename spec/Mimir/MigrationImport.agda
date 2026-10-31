{-# OPTIONS --safe #-}
-- Legacy import orchestration as observed by db.rs, which discards the
-- successful cloned Receipt. Imported rows commit separately; dropping the
-- legacy table is a final, separate awaited statement.
module Mimir.MigrationImport where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.Effects as Effects
import Mimir.MigrationHistory as History
open import Mimir.Collections using (module Equality)

module Import (Problem Version Checksum Name Schema Migration Payload : Set)
  (versionEqual : DecidableEquality Version) (checksumEqual : DecidableEquality Checksum)
  (nameEqual : DecidableEquality Name)
  (_<_ : Version → Version → Set) (before? : ∀ left right → Dec (left < right)) where

  module H = History.History Version Checksum Name Payload versionEqual checksumEqual _<_ before?
  module Names = Equality Name nameEqual

  record Pure : Set where
    field
      lookupMigration : Name → Maybe Migration
      prepareImported : H.Entry → Maybe Name → Migration → Migration

  data Error : Set where
    external : Problem → Error
    invalidHistory : H.Error → Error
    missingMigration : Name → Error

  Result : Set → Set
  Result A = Error ⊎ A

  data Effect : Set where
    legacyExists readSuccessfulRows ensureSchema readCanonicalNames currentSchema dropLegacyTable : Effect
    recordApplied : Migration → Schema → Effect

  Reply : Effect → Set
  Reply legacyExists = Result Bool
  Reply readSuccessfulRows = Result (List H.Row)
  Reply readCanonicalNames = Result (List Name)
  Reply currentSchema = Result Schema
  Reply _ = Result ⊤

  module E = Effects.Protocol Effect Reply
  open E public

  selected : List Version → List H.Entry → List H.Entry
  selected versions [] = []
  selected versions (entry ∷ rest) with H.Versions.member? (H.Entry.version entry) versions
  ... | yes present = entry ∷ selected versions rest
  ... | no absent = selected versions rest

  module Run (pure : Pure) where
    open Pure pure

    entries : List Name → Schema → Maybe Name → List H.Entry → Script (Result ⊤)
    entries snapshot schema previous [] = done (inj₂ tt)
    entries snapshot schema previous (entry ∷ rest) with Names.present? (H.Entry.name entry) snapshot
    ... | yes already = entries snapshot schema (just (H.Entry.name entry)) rest
    ... | no missing with lookupMigration (H.Entry.name entry)
    ...   | nothing = done (inj₁ (missingMigration (H.Entry.name entry)))
    ...   | just migration = ask (recordApplied (prepareImported entry previous migration) schema) λ where
      (inj₁ error) → done (inj₁ error)
      (inj₂ tt) → entries snapshot schema (just (H.Entry.name entry)) rest

    -- The predecessor for reconstruction advances even when an existing
    -- canonical row is skipped, matching the source's applied_names[i-1].
    alreadyRecordedStillPrecedes : ∀ snapshot schema previous entry rest →
      Names.Present (H.Entry.name entry) snapshot →
      entries snapshot schema previous (entry ∷ rest) ≡
        entries snapshot schema (just (H.Entry.name entry)) rest
    alreadyRecordedStillPrecedes snapshot schema previous entry rest present
      with Names.present? (H.Entry.name entry) snapshot
    ... | yes already = refl
    ... | no absent with absent present
    ...   | ()

    writeThenDrop : List Name → Schema → List H.Entry → Script (Result ⊤)
    writeThenDrop snapshot schema applied = entries snapshot schema nothing applied >>= λ where
      (inj₁ error) → done (inj₁ error)
      (inj₂ tt) → ask dropLegacyTable done

    readSchema : List Name → List H.Entry → Script (Result ⊤)
    readSchema snapshot applied = ask currentSchema λ where
      (inj₁ error) → done (inj₁ error)
      (inj₂ schema) → writeThenDrop snapshot schema applied

    readSnapshot : List H.Entry → Script (Result ⊤)
    readSnapshot applied = ask readCanonicalNames λ where
      (inj₁ error) → done (inj₁ error)
      (inj₂ snapshot) → readSchema snapshot applied

    ensure : List H.Entry → Script (Result ⊤)
    ensure applied = ask ensureSchema λ where
      (inj₁ error) → done (inj₁ error)
      (inj₂ tt) → readSnapshot applied

    check : List H.Entry → List H.Row → Script (Result ⊤)
    check receipt rows with H.result receipt rows
    ... | inj₁ invalid = done (inj₁ (invalidHistory invalid))
    ... | inj₂ tt = ensure (selected (map H.Row.version rows) receipt)

    readRows : List H.Entry → Script (Result ⊤)
    readRows receipt = ask readSuccessfulRows λ where
      (inj₁ error) → done (inj₁ error)
      (inj₂ rows) → check receipt rows

    start : List H.Entry → Script (Result ⊤)
    start receipt = ask legacyExists λ where
      (inj₁ error) → done (inj₁ error)
      (inj₂ false) → done (inj₂ tt)
      (inj₂ true) → readRows receipt

    absentLegacyOnlyQueriesExistence : ∀ receipt events result →
      Runs (start receipt) ((legacyExists , inj₂ false) ∷ events) result →
      events ≡ [] × result ≡ inj₂ tt
    absentLegacyOnlyQueriesExistence _ _ _ (replied _ _ _ (returned _)) = refl , refl

    rejectedHistoryHasNoFurtherEffects : ∀ receipt rows invalid → H.result receipt rows ≡ inj₁ invalid →
      ∀ events result → Runs (check receipt rows) events result →
      events ≡ [] × result ≡ inj₁ (invalidHistory invalid)
    rejectedHistoryHasNoFurtherEffects receipt rows invalid rejected rewrite rejected =
      λ { _ _ (returned _) → refl , refl }
