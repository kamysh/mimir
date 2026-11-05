{-# OPTIONS --safe #-}
-- Import historical item IDs without generating replacements. Historical
-- rows are supplied in PostgreSQL's observation order; an existing owner wins
-- even if a historical record names different provenance for the same ID.
module Mimir.ItemOwnerBackfill where

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (Σ; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans)
import Mimir.ItemOwners as Owners
import Mimir.DatabaseTransaction as Database

record Row : Set where
  constructor historical
  field identity : ℕ; owner : Owners.Owner

importOne : Row → Owners.Registry → Owners.Registry
importOne row before with before (Row.identity row)
... | just existing = before
... | nothing = Owners.Store.write (Row.identity row) (just (Row.owner row)) before

backfill : List Row → Owners.Registry → Owners.Registry
backfill [] before = before
backfill (row ∷ rest) before = backfill rest (importOne row before)

existingRowUnchanged : ∀ row before owner → before (Row.identity row) ≡ just owner →
  importOne row before ≡ before
existingRowUnchanged row before owner present rewrite present = refl

missingRowImported : ∀ row before → before (Row.identity row) ≡ nothing →
  importOne row before (Row.identity row) ≡ just (Row.owner row)
missingRowImported row before absent rewrite absent =
  Owners.Store.write-own (Row.identity row) (just (Row.owner row)) before

justNotNothing : ∀ (owner : Owners.Owner) → just owner ≢ nothing
justNotNothing owner ()

importPreservesExisting : ∀ row before identity old → before identity ≡ just old →
  importOne row before identity ≡ just old
importPreservesExisting row before identity old original
  with before (Row.identity row) in reservation
... | just existing = original
... | nothing with identity ≟ Row.identity row
...   | yes refl = ⊥-elim (justNotNothing old (trans (sym original) reservation))
...   | no different = original

existingOwnersPreserved : ∀ rows before identity old → before identity ≡ just old →
  backfill rows before identity ≡ just old
existingOwnersPreserved [] before identity old original = original
existingOwnersPreserved (row ∷ rest) before identity old original =
  existingOwnersPreserved rest (importOne row before) identity old
    (importPreservesExisting row before identity old original)

Recorded : Owners.Registry → Row → Set
Recorded registry row = Σ Owners.Owner (λ owner → registry (Row.identity row) ≡ just owner)

importRecordsIdentity : ∀ row before → Recorded (importOne row before) row
importRecordsIdentity row before with before (Row.identity row) in found
... | just old = old , found
... | nothing = Row.owner row , Owners.Store.write-own (Row.identity row) (just (Row.owner row)) before

everyHistoricalIdentityRecorded : ∀ rows before → All (Recorded (backfill rows before)) rows
everyHistoricalIdentityRecorded [] before = []
everyHistoricalIdentityRecorded (row ∷ rest) before
  with importRecordsIdentity row before
... | owner , recorded =
  (owner , existingOwnersPreserved rest (importOne row before) (Row.identity row) owner recorded)
  ∷ everyHistoricalIdentityRecorded rest (importOne row before)

recordedHistoryUnchanged : ∀ rows before → All (Recorded before) rows → backfill rows before ≡ before
recordedHistoryUnchanged [] before [] = refl
recordedHistoryUnchanged (row ∷ rest) before ((owner , found) ∷ recorded)
  rewrite existingRowUnchanged row before owner found = recordedHistoryUnchanged rest before recorded

backfillIdempotent : ∀ rows before → backfill rows (backfill rows before) ≡ backfill rows before
backfillIdempotent rows before = recordedHistoryUnchanged rows (backfill rows before)
  (everyHistoricalIdentityRecorded rows before)

importUnmentionedUnchanged : ∀ row before identity → identity ≢ Row.identity row →
  importOne row before identity ≡ before identity
importUnmentionedUnchanged row before identity different with before (Row.identity row)
... | just old = refl
... | nothing = Owners.Store.write-other (Row.identity row) identity (just (Row.owner row)) before different

unmentionedUnchanged : ∀ rows before identity → All (λ row → identity ≢ Row.identity row) rows →
  backfill rows before identity ≡ before identity
unmentionedUnchanged [] before identity [] = refl
unmentionedUnchanged (row ∷ rest) before identity (different ∷ remaining) = trans
  (unmentionedUnchanged rest (importOne row before) identity remaining)
  (importUnmentionedUnchanged row before identity different)

firstHistoricalOwnerRetained : ∀ row rest before → before (Row.identity row) ≡ nothing →
  backfill (row ∷ rest) before (Row.identity row) ≡ just (Row.owner row)
firstHistoricalOwnerRetained row rest before absent =
  existingOwnersPreserved rest (importOne row before) (Row.identity row) (Row.owner row)
    (missingRowImported row before absent)

publicationPreservesExisting : ∀ rows before receipt actual identity old →
  Database.Atomic before (backfill rows before) receipt actual → before identity ≡ just old →
  actual identity ≡ just old
publicationPreservesExisting rows before receipt actual identity old publication original =
  Database.invariantPreserved (λ registry → registry identity ≡ just old) publication original
    (existingOwnersPreserved rows before identity old original)

abortedBackfillUnchanged : ∀ rows before actual →
  Database.Atomic before (backfill rows before) Database.aborted actual → actual ≡ before
abortedBackfillUnchanged rows before actual Database.abortedNone = refl
