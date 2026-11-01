{-# OPTIONS --safe #-}
-- Upgrade edits operational metadata and removes retired review limits; unrelated payload and
-- comments are preserved by the TOML document editor. No fallback on malformed
-- input and no downgrade of a future format. Publication uses the existing
-- owned-temporary-file, fsync, rename protocol; no backup is produced.
module Mimir.ConfigurationUpgrade where

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.List using (List; []; _∷_)
open import Data.String using (toList)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.StructuredValue as V
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Mimir.Validation using (Fault)
import Mimir.OperationalConfiguration as O

-- Only these obsolete application budgets are removed. Other settings retain
-- their values and order, including model/provider credentials.
retired : Text → Bool
retired key = (does (key ≟Text toList "timeout_seconds")) ∨ (does (key ≟Text toList "max_calls")) ∨
  (does (key ≟Text toList "max_output_tokens")) ∨ (does (key ≟Text toList "max_budget_usd"))

Fields = List (Text × V.Value)

removeRetired : Fields → Fields
removeRetired [] = []
removeRetired ((key , value) ∷ rest) with retired key
... | true = removeRetired rest
... | false = (key , value) ∷ removeRetired rest

-- A receipt accounts for every input setting; only a retired key can disappear.
data Migration : Fields → Fields → Set where
  empty : Migration [] []
  removed : ∀ key value before after → retired key ≡ true → Migration before after →
    Migration ((key , value) ∷ before) after
  preserved : ∀ key value before after → retired key ≡ false → Migration before after →
    Migration ((key , value) ∷ before) ((key , value) ∷ after)

migrationComplete : ∀ fields → Migration fields (removeRetired fields)
migrationComplete [] = empty
migrationComplete ((key , value) ∷ rest) with retired key in eq
... | true = removed key value rest (removeRetired rest) eq (migrationComplete rest)
... | false = preserved key value rest (removeRetired rest) eq (migrationComplete rest)

migrationIdempotent : ∀ fields → removeRetired (removeRetired fields) ≡ removeRetired fields
migrationIdempotent [] = refl
migrationIdempotent ((key , value) ∷ rest) with retired key in eq
... | true = migrationIdempotent rest
... | false rewrite eq = cong ((key , value) ∷_) (migrationIdempotent rest)

upgradeLlm : Maybe Fields → Maybe Fields
upgradeLlm nothing = nothing
upgradeLlm (just fields) = just (removeRetired fields)

module Document (Payload : Set) where
  record Before : Set where
    constructor before
    field version : Maybe ℕ; logging : O.Logging; llm : Maybe Fields; payload : Payload
  record After : Set where
    constructor after
    field operations : O.Admitted; llm : Maybe Fields; payload : Payload
  data Failure : Set where futureVersion : Failure; invalid : Fault → Failure

  validate : Before → Failure ⊎ After
  validate old with O.admit (O.settings O.formatVersion (Before.logging old))
  ... | inj₁ fault = inj₁ (invalid fault)
  ... | inj₂ accepted = inj₂ (after accepted (upgradeLlm (Before.llm old)) (Before.payload old))

  upgrade : Before → Failure ⊎ After
  upgrade old with Before.version old
  ... | nothing = validate old
  ... | just version with version ≟ O.formatVersion
  ...   | yes _ = validate old
  ...   | no _ = inj₁ futureVersion

  payloadPreserved : ∀ old new → validate old ≡ inj₂ new → After.payload new ≡ Before.payload old
  payloadPreserved old new proof with O.admit (O.settings O.formatVersion (Before.logging old))
  ... | inj₁ fault with proof
  ...   | ()
  payloadPreserved old .(after accepted (upgradeLlm (Before.llm old)) (Before.payload old)) refl | inj₂ accepted = refl

  -- Startup requires the admitted value, so the new package cannot execute
  -- application I/O using absent or incompatible operational settings.
  data Started : After → Set where start : ∀ ready → Started ready
  startedCompatible : ∀ ready → Started ready →
    O.Settings.version (O.Admitted.value (After.operations ready)) ≡ O.formatVersion
  startedCompatible ready _ = O.acceptedVersion (After.operations ready)
