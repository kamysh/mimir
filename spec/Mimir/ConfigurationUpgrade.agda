{-# OPTIONS --safe #-}
-- Upgrade edits only operational metadata; the parsed application payload and
-- comments are preserved by the TOML document editor. No fallback on malformed
-- input and no downgrade of a future format. Publication uses the existing
-- owned-temporary-file, fsync, rename protocol; no backup is produced.
module Mimir.ConfigurationUpgrade where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Validation using (Fault)
import Mimir.OperationalConfiguration as O

module Document (Payload : Set) where
  record Before : Set where
    constructor before
    field version : Maybe ℕ; logging : O.Logging; payload : Payload
  record After : Set where
    constructor after
    field operations : O.Admitted; payload : Payload
  data Failure : Set where futureVersion : Failure; invalid : Fault → Failure

  validate : Before → Failure ⊎ After
  validate old with O.admit (O.settings O.formatVersion (Before.logging old))
  ... | inj₁ fault = inj₁ (invalid fault)
  ... | inj₂ accepted = inj₂ (after accepted (Before.payload old))

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
  payloadPreserved old .(after accepted (Before.payload old)) refl | inj₂ accepted = refl

  -- Startup requires the admitted value, so the new package cannot execute
  -- application I/O using absent or incompatible operational settings.
  data Started : After → Set where start : ∀ ready → Started ready
  startedCompatible : ∀ ready → Started ready →
    O.Settings.version (O.Admitted.value (After.operations ready)) ≡ O.formatVersion
  startedCompatible ready _ = O.acceptedVersion (After.operations ready)
