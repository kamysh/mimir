{-# OPTIONS --safe #-}
-- Mimir accepts UUID-valued string fields through the supplied UUID library.
-- The 128-bit value carrier is retained; spelling, parsing and formatting
-- correctness are external library guarantees.
import Mimir.StandardLibrary
module Mimir.UUIDSchema (library : Mimir.StandardLibrary.Contract) where

open import Data.List using ([])
open import Data.Maybe using (just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Validation using (Fault; fault; malformedInput)
import Mimir.StructuredValue as V
import Mimir.StandardLibrary as Library
import Mimir.UUIDGroups as UUID

decode : V.Value → Fault ⊎ UUID.UUID
decode (V.string text) with Library.Contract.parseUUID library text
... | nothing = inj₁ (fault [] malformedInput "invalid UUID")
... | just value = inj₂ value
decode _ = inj₁ (fault [] malformedInput "expected a UUID string")

encode : UUID.UUID → V.Value
encode value = V.string (Library.Contract.formatUUID library value)

roundTrip : ∀ value → decode (encode value) ≡ inj₂ value
roundTrip value rewrite Library.Contract.uuidRoundTrip library value = refl
