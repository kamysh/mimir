{-# OPTIONS --safe #-}
-- Mimir accepts UUID-valued string fields through the supplied UUID library.
-- UUIDs remain abstract; parsing is an external library operation.
import Mimir.StandardLibrary
module Mimir.UUIDSchema (library : Mimir.StandardLibrary.Contract) where

open import Data.List using ([])
open import Data.Maybe using (just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Mimir.Validation using (Fault; fault; malformedInput)
import Mimir.StructuredValue as V
import Mimir.StandardLibrary as Library
import Mimir.UUIDGroups as UUID

decode : V.Value → Fault ⊎ UUID.UUID
decode (V.string text) with Library.Contract.parseUUID library text
... | nothing = inj₁ (fault [] malformedInput "invalid UUID")
... | just value = inj₂ value
decode _ = inj₁ (fault [] malformedInput "expected a UUID string")
