{-# OPTIONS --safe #-}
-- Each acknowledged file operation names the exact locked directory, file,
-- decoded schema or serialized value and durability receipt. This binds the
-- outbox/cache/cursor protocols to one filesystem implementation contract.
module Mimir.NotificationFileBinding where

open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Mimir.Text using (Text)
import Mimir.NotificationCodec as Codec
import Mimir.NotificationStorage as Storage
import Mimir.NotificationDelivery as Delivery
import Mimir.Validation as Validation

module Bound (library : Codec.JSONLibrary) (sizeMaximum clockMaximum : ℕ) where
  private
    module C = Codec.Decode library sizeMaximum clockMaximum
  module F = Storage.File ℕ Text
  private
    module R name = F.Decoded (Codec.Value name) Validation.Fault (C.bytes name)

  readResult : ∀ name → F.FS.Result (Maybe (R.R.Read name 1048576)) →
    F.FS.Error ⊎ Maybe (Codec.Value name)
  readResult name (inj₁ failure) = inj₁ failure
  readResult name (inj₂ nothing) = inj₂ nothing
  readResult name (inj₂ (just value)) = inj₂ (just (R.R.Read.value value))

  data Read (held : F.L.Locked) (name : Storage.Name) : F.FS.Error ⊎ Maybe (Codec.Value name) → Set where
    observed : ∀ events reply → F.FS.Runs (R.read name held name) events reply → Read held name (readResult name reply)

  writeResult : F.WriteResult → Delivery.WriteReceipt
  writeResult F.oversized = Delivery.refused
  writeResult (F.replaced F.W.committed) = Delivery.durable
  writeResult (F.replaced (F.W.unchanged _ _)) = Delivery.refused
  writeResult (F.replaced (F.W.uncertain _ _)) = Delivery.uncertain

  data Written (held : F.L.Locked) (name : Storage.Name) (value : Codec.Value name) : Delivery.WriteReceipt → Set where
    encodingFailed : ∀ error → Codec.JSONLibrary.pretty library (Codec.encode name value) ≡ inj₁ error →
      Written held name value Delivery.refused
    stored : ∀ id bytes events outcome →
      Codec.JSONLibrary.pretty library (Codec.encode name value) ≡ inj₂ bytes →
      F.FS.Runs (F.write held name id bytes) events outcome → Written held name value (writeResult outcome)
