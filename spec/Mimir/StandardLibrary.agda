{-# OPTIONS --safe #-}
-- Supplied library operations, not implementations or proofs of Rust/Serde,
-- Unicode codecs, UUID formatting or SHA-256. No instance is assumed here.
-- Mimir's rules concern the supplied results and their use by the application.
module Mimir.StandardLibrary where

open import Data.Fin using (Fin)
open import Data.Bool using (Bool)
open import Data.List using (List; length)
open import Data.Maybe using (Maybe; just)
open import Data.Nat using (ℕ; _≤_; _*_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Mimir.Text using (Text; byteLength)
open import Mimir.Bits using (Byte)
open import Mimir.Binary64 using (power)
import Mimir.FloatValue as Float
import Mimir.StructuredValue as Value
import Mimir.ExactBytes as Bytes
import Mimir.UUIDGroups as UUID
import Mimir.Validation as Validation

record JSONError : Set where
  constructor jsonError
  field message : Text; line column : ℕ

data JSONResult : Set where
  parsed : Value.Value → JSONResult
  rejected : JSONError → JSONResult
  panicked : Text → JSONResult

-- Typed deserialization is a library boundary too. Its token view belongs
-- to that schema's visitor: unknown values need not be materialized as a
-- generic serde_json::Value. A success must retain Mimir's field-decoding
-- equation. There is no locally constructed library implementation.
data ReadResult {A : Set} (decode : Value.Value → Validation.Fault ⊎ A) : Set where
  decoded : ∀ raw value → decode raw ≡ inj₂ value → ReadResult decode
  syntaxError : JSONError → ReadResult decode
  schemaError : Validation.Fault → ReadResult decode
  decodePanicked : Text → ReadResult decode

record Contract : Set₁ where
  field
    cast : Fin (power 64) → Float.Number
    -- Generic Value parsing uses library object normalization.
    jsonValue : List Byte → JSONResult
    -- MCP's Serde visitor observes every member before map insertion. This
    -- separate boundary retains repeated names for pre-dispatch admission.
    jsonMembers : List Byte → JSONResult
    readTyped : ∀ {A : Set} (decode : Value.Value → Validation.Fault ⊎ A) → List Byte → ReadResult decode
    compactJSON : Value.Value → List Byte
    prettyJSON : Value.Value → Text ⊎ List Byte
    decodeUTF8 : List Byte → Text ⊎ Text
    encodeUTF8 : Text → List Byte
    lossyUTF8 : List Byte → Text
    -- Standard replacement decoding expands at most threefold. Mimir uses
    -- this external guarantee only to bound its own selected error window.
    lossyByteBound : ∀ input → byteLength (lossyUTF8 input) ≤ 3 * length input
    sha256 : List Byte → Bytes.Bytes 32
    parseUUID : Text → Maybe UUID.UUID
    formatUUID : UUID.UUID → Text
    uuidRoundTrip : ∀ value → parseUUID (formatUUID value) ≡ just value
    uuidFromRandom : Bool → UUID.UUID → UUID.UUID

readRecord : ∀ {A : Set} (library : Contract) (decode : Value.Value → Validation.Fault ⊎ A) →
  List Byte → ReadResult decode
readRecord library decode input = Contract.readTyped library decode input
