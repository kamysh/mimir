{-# OPTIONS --safe #-}
-- Scalar field visitors for private judge state. Native state reads collapse
-- every serde failure to "invalid state report"; these faults retain useful
-- model structure without claiming serde's private diagnostic wording.
module Mimir.JudgeStatePrimitives where

open import Data.List using ([])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤_)
open import Data.Integer using (ℤ; +_; _≤?_)
import Data.Integer as Int
open import Data.Product using (_×_; _,_; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Mimir.Text using (Text)
import Mimir.StructuredValue as JSON
import Mimir.Validation as V
import Mimir.Binary64 as Binary
import Mimir.SignedMachine as Signed
import Mimir.UUIDGroups as UUID
import Mimir.UUIDSchema as UUIDCodecDependency
import Mimir.StandardLibrary as Library
import Mimir.SerdeSequence as Sequence
import Mimir.SerdeStruct as Struct

module I64 = Signed.Width 63

uint : ℕ → JSON.Value → V.Fault ⊎ ℕ
uint maximum raw with JSON.uint maximum raw
... | V.rejected failure invalid = inj₁ failure
... | V.accepted (number , proof) = inj₂ number

uintRoundTrip : ∀ maximum number → number ≤ maximum → uint maximum (JSON.unsigned number) ≡ inj₂ number
uintRoundTrip maximum number bounded with JSON.uint maximum (JSON.unsigned number)
... | V.rejected failure impossible = ⊥-elim (impossible (number , JSON.fromUnsigned number bounded))
... | V.accepted (.number , JSON.fromUnsigned .number actual) = refl

uintSound : ∀ maximum raw number → uint maximum raw ≡ inj₂ number → JSON.UIntValue maximum raw number
uintSound maximum raw number observed with JSON.uint maximum raw
... | V.rejected failure invalid with observed
...   | ()
uintSound maximum raw .number refl | V.accepted (number , proof) = proof

signedNumber : ℤ → V.Fault ⊎ ℤ
signedNumber number with I64.minimum ≤? number
... | no underflow = inj₁ (V.fault [] V.invalidNumber "integer below i64 range")
... | yes above with number ≤? I64.maximum
...   | no overflow = inj₁ (V.fault [] V.invalidNumber "integer above i64 range")
...   | yes below = inj₂ number

signed : JSON.Value → V.Fault ⊎ ℤ
signed (JSON.signed number) = signedNumber number
signed (JSON.unsigned number) = signedNumber (+ number)
signed other = inj₁ (V.fault [] V.malformedInput "expected an integer")

signedNumberRoundTrip : ∀ number → I64.InRange number → signedNumber number ≡ inj₂ number
signedNumberRoundTrip number (above , below) with I64.minimum ≤? number
... | no impossible = ⊥-elim (impossible above)
... | yes actualAbove with number ≤? I64.maximum
...   | no impossible = ⊥-elim (impossible below)
...   | yes actualBelow = refl

signedNumberSound : ∀ number result → signedNumber number ≡ inj₂ result → number ≡ result × I64.InRange number
signedNumberSound number result observed with I64.minimum ≤? number
... | no underflow with observed
...   | ()
signedNumberSound number result observed | yes above with number ≤? I64.maximum
... | no overflow with observed
...   | ()
signedNumberSound number .number refl | yes above | yes below = refl , above , below

module UUIDFields (library : Library.Contract) where
  module UUIDCodec = UUIDCodecDependency library
  uuid : JSON.Value → V.Fault ⊎ UUID.UUID
  uuid raw with UUIDCodec.decode raw
  ... | inj₁ failure = inj₁ (V.fault [] V.malformedInput "invalid UUID field")
  ... | inj₂ value = inj₂ value

  uuidRoundTrip : ∀ value → uuid (UUIDCodec.encode value) ≡ inj₂ value
  uuidRoundTrip value rewrite UUIDCodec.roundTrip value = refl


optionResult : ∀ {A : Set} → V.Fault ⊎ A → V.Fault ⊎ Maybe A
optionResult (inj₁ failure) = inj₁ failure
optionResult (inj₂ value) = inj₂ (just value)

option : ∀ {A : Set} → (JSON.Value → V.Fault ⊎ A) → JSON.Value → V.Fault ⊎ Maybe A
option decode JSON.null = inj₂ nothing
option decode raw = optionResult (decode raw)

required : ∀ name (A : Set) → (JSON.Value → V.Fault ⊎ A) → Sequence.Field
required name A decode = Sequence.fieldType name A decode nothing

defaulted : ∀ name (A : Set) → (JSON.Value → V.Fault ⊎ A) → A → Sequence.Field
defaulted name A decode fallback = Sequence.fieldType name A decode (just fallback)

optional : ∀ name (A : Set) → (JSON.Value → V.Fault ⊎ A) → Sequence.Field
optional name A decode = defaulted name (Maybe A) (option decode) nothing

recordResult : ∀ {A : Set} {fields} → (Sequence.Values fields → A) → Struct.Error ⊎ Sequence.Values fields → V.Fault ⊎ A
recordResult build (inj₁ failure) = inj₁ (V.fault [] V.malformedInput "invalid state record")
recordResult build (inj₂ values) = inj₂ (build values)

recordDecoder : ∀ {A : Set} fields → (Sequence.Values fields → A) → JSON.Value → V.Fault ⊎ A
recordDecoder fields build raw = recordResult build (Struct.read fields raw)

recordSuccess : ∀ {A : Set} fields (build : Sequence.Values fields → A) raw value → recordDecoder fields build raw ≡ inj₂ value →
  Σ (Sequence.Values fields) (λ values → Struct.Admitted fields raw values × build values ≡ value)
recordSuccess fields build raw value observed with Struct.read fields raw in decoded
... | inj₁ failure with observed
...   | ()
recordSuccess fields build raw .(build values) refl | inj₂ values = values , Struct.admittedSound fields raw values decoded , refl

u64Maximum : ℕ
u64Maximum = Binary.powerMinusOne 64
