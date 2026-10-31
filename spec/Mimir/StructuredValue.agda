{-# OPTIONS --safe #-}
-- Structured input values before per-record decoding. Integer and floating
-- variants remain distinct: a floating 1.0 is not a u16/usize field value.
-- Raw UTF-8/JSON parsing and float conversion construct this representation.
module Mimir.StructuredValue where

open import Data.Bool using (Bool)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤_; _≤?_)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (fromList)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.Binary64 using (Number)
open import Mimir.Validation
import Mimir.JsonObjects as Objects

data Value : Set where
  null : Value
  boolean : Bool → Value
  string : Text → Value
  signed : ℤ → Value
  unsigned : ℕ → Value
  floating : Number → Value
  array : List Value → Value
  object : List (Text × Value) → Value

module Object = Objects.Object Value

data UIntValue (maximum : ℕ) : Value → ℕ → Set where
  fromUnsigned : ∀ n → n ≤ maximum → UIntValue maximum (unsigned n) n
  fromSigned : ∀ n → n ≤ maximum → UIntValue maximum (signed (+ n)) n

UIntRead : ℕ → Value → Set
UIntRead maximum raw = Σ[ n ∈ ℕ ] UIntValue maximum raw n

uint : ∀ maximum raw → Checked (UIntRead maximum raw)
uint maximum (unsigned n) with n ≤? maximum
... | yes bounded = accepted (n , fromUnsigned n bounded)
... | no overflow = rejected (fault [] invalidNumber "integer exceeds field range")
  (λ { (.n , fromUnsigned .n bounded) → overflow bounded })
uint maximum (signed (+ n)) with n ≤? maximum
... | yes bounded = accepted (n , fromSigned n bounded)
... | no overflow = rejected (fault [] invalidNumber "integer exceeds field range")
  (λ { (.n , fromSigned .n bounded) → overflow bounded })
uint maximum (signed (-[1+ n ])) = rejected (fault [] invalidNumber "unsigned field cannot be negative") (λ { (n , ()) })
uint maximum null = rejected (fault [] malformedInput "expected an unsigned integer") (λ { (n , ()) })
uint maximum (boolean b) = rejected (fault [] malformedInput "expected an unsigned integer") (λ { (n , ()) })
uint maximum (string s) = rejected (fault [] malformedInput "expected an unsigned integer") (λ { (n , ()) })
uint maximum (floating n) = rejected (fault [] malformedInput "expected an integer, not a floating value") (λ { (n , ()) })
uint maximum (array values) = rejected (fault [] malformedInput "expected an unsigned integer") (λ { (n , ()) })
uint maximum (object values) = rejected (fault [] malformedInput "expected an unsigned integer") (λ { (n , ()) })

integerInRange : ∀ {maximum raw n} → UIntValue maximum raw n → n ≤ maximum
integerInRange (fromUnsigned n bounded) = bounded
integerInRange (fromSigned n bounded) = bounded

asString : Value → Fault ⊎ Text
asString (string s) = inj₂ s
asString _ = inj₁ (fault [] malformedInput "expected a string")

asBoolean : Value → Fault ⊎ Bool
asBoolean (boolean b) = inj₂ b
asBoolean _ = inj₁ (fault [] malformedInput "expected a boolean")

asArray : Value → Fault ⊎ List Value
asArray (array xs) = inj₂ xs
asArray _ = inj₁ (fault [] malformedInput "expected an array")

asObject : Value → Fault ⊎ Object.Fields
asObject (object xs) = inj₂ xs
asObject _ = inj₁ (fault [] malformedInput "expected an object")

withField : ∀ {A : Set} → Text → Fault ⊎ A → Fault ⊎ A
withField name (inj₁ failure) = inj₁ (prependPath (fieldKey name) failure)
withField name (inj₂ value) = inj₂ value

required : ∀ {A : Set} → Text → (Value → Fault ⊎ A) → Object.View → Fault ⊎ A
required name decode view with view name
... | nothing = inj₁ (fault (fieldKey name ∷ []) malformedInput "required field is missing")
... | just value = withField name (decode value)

defaulted : ∀ {A : Set} → Text → A → (Value → Fault ⊎ A) → Object.View → Fault ⊎ A
defaulted name fallback decode view with view name
... | nothing = inj₂ fallback
... | just value = withField name (decode value)

nullable : ∀ {A : Set} → (Value → Fault ⊎ A) → Maybe Value → Fault ⊎ Maybe A
nullable decode nothing = inj₂ nothing
nullable decode (just null) = inj₂ nothing
nullable decode (just raw) with decode raw
... | inj₁ failure = inj₁ failure
... | inj₂ value = inj₂ (just value)

optional : ∀ {A : Set} → Text → (Value → Fault ⊎ A) → Object.View → Fault ⊎ Maybe A
optional name decode view = withField name (nullable decode (view name))

literalStringPreserved : ∀ s → asString (string s) ≡ inj₂ s
literalStringPreserved s = refl

missingUsesDefault : ∀ {A : Set} name (fallback : A) decode view → view name ≡ nothing →
  defaulted name fallback decode view ≡ inj₂ fallback
missingUsesDefault name fallback decode view absent rewrite absent = refl

presentNeverUsesDefault : ∀ {A : Set} name (fallback : A) decode view raw → view name ≡ just raw →
  defaulted name fallback decode view ≡ withField name (decode raw)
presentNeverUsesDefault name fallback decode view raw present rewrite present = refl

nullOptionalIsAbsent : ∀ {A : Set} (decode : Value → Fault ⊎ A) → nullable decode (just null) ≡ inj₂ nothing
nullOptionalIsAbsent decode = refl
