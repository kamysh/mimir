{-# OPTIONS --safe #-}
-- Shared wire admission. JSON integer and floating variants stay distinct.
-- UUIDs are represented internally by their 128-bit big-endian integer, not
-- by an invented ordinal. Standard integer-to-f64 casting is a dependency.
module Mimir.PublicInput where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (fromℕ<; toℕ)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; []; _∷_; map; foldl)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _+_; _*_; _<?_; _≤?_)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String; toList)
import Data.Vec as Vec
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.Empty using (⊥-elim)
import Data.List.Relation.Unary.Any as Any
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
open import Mimir.Validation using (Fault; fault; malformedInput; invalidNumber; result)
open import Mimir.RecordDecoding using (_>>=_; mapResult)
import Mimir.StructuredValue as V
import Mimir.UUIDSchema as UUID
import Mimir.UUIDGroups as UUIDValue
import Mimir.Binary64 as B
import Mimir.StandardLibrary as Conversion
import Mimir.FloatValue as Float

bad : ∀ {A : Set} → String → Fault ⊎ A
bad message = inj₁ (fault [] malformedInput message)

uuidNumber : UUIDValue.UUID → ℕ
uuidNumber id = foldl (λ n byte → 256 * n + toℕ byte) 0 (Vec.toList id)

readUUID : Conversion.Contract → V.Value → Fault ⊎ ℕ
readUUID conversion raw with UUID.decode conversion raw
... | inj₁ error = bad "invalid UUID"
... | inj₂ id = inj₂ (uuidNumber id)

unsigned : ℕ → V.Value → Fault ⊎ ℕ
unsigned maximum raw = mapResult proj₁ (result (V.uint maximum raw))

i64 : V.Value → Fault ⊎ ℤ
i64 (V.signed (+ n)) with n ≤? B.powerMinusOne 63
... | yes bounded = inj₂ (+ n)
... | no _ = bad "integer exceeds i64 range"
i64 (V.signed (-[1+ n ])) with n ≤? B.powerMinusOne 63
... | yes bounded = inj₂ (-[1+ n ])
... | no _ = bad "integer exceeds i64 range"
i64 (V.unsigned n) = mapResult +_ (unsigned (B.powerMinusOne 63) (V.unsigned n))
i64 _ = bad "expected i64 integer"

enum : ∀ {A : Set} → List (String × A) → V.Value → Fault ⊎ A
enum choices raw = V.asString raw >>= λ text → choose text choices
  where
  choose : ∀ {A : Set} → Text → List (String × A) → Fault ⊎ A
  choose text [] = bad "unknown enum value"
  choose text ((name , value) ∷ rest) with text ≟Text toList name
  ... | yes _ = inj₂ value
  ... | no _ = choose text rest

view : V.Value → V.Object.View
view (V.object fields) = V.Object.normalize fields
view _ = λ _ → nothing

required : ∀ {A : Set} → String → (V.Value → Fault ⊎ A) → V.Object.View → Fault ⊎ A
required name = V.required (toList name)

defaulted : ∀ {A : Set} → String → A → (V.Value → Fault ⊎ A) → V.Object.View → Fault ⊎ A
defaulted name = V.defaulted (toList name)

optional : ∀ {A : Set} → String → (V.Value → Fault ⊎ A) → V.Object.View → Fault ⊎ Maybe A
optional name = V.optional (toList name)

-- MCP removes only the explicit operation-token field before binding a
-- business request. All other submitted fields/values remain as supplied;
-- omission is not replaced by a decoded default or an explicit null.
withoutFields : Text → V.Object.Fields → V.Object.Fields
withoutFields removed [] = []
withoutFields removed ((name , value) ∷ rest) with name ≟Text removed
... | yes _ = withoutFields removed rest
... | no _ = (name , value) ∷ withoutFields removed rest

withoutField : Text → V.Value → V.Value
withoutField removed (V.object fields) = V.object (withoutFields removed fields)
withoutField removed value = value

-- Retrying with an omitted field and retrying with an explicit default are
-- different bindings. Removing the token retains every other exact value.
withoutFieldsKeepsOther : ∀ removed name value fields → name ≢ removed →
  Any.Any (λ entry → entry ≡ (name , value)) fields →
  Any.Any (λ entry → entry ≡ (name , value)) (withoutFields removed fields)
withoutFieldsKeepsOther removed name value [] different ()
withoutFieldsKeepsOther removed name value ((entry , supplied) ∷ rest) different known with entry ≟Text removed
... | yes same with known
... | Any.here refl = ⊥-elim (different same)
... | Any.there later = withoutFieldsKeepsOther removed name value rest different later
withoutFieldsKeepsOther removed name value ((entry , supplied) ∷ rest) different known | no _ with known
... | Any.here refl = Any.here refl
... | Any.there later = Any.there (withoutFieldsKeepsOther removed name value rest different later)

withoutFieldsCannotInvent : ∀ removed pair fields → Any.Any (λ entry → entry ≡ pair) (withoutFields removed fields) →
  Any.Any (λ entry → entry ≡ pair) fields
withoutFieldsCannotInvent removed pair [] ()
withoutFieldsCannotInvent removed pair ((entry , supplied) ∷ rest) known with entry ≟Text removed
... | yes _ = Any.there (withoutFieldsCannotInvent removed pair rest known)
... | no _ with known
... | Any.here same = Any.here same
... | Any.there later = Any.there (withoutFieldsCannotInvent removed pair rest later)

-- Hand-written MCP args.get(...).map(decode) rejects explicit null, unlike an
-- Option<T> field decoded by serde. Loose accessors use their fallback on any
-- wrong type, matching args[key].as_*().unwrap_or(...).
present : ∀ {A : Set} → String → (V.Value → Fault ⊎ A) → V.Object.View → Fault ⊎ Maybe A
present name decode fields with fields (toList name)
... | nothing = inj₂ nothing
... | just raw = mapResult just (V.withField (toList name) (decode raw))

loose : ∀ {A : Set} → String → A → (V.Value → Fault ⊎ A) → V.Object.View → A
loose name fallback decode fields with fields (toList name)
... | nothing = fallback
... | just raw with decode raw
...   | inj₁ error = fallback
...   | inj₂ value = value

looseOptional : ∀ {A : Set} → String → (V.Value → Fault ⊎ A) → V.Object.View → Maybe A
looseOptional name decode = loose name nothing (λ raw → mapResult just (decode raw))

module Numbers (conversion : Conversion.Contract) where
  uuid : V.Value → Fault ⊎ ℕ
  uuid = readUUID conversion

  castNatural : ℕ → Fault ⊎ B.Number
  castNatural n with n <? B.power 64
  ... | no _ = bad "JSON integer exceeds u64 range"
  ... | yes bounded with Conversion.Contract.cast conversion (fromℕ< bounded)
  ...   | Float.finite sign amount = inj₂ (B.finite (Float.finiteValue sign amount))
  ...   | _ = bad "nonfinite integer conversion"

  negative : B.Number → B.Number
  negative (B.finite amount) = B.finite (B.finiteNumber
    (record (B.FiniteNumber.word amount) { sign = B.negative }) (B.FiniteNumber.finite amount))
  negative (B.nonfinite word proof) = B.nonfinite (record word { sign = B.negative }) proof

  number : V.Value → Fault ⊎ B.Number
  number (V.floating value) = inj₂ value
  number (V.unsigned n) = castNatural n
  number (V.signed (+ n)) = castNatural n
  number (V.signed (-[1+ n ])) = mapResult negative (castNatural (suc n))
  number _ = bad "expected a number"
