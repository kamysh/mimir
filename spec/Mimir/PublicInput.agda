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
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
open import Mimir.Validation using (Fault; fault; malformedInput; invalidNumber; result)
open import Mimir.RecordDecoding using (_>>=_; mapResult)
import Mimir.StructuredValue as V
import Mimir.UUIDSchema as UUID
import Mimir.UUIDGroups as UUIDValue
import Mimir.Binary64 as B
import Mimir.FloatConversion as Conversion
import Mimir.FloatValue as Float

bad : ∀ {A : Set} → String → Fault ⊎ A
bad message = inj₁ (fault [] malformedInput message)

uuidNumber : UUIDValue.UUID → ℕ
uuidNumber id = foldl (λ n byte → 256 * n + toℕ byte) 0 (Vec.toList id)

uuid : V.Value → Fault ⊎ ℕ
uuid raw with UUID.decode raw
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
