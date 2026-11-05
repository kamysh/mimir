{-# OPTIONS --safe #-}
-- Transport an exact lexical-prefix parser to bytes through the checked
-- byte/character bijection; preserve its token and unconsumed suffix.
module Mimir.BytePart where

open import Data.List using (List; _++_)
open import Data.List.Properties using (map-++)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.All.Properties using (++⁻ʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂; trans; sym; subst)
open import Mimir.Bits using (Byte)
open import Mimir.Text using (Text)
import Mimir.ByteText as Wire
import Mimir.ParsedPart as TextPart

module Lift (A : Set) (spell : A → Text) (bounded : ∀ value → All Wire.Bounded (spell value)) where
  spelling : A → List Byte
  spelling value = Wire.bytes (spell value) (bounded value)

  spellingText : ∀ value → Wire.text (spelling value) ≡ spell value
  spellingText value = Wire.textBytes (spell value) (bounded value)

  record Part (input : List Byte) : Set where
    constructor part
    field value : A; rest : List Byte; exact : input ≡ spelling value ++ rest

  remainingBounded : ∀ {input} (result : TextPart.Part A spell (Wire.text input)) →
    All Wire.Bounded (TextPart.Part.rest result)
  remainingBounded {input} (TextPart.part value rest exact) =
    ++⁻ʳ (spell value) (subst (All Wire.Bounded) exact (Wire.textBounded input))

  transport : ∀ {input} → TextPart.Part A spell (Wire.text input) → Part input
  transport {input} result@(TextPart.part value rest exact) = part value suffix
    (Wire.textInjective input (spelling value ++ suffix) (trans exact (sym encodedText)))
    where
    restBounded = remainingBounded result
    suffix = Wire.bytes rest restBounded
    encodedText = trans (map-++ Wire.character (spelling value) suffix)
      (cong₂ _++_ (spellingText value) (Wire.textBytes rest restBounded))

  parse : TextPart.Parser A spell → (input : List Byte) → Maybe (Part input)
  parse parser input with parser (Wire.text input)
  ... | nothing = nothing
  ... | just result = just (transport result)

  transportValue : ∀ {input} (result : TextPart.Part A spell (Wire.text input)) →
    Part.value (transport result) ≡ TextPart.Part.value result
  transportValue (TextPart.part value rest exact) = refl

  transportRest : ∀ {input} (result : TextPart.Part A spell (Wire.text input)) →
    Wire.text (Part.rest (transport result)) ≡ TextPart.Part.rest result
  transportRest result@(TextPart.part value rest exact) = Wire.textBytes rest (remainingBounded result)

  successPreserved : ∀ parser input rest → TextPart.Succeeded parser (Wire.text input) (Wire.text rest) →
    Σ (Part input) (λ result → parse parser input ≡ just result × Part.rest result ≡ rest)
  successPreserved parser input rest (result , observed , sameRest) rewrite observed =
    transport result , refl , Wire.textInjective (Part.rest (transport result)) rest (trans (transportRest result) sameRest)
