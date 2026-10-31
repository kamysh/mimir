{-# OPTIONS --safe #-}
-- Serialized bytes cannot vary with the choice of Unicode/admission proof.
module Mimir.JsonCompactIdentity where

open import Data.List using ([]; _∷_)
import Data.List.Relation.Unary.All as All
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
import Mimir.StructuredValue as JSON
import Mimir.UnicodeText as Unicode
import Mimir.JsonCompactRecords as C

mutual
  supportedUnique : ∀ value (first second : C.Supported value) → first ≡ second
  supportedUnique JSON.null C.null C.null = refl
  supportedUnique (JSON.boolean value) (C.boolean .value) (C.boolean .value) = refl
  supportedUnique (JSON.signed value) (C.signed .value) (C.signed .value) = refl
  supportedUnique (JSON.unsigned value) (C.unsigned .value) (C.unsigned .value) = refl
  supportedUnique (JSON.string value) (C.string first) (C.string second) = cong C.string (Unicode.validIrrelevant first second)
  supportedUnique (JSON.array values) (C.array first) (C.array second) = cong C.array (arrayUnique values first second)
  supportedUnique (JSON.object fields) (C.object first) (C.object second) = cong C.object (fieldsUnique fields first second)

  arrayUnique : ∀ values (first second : All.All C.Supported values) → first ≡ second
  arrayUnique [] All.[] All.[] = refl
  arrayUnique (value ∷ values) (first All.∷ rest) (second All.∷ remaining) =
    cong₂ All._∷_ (supportedUnique value first second) (arrayUnique values rest remaining)

  fieldsUnique : ∀ fields (first second : All.All C.FieldSupported fields) → first ≡ second
  fieldsUnique [] All.[] All.[] = refl
  fieldsUnique ((name , value) ∷ fields) ((name₁ , first) All.∷ rest) ((name₂ , second) All.∷ remaining) =
    cong₂ All._∷_ (cong₂ _,_ (Unicode.validIrrelevant name₁ name₂) (supportedUnique value first second))
      (fieldsUnique fields rest remaining)

bytesIndependent : ∀ value first second → C.bytes value first ≡ C.bytes value second
bytesIndependent value first second = cong (C.bytes value) (supportedUnique value first second)

countIndependent : ∀ value first second → C.count value first ≡ C.count value second
countIndependent value first second = cong (C.count value) (supportedUnique value first second)
