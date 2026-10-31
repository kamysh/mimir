{-# OPTIONS --safe #-}
-- General record round trips with optional omission. Every emitted field
-- carries its codec round trip; every omitted field carries its actual
-- default equality. Unique schema names prevent overwrite or ambiguity.
module Mimir.SerdeEmission where

open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.StructuredValue as JSON
import Mimir.JsonObjects as Objects
import Mimir.SerdeSequence as Sequence
import Mimir.SerdeStruct as Struct

open Sequence using (Field; Values; empty; more)
module O = JSON.Object
module N = Objects.Names

data Emits : (fields : List Field) → Values fields → O.Fields → Set₁ where
  done : Emits [] empty []
  emitted : ∀ {entry rest value values raw input} → Field.decode entry raw ≡ inj₂ value →
    Emits rest values input → Emits (entry ∷ rest) (more value values) ((Field.name entry , raw) ∷ input)
  omitted : ∀ {entry rest value values input} → Field.missing entry ≡ just value →
    Emits rest values input → Emits (entry ∷ rest) (more value values) input

absentEmitted : ∀ {fields values input} name → N.Absent name (Struct.names fields) → Emits fields values input → N.Absent name (map proj₁ input)
absentEmitted name All.[] done = All.[]
absentEmitted name (different All.∷ others) (emitted decoded rest) = different All.∷ absentEmitted name others rest
absentEmitted name (different All.∷ others) (omitted fallback rest) = absentEmitted name others rest

uniqueEmitted : ∀ {fields values input} → N.Unique (Struct.names fields) → Emits fields values input → N.Unique (map proj₁ input)
uniqueEmitted unique done = tt
uniqueEmitted (absent , unique) (emitted {entry} decoded rest) = absentEmitted (Field.name entry) absent rest , uniqueEmitted unique rest
uniqueEmitted (absent , unique) (omitted fallback rest) = uniqueEmitted unique rest

knownAbsent : ∀ name allowed input → N.Absent name (map proj₁ input) → N.Absent name (O.knownKeys allowed input)
knownAbsent name allowed [] All.[] = All.[]
knownAbsent name allowed ((key , value) ∷ input) (different All.∷ others) with N.present? key allowed
... | yes present = different All.∷ knownAbsent name allowed input others
... | no absent = knownAbsent name allowed input others

knownUnique : ∀ allowed input → N.Unique (map proj₁ input) → N.Unique (O.knownKeys allowed input)
knownUnique allowed [] unique = tt
knownUnique allowed ((key , value) ∷ input) (absent , unique) with N.present? key allowed
... | yes present = knownAbsent key allowed input absent , knownUnique allowed input unique
... | no missing = knownUnique allowed input unique

loadAbsent : ∀ name input before → N.Absent name (map proj₁ input) → O.load input before name ≡ before name
loadAbsent name [] before All.[] = refl
loadAbsent name ((key , value) ∷ input) before (different All.∷ rest) =
  trans (loadAbsent name input (O.write key value before) rest) (O.otherField key name value before different)

writeCongruent : ∀ key value first second name → first name ≡ second name → O.write key value first name ≡ O.write key value second name
writeCongruent key value first second name same with name ≟Text key
... | yes equal = refl
... | no different = same

loadCongruent : ∀ input first second name → first name ≡ second name → O.load input first name ≡ O.load input second name
loadCongruent [] first second name same = same
loadCongruent ((key , value) ∷ input) first second name same = loadCongruent input
  (O.write key value first) (O.write key value second) name (writeCongruent key value first second name same)

headOther : ∀ key raw input name → name ≢ key → O.normalize ((key , raw) ∷ input) name ≡ O.normalize input name
headOther key raw input name different = loadCongruent input (O.write key raw O.empty) O.empty name
  (O.otherField key name raw O.empty different)

headOwn : ∀ key raw input → N.Absent key (map proj₁ input) → O.normalize ((key , raw) ∷ input) key ≡ just raw
headOwn key raw input absent = trans (loadAbsent key input (O.write key raw O.empty) absent) (O.ownField key raw O.empty)

transfer : ∀ {fields values first second} → All (λ entry → first (Field.name entry) ≡ second (Field.name entry)) fields →
  Struct.MapAdmitted first fields values → Struct.MapAdmitted second fields values
transfer All.[] Struct.done = Struct.done
transfer (same All.∷ others) (Struct.supplied present decoded rest) = Struct.supplied (trans (sym same) present) decoded (transfer others rest)
transfer (same All.∷ others) (Struct.defaulted absent fallback rest) = Struct.defaulted (trans (sym same) absent) fallback (transfer others rest)

tailViews : ∀ key raw input fields → N.Absent key (Struct.names fields) →
  All (λ entry → O.normalize input (Field.name entry) ≡ O.normalize ((key , raw) ∷ input) (Field.name entry)) fields
tailViews key raw input [] All.[] = All.[]
tailViews key raw input (entry ∷ fields) (different All.∷ rest) =
  sym (headOther key raw input (Field.name entry) (λ same → different (sym same))) All.∷ tailViews key raw input fields rest

mapAdmitted : ∀ {fields values input} → N.Unique (Struct.names fields) → Emits fields values input →
  Struct.MapAdmitted (O.normalize input) fields values
mapAdmitted unique done = Struct.done
mapAdmitted (absent , unique) (emitted {entry} {rest} {raw = raw} {input} decoded later) =
  Struct.supplied (headOwn (Field.name entry) raw input (absentEmitted (Field.name entry) absent later)) decoded
    (transfer (tailViews (Field.name entry) raw input rest absent) (mapAdmitted unique later))
mapAdmitted (absent , unique) (omitted {entry} {input = input} fallback later) =
  Struct.defaulted (loadAbsent (Field.name entry) input O.empty (absentEmitted (Field.name entry) absent later))
    fallback (mapAdmitted unique later)

admitted : ∀ {fields values input} → N.Unique (Struct.names fields) → Emits fields values input → Struct.Admitted fields (JSON.object input) values
admitted {fields} {input = input} unique emittedFields = Struct.object
  (knownUnique (Struct.names fields) input (uniqueEmitted unique emittedFields)) (mapAdmitted unique emittedFields)

roundTrip : ∀ {fields values input} → N.Unique (Struct.names fields) → Emits fields values input → Struct.read fields (JSON.object input) ≡ inj₂ values
roundTrip unique emittedFields = Struct.admittedComplete (admitted unique emittedFields)
