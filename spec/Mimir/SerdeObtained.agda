{-# OPTIONS --safe #-}
-- Every field of a successfully decoded struct came either from its decoder
-- or its declared default. Field invariants therefore compose through both
-- object and positional-array representations.
module Mimir.SerdeObtained where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Mimir.StructuredValue as JSON
import Mimir.SerdeSequence as Sequence
import Mimir.SerdeStruct as Struct

open Sequence using (Field; Values; empty; more)

data FieldValue (entry : Field) (value : Field.Carrier entry) : Set where
  supplied : ∀ raw → Field.decode entry raw ≡ inj₂ value → FieldValue entry value
  defaulted : Field.missing entry ≡ just value → FieldValue entry value

data Obtained : ∀ fields → Values fields → Set₁ where
  done : Obtained [] empty
  next : ∀ {entry rest value values} → FieldValue entry value → Obtained rest values → Obtained (entry ∷ rest) (more value values)

fromMap : ∀ {fields view values} → Struct.MapAdmitted view fields values → Obtained fields values
fromMap Struct.done = done
fromMap (Struct.supplied {raw = raw} present decoded rest) = next (supplied raw decoded) (fromMap rest)
fromMap (Struct.defaulted absent fallback rest) = next (defaulted fallback) (fromMap rest)

fromSequence : ∀ {fields input values} → Sequence.Admitted fields input values → Obtained fields values
fromSequence Sequence.done = done
fromSequence (Sequence.supplied {raw = raw} decoded rest) = next (supplied raw decoded) (fromSequence rest)
fromSequence (Sequence.defaulted fallback rest) = next (defaulted fallback) (fromSequence rest)

fromStruct : ∀ {fields input values} → Struct.Admitted fields input values → Obtained fields values
fromStruct (Struct.object unique admitted) = fromMap admitted
fromStruct (Struct.array admitted) = fromSequence admitted

record Sound (entry : Field) (predicate : Field.Carrier entry → Set) : Set where
  constructor sound
  field
    decoded : ∀ raw value → Field.decode entry raw ≡ inj₂ value → predicate value
    fallback : ∀ value → Field.missing entry ≡ just value → predicate value

fieldSound : ∀ {entry predicate value} → Sound entry predicate → FieldValue entry value → predicate value
fieldSound law (supplied raw observed) = Sound.decoded law raw _ observed
fieldSound law (defaulted observed) = Sound.fallback law _ observed

data Rules : List Field → Set₁ where
  done : Rules []
  next : ∀ {entry rest predicate} → Sound entry predicate → Rules rest → Rules (entry ∷ rest)

Satisfied : ∀ {fields} → Rules fields → Values fields → Set
Satisfied done empty = ⊤
Satisfied (next {predicate = predicate} law rest) (more value values) = predicate value × Satisfied rest values

satisfied : ∀ {fields values} (rules : Rules fields) → Obtained fields values → Satisfied rules values
satisfied done done = tt
satisfied (next law rest) (next evidence later) = fieldSound law evidence , satisfied rest later

accepted : ∀ fields (rules : Rules fields) input values → Struct.read fields input ≡ inj₂ values → Satisfied rules values
accepted fields rules input values observed = satisfied rules (fromStruct (Struct.admittedSound fields input values observed))

trivial : ∀ entry → Sound entry (λ value → ⊤)
trivial entry = sound (λ raw value observed → tt) (λ value observed → tt)
