{-# OPTIONS --safe #-}
-- Acceptance semantics for derived structs: ordered positional arrays or
-- maps with ignored unknown keys and rejected repeated known keys. State-file
-- reads erase deserializer diagnostics, so this does not claim native error
-- ordering or wording. Parsing ignored raw JSON remains a separate boundary.
module Mimir.SerdeStruct where

open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
import Data.Sum.Properties
import Mimir.StructuredValue as JSON
import Mimir.JsonObjects as Objects
import Mimir.SerdeSequence as Sequence
import Mimir.Validation as V
import Mimir.Text

open Sequence using (Field; Values; empty; more)
module O = JSON.Object

data MapAdmitted (view : O.View) : (fields : List Field) → Values fields → Set₁ where
  done : MapAdmitted view [] empty
  supplied : ∀ {entry rest raw value values} → view (Field.name entry) ≡ just raw →
    Field.decode entry raw ≡ inj₂ value → MapAdmitted view rest values → MapAdmitted view (entry ∷ rest) (more value values)
  defaulted : ∀ {entry rest value values} → view (Field.name entry) ≡ nothing →
    Field.missing entry ≡ just value → MapAdmitted view rest values → MapAdmitted view (entry ∷ rest) (more value values)

prepend : ∀ {entry rest} → Field.Carrier entry → V.Fault ⊎ Values rest → V.Fault ⊎ Values (entry ∷ rest)
prepend value (inj₁ failure) = inj₁ failure
prepend value (inj₂ values) = inj₂ (more value values)

readFields : ∀ fields → O.View → V.Fault ⊎ Values fields
readFields [] view = inj₂ empty
readFields (entry ∷ rest) view with view (Field.name entry)
... | nothing with Field.missing entry
...   | nothing = inj₁ (V.fault (V.fieldKey (Field.name entry) ∷ []) V.malformedInput "required field is missing")
...   | just value = prepend {entry = entry} value (readFields rest view)
readFields (entry ∷ rest) view | just raw with Field.decode entry raw
... | inj₁ failure = inj₁ (V.prependPath (V.fieldKey (Field.name entry)) failure)
... | inj₂ value = prepend {entry = entry} value (readFields rest view)

complete : ∀ {fields view values} → MapAdmitted view fields values → readFields fields view ≡ inj₂ values
complete done = refl
complete (supplied present decoded rest) rewrite present | decoded | complete rest = refl
complete (defaulted absent fallback rest) rewrite absent | fallback | complete rest = refl

prependSuccess : ∀ {entry rest} (value : Field.Carrier entry) (result : V.Fault ⊎ Values rest) output →
  prepend {entry = entry} value result ≡ inj₂ output → Σ (Values rest) (λ values → result ≡ inj₂ values × output ≡ more value values)
prependSuccess value (inj₁ failure) output ()
prependSuccess value (inj₂ values) .(more value values) refl = values , refl , refl

sound : ∀ fields view values → readFields fields view ≡ inj₂ values → MapAdmitted view fields values
sound [] view .empty refl = done
sound (entry ∷ rest) view values observed with view (Field.name entry) in present
... | nothing with Field.missing entry in fallback
...   | nothing with observed
...     | ()
sound (entry ∷ rest) view values observed | nothing | just value
  with prependSuccess {entry = entry} value (readFields rest view) values observed
... | remaining , successful , refl = defaulted present fallback (sound rest view remaining successful)
sound (entry ∷ rest) view values observed | just raw with Field.decode entry raw in decoded
... | inj₁ failure with observed
...   | ()
sound (entry ∷ rest) view values observed | just raw | inj₂ value
  with prependSuccess {entry = entry} value (readFields rest view) values observed
... | remaining , successful , refl = supplied present decoded (sound rest view remaining successful)

names : List Field → List Mimir.Text.Text
names = map Field.name

data Error : Set where
  wrongType : JSON.Value → Error
  mapFailure : V.Fault → Error
  sequenceFailure : Sequence.Error → Error

mapResult : ∀ {fields} → V.Fault ⊎ Values fields → Error ⊎ Values fields
mapResult (inj₁ failure) = inj₁ (mapFailure failure)
mapResult (inj₂ values) = inj₂ values

sequenceResult : ∀ {fields} → Sequence.Error ⊎ Values fields → Error ⊎ Values fields
sequenceResult (inj₁ failure) = inj₁ (sequenceFailure failure)
sequenceResult (inj₂ values) = inj₂ values

readObject : ∀ fields → O.Fields → Error ⊎ Values fields
readObject fields input with O.checkDuplicates Objects.rejectKnownRepeated (names fields) input
... | V.rejected failure invalid = inj₁ (mapFailure failure)
... | V.accepted unique = mapResult (readFields fields (O.normalize input))

read : ∀ fields → JSON.Value → Error ⊎ Values fields
read fields (JSON.object input) = readObject fields input
read fields (JSON.array input) = sequenceResult (Sequence.read fields 0 input)
read fields other = inj₁ (wrongType other)

data Admitted (fields : List Field) : JSON.Value → Values fields → Set₁ where
  object : ∀ {input values} → O.DuplicatesAllowed Objects.rejectKnownRepeated (names fields) input →
    MapAdmitted (O.normalize input) fields values → Admitted fields (JSON.object input) values
  array : ∀ {input values} → Sequence.Admitted fields input values → Admitted fields (JSON.array input) values

objectComplete : ∀ fields input values → O.DuplicatesAllowed Objects.rejectKnownRepeated (names fields) input →
  MapAdmitted (O.normalize input) fields values → readObject fields input ≡ inj₂ values
objectComplete fields input values unique admitted with O.checkDuplicates Objects.rejectKnownRepeated (names fields) input
... | V.rejected failure impossible = ⊥-elim (impossible unique)
... | V.accepted actual rewrite complete admitted = refl

admittedComplete : ∀ {fields input values} → Admitted fields input values → read fields input ≡ inj₂ values
admittedComplete {fields} (object {input} {values} unique admitted) = objectComplete fields input values unique admitted
admittedComplete (array admitted) rewrite Sequence.complete admitted 0 = refl

mapResultSuccess : ∀ {fields} (result : V.Fault ⊎ Values fields) values → mapResult result ≡ inj₂ values → result ≡ inj₂ values
mapResultSuccess (inj₁ failure) values ()
mapResultSuccess (inj₂ .values) values refl = refl

sequenceResultSuccess : ∀ {fields} (result : Sequence.Error ⊎ Values fields) values → sequenceResult result ≡ inj₂ values → result ≡ inj₂ values
sequenceResultSuccess (inj₁ failure) values ()
sequenceResultSuccess (inj₂ .values) values refl = refl

objectSound : ∀ fields input values → readObject fields input ≡ inj₂ values → Admitted fields (JSON.object input) values
objectSound fields input values observed with O.checkDuplicates Objects.rejectKnownRepeated (names fields) input
... | V.rejected failure invalid with observed
...   | ()
objectSound fields input values observed | V.accepted unique = object unique (sound fields (O.normalize input) values
  (mapResultSuccess (readFields fields (O.normalize input)) values observed))

admittedSound : ∀ fields input values → read fields input ≡ inj₂ values → Admitted fields input values
admittedSound fields (JSON.object input) values observed = objectSound fields input values observed
admittedSound fields (JSON.array input) values observed = array (Sequence.sound fields 0 input values
  (sequenceResultSuccess (Sequence.read fields 0 input) values observed))
admittedSound fields JSON.null values ()
admittedSound fields (JSON.boolean value) values ()
admittedSound fields (JSON.string value) values ()
admittedSound fields (JSON.signed value) values ()
admittedSound fields (JSON.unsigned value) values ()
admittedSound fields (JSON.floating value) values ()
