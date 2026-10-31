{-# OPTIONS --safe #-}
-- Heterogeneous typed-struct storage with explicit presence. A supplied null
-- optional value remains present, so it cannot hide a duplicate known field.
module Mimir.SerdeSlots where

open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.SerdeSequence as Sequence
import Mimir.SerdeFlow as Flow
import Mimir.Validation as V
open Sequence using (Field)

Values : List Field → Set
Values [] = ⊤
Values (entry ∷ rest) = Field.Carrier entry × Values rest

Slots : List Field → Set
Slots [] = ⊤
Slots (entry ∷ rest) = Maybe (Field.Carrier entry) × Slots rest

Readers : List Field → Set
Readers [] = ⊤
Readers (entry ∷ rest) = Flow.Parser (Field.Carrier entry) × Readers rest

fieldAt : (fields : List Field) → Fin (length fields) → Field
fieldAt [] ()
fieldAt (entry ∷ rest) zero = entry
fieldAt (entry ∷ rest) (suc index) = fieldAt rest index

readerAt : ∀ fields (index : Fin (length fields)) → Readers fields → Flow.Parser (Field.Carrier (fieldAt fields index))
readerAt [] () readers
readerAt (entry ∷ rest) zero (reader , readers) = reader
readerAt (entry ∷ rest) (suc index) (reader , readers) = readerAt rest index readers

find : Text → ∀ fields → Maybe (Fin (length fields))
find name [] = nothing
find name (entry ∷ rest) with name ≟Text Field.name entry
... | yes found = just zero
... | no different with find name rest
...   | nothing = nothing
...   | just index = just (suc index)

empty : ∀ fields → Slots fields
empty [] = tt
empty (entry ∷ rest) = nothing , empty rest

get : ∀ fields (index : Fin (length fields)) → Slots fields → Maybe (Field.Carrier (fieldAt fields index))
get [] () slots
get (entry ∷ rest) zero (value , slots) = value
get (entry ∷ rest) (suc index) (value , slots) = get rest index slots

put : ∀ fields (index : Fin (length fields)) → Field.Carrier (fieldAt fields index) → Slots fields → Slots fields
put [] () value slots
put (entry ∷ rest) zero value (previous , slots) = just value , slots
put (entry ∷ rest) (suc index) value (previous , slots) = previous , put rest index value slots

duplicate : Field → V.Fault
duplicate entry = V.fault (V.fieldKey (Field.name entry) ∷ []) V.duplicate "duplicate field"

assign : ∀ fields (index : Fin (length fields)) → Field.Carrier (fieldAt fields index) → Slots fields → V.Fault ⊎ Slots fields
assign fields index value slots with get fields index slots
... | just previous = inj₁ (duplicate (fieldAt fields index))
... | nothing = inj₂ (put fields index value slots)

emptyAbsent : ∀ fields index → get fields index (empty fields) ≡ nothing
emptyAbsent [] ()
emptyAbsent (entry ∷ fields) zero = refl
emptyAbsent (entry ∷ fields) (suc index) = emptyAbsent fields index

getOwnPut : ∀ fields index value slots → get fields index (put fields index value slots) ≡ just value
getOwnPut [] () value slots
getOwnPut (entry ∷ fields) zero value (previous , slots) = refl
getOwnPut (entry ∷ fields) (suc index) value (previous , slots) = getOwnPut fields index value slots

getOtherPut : ∀ fields first second value slots → first ≢ second →
  get fields second (put fields first value slots) ≡ get fields second slots
getOtherPut [] () second value slots different
getOtherPut (entry ∷ fields) zero zero value slots different = ⊥-elim (different refl)
getOtherPut (entry ∷ fields) zero (suc second) value (previous , slots) different = refl
getOtherPut (entry ∷ fields) (suc first) zero value (previous , slots) different = refl
getOtherPut (entry ∷ fields) (suc first) (suc second) value (previous , slots) different = getOtherPut fields first second value slots (λ same → different (cong suc same))

duplicateRejected : ∀ fields index value slots previous → get fields index slots ≡ just previous →
  assign fields index value slots ≡ inj₁ (duplicate (fieldAt fields index))
duplicateRejected fields index value slots previous present rewrite present = refl

firstAssignment : ∀ fields index value slots → get fields index slots ≡ nothing →
  assign fields index value slots ≡ inj₂ (put fields index value slots)
firstAssignment fields index value slots absent rewrite absent = refl

toSequence : ∀ fields → Values fields → Sequence.Values fields
toSequence [] values = Sequence.empty
toSequence (entry ∷ rest) (value , values) = Sequence.more value (toSequence rest values)

fromSequence : ∀ {fields} → Sequence.Values fields → Values fields
fromSequence Sequence.empty = tt
fromSequence (Sequence.more value values) = value , fromSequence values

sequenceRoundTrip : ∀ fields values → fromSequence (toSequence fields values) ≡ values
sequenceRoundTrip [] tt = refl
sequenceRoundTrip (entry ∷ fields) (value , values) = cong (value ,_) (sequenceRoundTrip fields values)

missing : Field → V.Fault
missing entry = V.fault (V.fieldKey (Field.name entry) ∷ []) V.malformedInput "required field is missing"

prepend : ∀ {entry rest} → Field.Carrier entry → V.Fault ⊎ Values rest → V.Fault ⊎ Values (entry ∷ rest)
prepend value (inj₁ error) = inj₁ error
prepend value (inj₂ values) = inj₂ (value , values)

resolve : ∀ fields → Slots fields → V.Fault ⊎ Values fields
resolve [] slots = inj₂ tt
resolve (entry ∷ rest) (just value , slots) = prepend {entry = entry} value (resolve rest slots)
resolve (entry ∷ rest) (nothing , slots) with Field.missing entry
... | nothing = inj₁ (missing entry)
... | just value = prepend {entry = entry} value (resolve rest slots)

data Resolved : ∀ fields → Slots fields → Values fields → Set₁ where
  resolvedEmpty : Resolved [] tt tt
  supplied : ∀ {entry rest value slots values} → Resolved rest slots values →
    Resolved (entry ∷ rest) (just value , slots) (value , values)
  defaulted : ∀ {entry rest value slots values} → Field.missing entry ≡ just value →
    Resolved rest slots values → Resolved (entry ∷ rest) (nothing , slots) (value , values)

resolveComplete : ∀ {fields slots values} → Resolved fields slots values → resolve fields slots ≡ inj₂ values
resolveComplete resolvedEmpty = refl
resolveComplete (supplied resolved) rewrite resolveComplete resolved = refl
resolveComplete (defaulted fallback resolved) rewrite fallback | resolveComplete resolved = refl

prependSuccess : ∀ {entry rest} (value : Field.Carrier entry) (result : V.Fault ⊎ Values rest) output →
  prepend {entry = entry} value result ≡ inj₂ output →
  Σ (Values rest) (λ values → result ≡ inj₂ values × output ≡ (value , values))
prependSuccess value (inj₁ error) output ()
prependSuccess value (inj₂ values) .(value , values) refl = values , refl , refl

resolveSound : ∀ fields slots values → resolve fields slots ≡ inj₂ values → Resolved fields slots values
resolveSound [] tt tt observed = resolvedEmpty
resolveSound (entry ∷ fields) (just value , slots) values observed
  with prependSuccess {entry = entry} value (resolve fields slots) values observed
... | tail , completed , refl = supplied (resolveSound fields slots tail completed)
resolveSound (entry ∷ fields) (nothing , slots) values observed with Field.missing entry in fallback
... | nothing with observed
...   | ()
resolveSound (entry ∷ fields) (nothing , slots) values observed | just value
  with prependSuccess {entry = entry} value (resolve fields slots) values observed
... | tail , completed , refl = defaulted fallback (resolveSound fields slots tail completed)

assignedValue : ∀ fields index value slots output → assign fields index value slots ≡ inj₂ output →
  get fields index output ≡ just value
assignedValue fields index value slots output observed with get fields index slots
... | just previous with observed
...   | ()
assignedValue fields index value slots output observed | nothing with observed
... | refl = getOwnPut fields index value slots

findSound : ∀ name fields index → find name fields ≡ just index → name ≡ Field.name (fieldAt fields index)
findSound name [] () observed
findSound name (entry ∷ fields) index observed with name ≟Text Field.name entry
... | yes found with observed
...   | refl = found
findSound name (entry ∷ fields) index observed | no different with find name fields in found
... | nothing with observed
...   | ()
findSound name (entry ∷ fields) index observed | no different | just selected with observed
... | refl = findSound name fields selected found

findAbsent : ∀ name fields → find name fields ≡ nothing →
  ∀ index → name ≢ Field.name (fieldAt fields index)
findAbsent name [] absent () same
findAbsent name (entry ∷ fields) absent zero same with name ≟Text Field.name entry
... | yes found with absent
...   | ()
findAbsent name (entry ∷ fields) absent zero same | no different = different same
findAbsent name (entry ∷ fields) absent (suc index) same with name ≟Text Field.name entry
... | yes found with absent
...   | ()
findAbsent name (entry ∷ fields) absent (suc index) same | no different with find name fields in found
... | just selected with absent
...   | ()
findAbsent name (entry ∷ fields) absent (suc index) same | no different | nothing = findAbsent name fields found index same
