{-# OPTIONS --safe #-}
-- Object normalization and schema-name policy. These are distinct layers:
-- serde_json::Value keeps the last duplicate; typed structs can reject a
-- repeated known field. Ignored unknown fields are not duplicate struct fields.
module Mimir.JsonObjects where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.String using (fromList)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
open import Mimir.Collections using (module Equality)
open import Mimir.Validation

module Names = Equality Text _≟Text_

data UnknownPolicy : Set where ignore forbid : UnknownPolicy
data DuplicatePolicy : Set where keepLast rejectKnownRepeated : DuplicatePolicy

module Object (Value : Set) where
  Fields = List (Text × Value)
  View = Text → Maybe Value

  empty : View
  empty name = nothing

  write : Text → Value → View → View
  write name value before queried with queried ≟Text name
  ... | yes _ = just value
  ... | no _ = before queried

  load : Fields → View → View
  load [] before = before
  load ((name , value) ∷ rest) before = load rest (write name value before)

  normalize : Fields → View
  normalize fields = load fields empty

  ownField : ∀ name value before → write name value before name ≡ just value
  ownField name value before with name ≟Text name
  ... | yes _ = refl
  ... | no impossible = ⊥-elim (impossible refl)

  otherField : ∀ name other value before → other ≢ name →
    write name value before other ≡ before other
  otherField name other value before different with other ≟Text name
  ... | yes same = ⊥-elim (different same)
  ... | no _ = refl

  loadAppend : ∀ first second before → load (first ++ second) before ≡ load second (load first before)
  loadAppend [] second before = refl
  loadAppend ((name , value) ∷ rest) second before = loadAppend rest second (write name value before)

  lastOccurrenceWins : ∀ prefix name value →
    normalize (prefix ++ ((name , value) ∷ [])) name ≡ just value
  lastOccurrenceWins prefix name value = trans
    (cong (λ view → view name) (loadAppend prefix ((name , value) ∷ []) empty))
    (ownField name value (normalize prefix))

  replacementForgetsOld : ∀ name newer older before queried →
    write name newer (write name older before) queried ≡ write name newer before queried
  replacementForgetsOld name newer older before queried with queried ≟Text name
  ... | yes _ = refl
  ... | no different = otherField name queried older before different

  knownKeys : List Text → Fields → List Text
  knownKeys allowed [] = []
  knownKeys allowed ((name , value) ∷ rest) with Names.present? name allowed
  ... | yes _ = name ∷ knownKeys allowed rest
  ... | no _ = knownKeys allowed rest

  UnknownsAllowed : UnknownPolicy → List Text → Fields → Set
  UnknownsAllowed ignore allowed fields = ⊤
  UnknownsAllowed forbid allowed fields = All (λ entry → Names.Present (proj₁ entry) allowed) fields

  checkKnown : (allowed : List Text) (fields : Fields) →
    Checked (All (λ entry → Names.Present (proj₁ entry) allowed) fields)
  checkKnown allowed [] = accepted []
  checkKnown allowed ((name , value) ∷ rest) with Names.present? name allowed
  ... | no unknown = rejected
    (fault (fieldKey name ∷ []) unknownField "unknown field")
    (λ { (known ∷ others) → unknown known })
  ... | yes known with checkKnown allowed rest
  ...   | accepted others = accepted (known ∷ others)
  ...   | rejected failure invalid = rejected failure (λ { (known ∷ others) → invalid others })

  checkUnknowns : ∀ policy allowed fields → Checked (UnknownsAllowed policy allowed fields)
  checkUnknowns ignore allowed fields = accepted tt
  checkUnknowns forbid allowed fields = checkKnown allowed fields

  DuplicatesAllowed : DuplicatePolicy → List Text → Fields → Set
  DuplicatesAllowed keepLast allowed fields = ⊤
  DuplicatesAllowed rejectKnownRepeated allowed fields = Names.Unique (knownKeys allowed fields)

  checkDuplicates : ∀ policy allowed fields → Checked (DuplicatesAllowed policy allowed fields)
  checkDuplicates keepLast allowed fields = accepted tt
  checkDuplicates rejectKnownRepeated allowed fields = Names.checkUnique (knownKeys allowed fields)

  unknownNeverCreatesKnownField : ∀ allowed name value rest →
    Names.Absent name allowed → knownKeys allowed ((name , value) ∷ rest) ≡ knownKeys allowed rest
  unknownNeverCreatesKnownField allowed name value rest absent with Names.present? name allowed
  ... | yes present = ⊥-elim (Names.presentAbsentContradiction present absent)
  ... | no _ = refl
