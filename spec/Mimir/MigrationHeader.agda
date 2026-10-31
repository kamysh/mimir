{-# OPTIONS --safe #-}
-- Interpretation after header lexing. Duplicate fields are FIRST-wins;
-- unknown fields are ignored. Name and description must be single strings,
-- while requires may be absent, one string, or a list of strings.
module Mimir.MigrationHeader where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.String using (toList)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Data.Empty using (⊥-elim)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)

data Value : Set where single : Text → Value; multiple : List Text → Value

Fields = List (Text × Value)

lookup : Text → Fields → Maybe Value
lookup query [] = nothing
lookup query ((name , value) ∷ rest) with query ≟Text name
... | yes same = just value
... | no different = lookup query rest

requirements : Maybe Value → List Text
requirements nothing = []
requirements (just (single name)) = name ∷ []
requirements (just (multiple names)) = names

record Header : Set where
  constructor header
  field name description : Text; requires : List Text
open Header

interpret : Fields → Maybe Header
interpret fields with lookup (toList "name") fields
... | nothing = nothing
... | just (multiple _) = nothing
... | just (single name) with lookup (toList "description") fields
...   | nothing = nothing
...   | just (multiple _) = nothing
...   | just (single description) = just (header name description (requirements (lookup (toList "requires") fields)))

Valid : Fields → Header → Set
Valid fields decoded = lookup (toList "name") fields ≡ just (single (name decoded)) ×
  lookup (toList "description") fields ≡ just (single (description decoded)) ×
  requires decoded ≡ requirements (lookup (toList "requires") fields)

sound : ∀ fields decoded → interpret fields ≡ just decoded → Valid fields decoded
sound fields decoded accepted with lookup (toList "name") fields
... | nothing with accepted
...   | ()
sound fields decoded accepted | just (multiple _) with accepted
... | ()
sound fields decoded accepted | just (single name) with lookup (toList "description") fields
... | nothing with accepted
...   | ()
sound fields decoded accepted | just (single name) | just (multiple _) with accepted
... | ()
sound fields decoded accepted | just (single name) | just (single description) with accepted
... | refl = refl , refl , refl

complete : ∀ fields decoded → Valid fields decoded → interpret fields ≡ just decoded
complete fields (header name description requires) (nameFound , descriptionFound , dependencies)
  rewrite nameFound | descriptionFound | dependencies = refl

firstFieldWins : ∀ key value rest → lookup key ((key , value) ∷ rest) ≡ just value
firstFieldWins key value rest with key ≟Text key
... | yes same = refl
... | no different = ⊥-elim (different refl)

otherFieldSkipped : ∀ query key value rest → query ≢ key →
  lookup query ((key , value) ∷ rest) ≡ lookup query rest
otherFieldSkipped query key value rest different with query ≟Text key
... | yes same = ⊥-elim (different same)
... | no unequal = refl
