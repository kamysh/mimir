{-# OPTIONS --safe #-}
-- Typed positional struct visitors. Defaults apply only to exhausted input;
-- present values are always decoded, and surplus elements are rejected.
module Mimir.SerdeSequence where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Sum.Properties
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
import Mimir.StructuredValue as JSON
import Mimir.Text as Text
import Mimir.Validation as Validation

record Field : Set₁ where
  constructor fieldType
  field
    name : Text.Text
    Carrier : Set
    decode : JSON.Value → Validation.Fault ⊎ Carrier
    missing : Maybe Carrier

data Values : List Field → Set₁ where
  empty : Values []
  more : ∀ {entry rest} → Field.Carrier entry → Values rest → Values (entry ∷ rest)

data Error : Set where
  malformed : ℕ → Validation.Fault → Error
  missing : ℕ → Text.Text → Error
  extra : ℕ → List JSON.Value → Error

data Admitted : (fields : List Field) → List JSON.Value → Values fields → Set₁ where
  done : Admitted [] [] empty
  supplied : ∀ {entry rest raw input value values} → Field.decode entry raw ≡ inj₂ value →
    Admitted rest input values → Admitted (entry ∷ rest) (raw ∷ input) (more value values)
  defaulted : ∀ {entry rest value values} → Field.missing entry ≡ just value →
    Admitted rest [] values → Admitted (entry ∷ rest) [] (more value values)

prepend : ∀ {entry rest} → Field.Carrier entry → Error ⊎ Values rest → Error ⊎ Values (entry ∷ rest)
prepend value (inj₁ error) = inj₁ error
prepend value (inj₂ values) = inj₂ (more value values)

read : ∀ fields → ℕ → List JSON.Value → Error ⊎ Values fields
read [] offset [] = inj₂ empty
read [] offset (raw ∷ input) = inj₁ (extra offset (raw ∷ input))
read (entry ∷ rest) offset [] with Field.missing entry
... | nothing = inj₁ (missing offset (Field.name entry))
... | just value = prepend {entry = entry} value (read rest (suc offset) [])
read (entry ∷ rest) offset (raw ∷ input) with Field.decode entry raw
... | inj₁ failure = inj₁ (malformed offset failure)
... | inj₂ value = prepend {entry = entry} value (read rest (suc offset) input)

prependSuccess : ∀ {entry rest} (value : Field.Carrier entry) (result : Error ⊎ Values rest) output →
  prepend {entry = entry} value result ≡ inj₂ output → Σ (Values rest) (λ values → result ≡ inj₂ values × output ≡ more value values)
prependSuccess value (inj₁ error) output ()
prependSuccess value (inj₂ values) .(more value values) refl = values , refl , refl

complete : ∀ {fields input values} → Admitted fields input values → ∀ offset → read fields offset input ≡ inj₂ values
complete done offset = refl
complete (supplied observed rest) offset rewrite observed | complete rest (suc offset) = refl
complete (defaulted observed rest) offset rewrite observed | complete rest (suc offset) = refl

sound : ∀ fields offset input values → read fields offset input ≡ inj₂ values → Admitted fields input values
sound [] offset [] .empty refl = done
sound [] offset (raw ∷ input) values ()
sound (entry ∷ rest) offset [] values observed with Field.missing entry in fallback
... | nothing with observed
...   | ()
sound (entry ∷ rest) offset [] values observed | just value
  with prependSuccess {entry = entry} value (read rest (suc offset) []) values observed
... | remaining , successful , refl = defaulted fallback (sound rest (suc offset) [] remaining successful)
sound (entry ∷ rest) offset (raw ∷ input) values observed with Field.decode entry raw in decoded
... | inj₁ failure with observed
...   | ()
sound (entry ∷ rest) offset (raw ∷ input) values observed | inj₂ value
  with prependSuccess {entry = entry} value (read rest (suc offset) input) values observed
... | remaining , successful , refl = supplied decoded (sound rest (suc offset) input remaining successful)

-- A field with an available fallback still cannot hide a malformed supplied
-- value. The statement holds for arbitrary later fields and input.
presentFailure : ∀ entry rest offset raw input failure → Field.decode entry raw ≡ inj₁ failure →
  read (entry ∷ rest) offset (raw ∷ input) ≡ inj₁ (malformed offset failure)
presentFailure entry rest offset raw input failure observed rewrite observed = refl

decodedUnique : ∀ {fields input first second} → Admitted fields input first → Admitted fields input second → first ≡ second
decodedUnique first second = Data.Sum.Properties.inj₂-injective
  (Relation.Binary.PropositionalEquality.trans (Relation.Binary.PropositionalEquality.sym (complete first 0)) (complete second 0))
