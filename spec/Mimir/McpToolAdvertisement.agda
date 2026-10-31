{-# OPTIONS --safe #-}
-- First-match tool lookup and exact advertised-property checks. Definitions
-- are retained verbatim; an invalid first duplicate is not silently replaced
-- by a later advertisement with the same name.
module Mimir.McpToolAdvertisement where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (nothing; just)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (toList)
open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
open import Mimir.Validation
open import Mimir.RecordDecoding using (_>>=_)
import Mimir.StructuredValue as V

get : Text → V.Value → V.Value
get name (V.object fields) with V.Object.normalize fields name
... | nothing = V.null
... | just value = value
get name _ = V.null

atPath : List Text → V.Value → V.Value
atPath [] value = value
atPath (key ∷ rest) value = atPath rest (get key value)

stringEqual : ∀ expected actual → Dec (V.string expected ≡ actual)
stringEqual expected (V.string actual) with expected ≟Text actual
... | yes refl = yes refl
... | no different = no (λ { refl → different refl })
stringEqual expected V.null = no (λ ())
stringEqual expected (V.boolean value) = no (λ ())
stringEqual expected (V.unsigned value) = no (λ ())
stringEqual expected (V.signed value) = no (λ ())
stringEqual expected (V.floating value) = no (λ ())
stringEqual expected (V.array value) = no (λ ())
stringEqual expected (V.object value) = no (λ ())

Named : Text → V.Value → Set
Named name raw = V.string name ≡ get (toList "name") raw

data First (name : Text) : List V.Value → V.Value → Set where
  here : ∀ {raw rest} → Named name raw → First name (raw ∷ rest) raw
  there : ∀ {raw rest selected} → ¬ Named name raw → First name rest selected → First name (raw ∷ rest) selected

data Search (name : Text) (tools : List V.Value) : Set where
  found : (raw : V.Value) → First name tools raw → Search name tools
  missing : All (λ raw → ¬ Named name raw) tools → Search name tools

find : ∀ name tools → Search name tools
find name [] = missing []
find name (raw ∷ rest) with stringEqual name (get (toList "name") raw)
... | yes named = found raw (here named)
... | no different with find name rest
...   | found selected first = found selected (there different first)
...   | missing absent = missing (different ∷ absent)

foundHasName : ∀ {name tools raw} → First name tools raw → Named name raw
foundHasName (here named) = named
foundHasName (there different first) = foundHasName first

missingCannotContain : ∀ {name tools raw} → All (λ entry → ¬ Named name entry) tools → First name tools raw → ⊥
missingCannotContain (different ∷ absent) (here named) = different named
missingCannotContain (different ∷ absent) (there skipped first) = missingCannotContain absent first

firstUnique : ∀ {name tools first second} → First name tools first → First name tools second → first ≡ second
firstUnique (here first) (here second) = refl
firstUnique (here first) (there skipped second) = Data.Empty.⊥-elim (skipped first)
firstUnique (there skipped first) (here second) = Data.Empty.⊥-elim (skipped second)
firstUnique (there skipped first) (there other second) = firstUnique first second

record Property : Set where
  constructor propertySpec
  field location : List Text; kind : Text

Matches : Property → V.Value → Set
Matches requirement raw = V.string (Property.kind requirement) ≡ atPath (Property.location requirement) raw

checkProperty : ∀ requirement raw → Checked (Matches requirement raw)
checkProperty requirement raw = check (problem (Data.List.map fieldKey (Property.location requirement))
  unsupportedCombination (toList "unsupported MCP schema"))
  (stringEqual (Property.kind requirement) (atPath (Property.location requirement) raw))

record Requirement : Set where
  constructor requirementSpec
  field name : Text; properties : List Property

record Selected (requirement : Requirement) (tools : List V.Value) : Set where
  constructor selectedTool
  field
    raw : V.Value
    first : First (Requirement.name requirement) tools raw
    checked : All (λ property → Matches property raw) (Requirement.properties requirement)

validateFound : ∀ requirement tools raw → First (Requirement.name requirement) tools raw → Fault ⊎ Selected requirement tools
validateFound requirement tools raw first =
  result (allChecked (λ property → checkProperty property raw) (Requirement.properties requirement)) >>= λ checked →
    inj₂ (selectedTool raw first checked)

required : ∀ requirement tools → Fault ⊎ Selected requirement tools
required requirement tools with find (Requirement.name requirement) tools
... | missing absent = inj₁ (fault [] missingReference "required MCP tool unavailable")
... | found raw first = validateFound requirement tools raw first

selectedHasExactName : ∀ {requirement tools} (selection : Selected requirement tools) →
  V.string (Requirement.name requirement) ≡ get (toList "name") (Selected.raw selection)
selectedHasExactName selection = foundHasName (Selected.first selection)
