{-# OPTIONS --safe #-}
module Mimir.SourceSchema where

open import Data.Char using (Char; _≟_)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; length; map)
open import Data.List.Properties using (≡-dec)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤_; _≤?_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Mimir.Text
open import Mimir.Validation

data Provenance : Set where userFeedback agentReport toolResult : Provenance

record Source : Set where
  constructor source
  field
    reference actor text : Text
    provenance : Provenance
    recordedAt : Maybe Text
open Source

optionalTimestamp : Maybe Text → Set
optionalTimestamp nothing = ⊤
optionalTimestamp (just text) = Nonempty text × Bounded 100 text

checkTimestamp : (timestamp : Maybe Text) → Checked (optionalTimestamp timestamp)
checkTimestamp nothing = accepted tt
checkTimestamp (just text) = combine
  (check (fault [] emptyText "source timestamp must not be empty") (nonempty? text))
  (check (fault [] textTooLong "source timestamp exceeds 100 UTF-8 bytes") (bounded? 100 text))

NamedText : ℕ → Text → Set
NamedText limit text = Nonblank text × Bounded limit text

checkNamed : (limit : ℕ) (text : Text) → Checked (NamedText limit text)
checkNamed limit text = combine
  (check (fault [] emptyText "text must contain a non-whitespace character") (nonblank? text))
  (check (fault [] textTooLong "text exceeds the field's UTF-8 byte limit") (bounded? limit text))

SourceValid : Source → Set
SourceValid s = optionalTimestamp (recordedAt s) ×
  (NamedText 1000 (reference s) ×
  (NamedText 200 (actor s) × (Nonempty (text s) × Bounded 12000 (text s))))

validateSource : (s : Source) → Checked (SourceValid s)
validateSource s = combine
  (at (key "recorded_at") (checkTimestamp (recordedAt s)))
  (combine (at (key "source_ref") (checkNamed 1000 (reference s)))
  (combine (at (key "actor") (checkNamed 200 (actor s)))
  (combine (at (key "text") (check
    (fault [] emptyText "source text must not be empty") (nonempty? (text s))))
    (at (key "text") (check
      (fault [] textTooLong "source text exceeds 12000 UTF-8 bytes") (bounded? 12000 (text s)))))))

-- Distinctness is checked on the exact source reference, without trimming or
-- case folding. Whitespace validation does not change source identity.
NotPresent : Text → List Text → Set
NotPresent reference references = All (λ other → reference ≢ other) references

notPresent? : ∀ reference references → Dec (NotPresent reference references)
notPresent? reference [] = yes []
notPresent? reference (other ∷ rest) with ≡-dec _≟_ reference other
... | yes same = no (λ { (notSame ∷ _) → notSame same })
... | no different with notPresent? reference rest
...   | yes proof = yes (different ∷ proof)
...   | no impossible = no (λ { (_ ∷ proof) → impossible proof })

data Distinct : List Text → Set where
  empty : Distinct []
  more : ∀ {reference rest} → NotPresent reference rest → Distinct rest →
    Distinct (reference ∷ rest)

distinct? : ∀ references → Dec (Distinct references)
distinct? [] = yes empty
distinct? (reference ∷ rest) with notPresent? reference rest
... | no impossible = no (λ { (more p _) → impossible p })
... | yes p with distinct? rest
...   | yes q = yes (more p q)
...   | no impossible = no (λ { (more _ q) → impossible q })

SourcesValid : List Source → Set
SourcesValid sources = length sources ≤ 32 ×
  (All SourceValid sources × Distinct (map reference sources))

-- Index each error so it can be corrected without guessing which source failed.
indexedSources : (offset : ℕ) (sources : List Source) → Checked (All SourceValid sources)
indexedSources offset [] = accepted []
indexedSources offset (s ∷ ss) with at (index offset) (validateSource s)
... | rejected failure notValid = rejected failure (λ { (p ∷ ps) → notValid p })
... | accepted p with indexedSources (Data.Nat.suc offset) ss
...   | accepted ps = accepted (p ∷ ps)
...   | rejected failure notValid = rejected failure (λ { (p ∷ ps) → notValid ps })

validateSources : (sources : List Source) → Checked (SourcesValid sources)
validateSources sources = at (key "source_records") (combine
  (check (fault [] tooMany "at most 32 source records are permitted") (length sources ≤? 32))
  (combine (indexedSources 0 sources)
    (check (fault [] duplicate "source references must be distinct")
      (distinct? (map reference sources)))))

validSourcesNeverRejected : ∀ sources → SourcesValid sources →
  reported (validateSources sources) ≡ []
validSourcesNeverRejected sources proof = noFalseRejection (validateSources sources) proof

record AcceptedSources : Set where
  constructor acceptedSources
  field
    raw : List Source
    valid : SourcesValid raw

countBound : ∀ (sources : AcceptedSources) → length (AcceptedSources.raw sources) ≤ 32
countBound sources = proj₁ (AcceptedSources.valid sources)

identityUnique : ∀ (sources : AcceptedSources) →
  Distinct (map reference (AcceptedSources.raw sources))
identityUnique sources = proj₂ (proj₂ (AcceptedSources.valid sources))
