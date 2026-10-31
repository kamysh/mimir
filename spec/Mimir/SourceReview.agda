{-# OPTIONS --safe #-}
-- Referential and quotation integrity for a review. Learning-item/prediction
-- field validation and numeric assessment validation are separate conjuncts.
-- A coverage claim records what the reviewer asserted; it is not an axiom that
-- an LLM found every semantically interesting sentence.
module Mimir.SourceReview where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char; _≟_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; length; map)
open import Data.List.Properties using (≡-dec)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ) renaming (_≟_ to _≟ℕ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans)
open import Mimir.Text
open import Mimir.Validation
open import Mimir.SourceSchema using (Source; NamedText; checkNamed; Distinct; distinct?)
open import Mimir.SourceText
open Matching Char _≟_

_≟Text_ = ≡-dec _≟_

findSource : Text → List Source → Maybe Source
findSource ref [] = nothing
findSource ref (s ∷ ss) with ref ≟Text Source.reference s
... | yes _ = just s
... | no _ = findSource ref ss

Found : ∀ {A : Set} → Maybe A → Set
Found nothing = ⊥
Found (just _) = ⊤

found? : ∀ {A : Set} (value : Maybe A) → Dec (Found value)
found? nothing = no (λ proof → proof)
found? (just _) = yes tt

data Status : Set where complete unresolved : Status

record Coverage : Set where
  constructor sourceCoverage
  field reference : Text; status : Status; reason : Text

CoverageValid : List Source → Coverage → Set
CoverageValid sources c = Found (findSource (Coverage.reference c) sources) ×
  NamedText 4000 (Coverage.reason c)

validateCoverage : ∀ sources c → Checked (CoverageValid sources c)
validateCoverage sources c = combine
  (at (key "source_ref") (check
    (fault [] missingReference "coverage must refer to a recorded source")
    (found? (findSource (Coverage.reference c) sources))))
  (at (key "reason") (checkNamed 4000 (Coverage.reason c)))

-- These are the source-relevant projections of a learning item. The immutable
-- ID is an exact integer representation, never an ordinal in the item array.
record Item : Set where
  constructor item
  field identity : ℕ; reference actor statement : Text

QuoteValid : Maybe Source → Item → Set
QuoteValid nothing i = ⊥
QuoteValid (just s) i = Item.actor i ≡ Source.actor s ×
  Contains (Item.statement i) (Source.text s)

validateQuote : (s : Maybe Source) (i : Item) → Checked (QuoteValid s i)
validateQuote nothing i = rejected
  (fault (key "source_ref" ∷ []) missingReference "extracted item has no recorded source")
  (λ impossible → impossible)
validateQuote (just s) i = combine
  (at (key "actor") (check
    (fault [] wrongActor "item actor must equal the recorded source actor")
    (Item.actor i ≟Text Source.actor s)))
  (at (key "statement") (check
    (fault [] quotationMismatch "statement must be an exact contiguous quotation from source text")
    (contains? (Item.statement i) (Source.text s))))

-- The validator cannot reject a valid quote, including a legacy quotation
-- supplied as text. Validation never rewrites or decodes the source text.
validQuoteAccepted : ∀ s i → QuoteValid s i → reported (validateQuote s i) ≡ []
validQuoteAccepted s i proof = noFalseRejection (validateQuote s i) proof

unresolvedFor : Text → List Coverage → Bool
unresolvedFor ref [] = false
unresolvedFor ref (c ∷ cs) with ref ≟Text Coverage.reference c | Coverage.status c
... | yes _ | unresolved = true
... | _ | _ = unresolvedFor ref cs

idPresent : ℕ → List ℕ → Bool
idPresent id [] = false
idPresent id (candidate ∷ rest) with id ≟ℕ candidate
... | yes _ = true
... | no _ = idPresent id rest

boolTrue? : (value : Bool) → Dec (value ≡ true)
boolTrue? true = yes refl
boolTrue? false = no (λ ())

Accounted : List Coverage → List ℕ → Item → Set
Accounted coverage assessed i = (unresolvedFor (Item.reference i) coverage ≡ true) ⊎
  (idPresent (Item.identity i) assessed ≡ true)

accounted? : ∀ coverage assessed i → Dec (Accounted coverage assessed i)
accounted? coverage assessed i with boolTrue? (unresolvedFor (Item.reference i) coverage)
... | yes proof = yes (inj₁ proof)
... | no notUnresolved with boolTrue? (idPresent (Item.identity i) assessed)
...   | yes proof = yes (inj₂ proof)
...   | no notAssessed = no (λ { (inj₁ proof) → notUnresolved proof ; (inj₂ proof) → notAssessed proof })

ItemIntegrity : List Source → List Coverage → List ℕ → Item → Set
ItemIntegrity sources coverage assessed i =
  QuoteValid (findSource (Item.reference i) sources) i × Accounted coverage assessed i

validateItemIntegrity : ∀ sources coverage assessed i →
  Checked (ItemIntegrity sources coverage assessed i)
validateItemIntegrity sources coverage assessed i = combine
  (validateQuote (findSource (Item.reference i) sources) i)
  (check (fault [] missingEvidence "item needs an assessment or explicit unresolved source coverage")
    (accounted? coverage assessed i))

data Fresh : List ℕ → List Item → Set where
  done : ∀ {existing} → Fresh existing []
  next : ∀ {existing i rest} → idPresent (Item.identity i) existing ≡ false →
    Fresh (Item.identity i ∷ existing) rest → Fresh existing (i ∷ rest)

fresh? : ∀ existing items → Dec (Fresh existing items)
fresh? existing [] = yes done
fresh? existing (i ∷ rest) with idPresent (Item.identity i) existing in seen
... | true = no (λ { (next absent _) → trueNotFalse (trans (sym seen) absent) })
  where
  trueNotFalse : true ≢ false
  trueNotFalse ()
... | false with fresh? (Item.identity i ∷ existing) rest
...   | yes proof = yes (next seen proof)
...   | no notFresh = no (λ { (next _ proof) → notFresh proof })

record Review : Set where
  constructor review
  field
    coverage : List Coverage
    extracted : List Item
    assessedIDs : List ℕ
    legacyContributions : Bool

CoverageIntegrity : List Source → List Coverage → Set
CoverageIntegrity sources coverage = length coverage ≡ length sources ×
  (All (CoverageValid sources) coverage × Distinct (map Coverage.reference coverage))

validateCoverageIntegrity : ∀ sources coverage → Checked (CoverageIntegrity sources coverage)
validateCoverageIntegrity sources coverage = combine
  (check (fault [] missingReference "every source needs exactly one coverage record")
    (length coverage ≟ℕ length sources))
  (combine (allChecked (validateCoverage sources) coverage)
    (check (fault [] duplicate "coverage references must be distinct")
      (distinct? (map Coverage.reference coverage))))

ReviewIntegrity : List Source → List ℕ → Review → Set
ReviewIntegrity [] existing r = Review.coverage r ≡ [] × Review.extracted r ≡ []
ReviewIntegrity sources@(_ ∷ _) existing r = Review.legacyContributions r ≡ false ×
  (CoverageIntegrity sources (Review.coverage r) ×
  (Fresh existing (Review.extracted r) ×
    All (ItemIntegrity sources (Review.coverage r) (Review.assessedIDs r)) (Review.extracted r)))

empty? : ∀ {A : Set} (xs : List A) → Dec (xs ≡ [])
empty? [] = yes refl
empty? (_ ∷ _) = no (λ ())

false? : ∀ b → Dec (b ≡ false)
false? false = yes refl
false? true = no (λ ())

validateReviewIntegrity : ∀ sources existing r → Checked (ReviewIntegrity sources existing r)
validateReviewIntegrity [] existing r = combine
  (at (key "source_coverage") (check
    (fault [] unsupportedCombination "coverage requires source records") (empty? (Review.coverage r))))
  (at (key "extracted_items") (check
    (fault [] unsupportedCombination "extraction requires source records") (empty? (Review.extracted r))))
validateReviewIntegrity sources@(_ ∷ _) existing r = combine
  (check (fault [] unsupportedCombination "source reviews use typed assessments, not legacy contributions")
    (false? (Review.legacyContributions r)))
  (combine (at (key "source_coverage") (validateCoverageIntegrity sources (Review.coverage r)))
  (combine (at (key "extracted_items") (check
    (fault [] duplicate "extracted item ID conflicts with an existing or extracted item")
    (fresh? existing (Review.extracted r))))
    (at (key "extracted_items") (allChecked
      (validateItemIntegrity sources (Review.coverage r) (Review.assessedIDs r)) (Review.extracted r)))))

validReviewNeverRejected : ∀ sources existing r → ReviewIntegrity sources existing r →
  reported (validateReviewIntegrity sources existing r) ≡ []
validReviewNeverRejected sources existing r proof =
  noFalseRejection (validateReviewIntegrity sources existing r) proof
