{-# OPTIONS --safe #-}

-- Exact source selection. Character/byte decoding is a separate obligation;
-- this module is valid for every element type, including UTF-8 bytes.
module Mimir.SourceText where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; subst; sym)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (Dec; yes; no)

module Selection (A : Set) where
  record Split (n : ℕ) (text : List A) : Set where
    constructor parts
    field
      prefix suffix : List A
      reconstruct : text ≡ prefix ++ suffix
      prefixLength : length prefix ≡ n

  split : (n : ℕ) (text : List A) → Maybe (Split n text)
  split zero text = just (parts [] text refl refl)
  split (suc n) [] = nothing
  split (suc n) (x ∷ xs) with split n xs
  ... | nothing = nothing
  ... | just (parts before after same size) =
    just (parts (x ∷ before) after (cong (x ∷_) same) (cong suc size))

  record Location (offset count : ℕ) (text : List A) : Set where
    constructor located
    field
      start : Split offset text
      extent : Split (suc count) (Split.suffix start)

  quotation : ∀ {offset count text} → Location offset count text → List A
  quotation location = Split.prefix (Location.extent location)

  select : (offset count : ℕ) (text : List A) → Maybe (Location offset count text)
  select offset count text with split offset text
  ... | nothing = nothing
  ... | just start with split (suc count) (Split.suffix start)
  ...   | nothing = nothing
  ...   | just extent = just (located start extent)

  exactLength : ∀ {offset count text} (location : Location offset count text) →
    length (quotation location) ≡ suc count
  exactLength location = Split.prefixLength (Location.extent location)

  -- The selected quotation is an exact contiguous part of the original source.
  sourceContainsQuotation : ∀ {offset count text}
    (location : Location offset count text) →
    text ≡ Split.prefix (Location.start location) ++
      (quotation location ++ Split.suffix (Location.extent location))
  sourceContainsQuotation location =
    trans (Split.reconstruct (Location.start location))
      (cong (Split.prefix (Location.start location) ++_)
        (Split.reconstruct (Location.extent location)))

  -- Fits is an inductive bound, independent of the selection algorithm.
  data Fits : ℕ → List A → Set where
    fitsZero : ∀ {xs} → Fits zero xs
    fitsNext : ∀ {n x xs} → Fits n xs → Fits (suc n) (x ∷ xs)

  splitComplete : ∀ {n text} → Fits n text →
    Σ (Split n text) (λ result → split n text ≡ just result)
  splitComplete fitsZero = parts [] _ refl refl , refl
  splitComplete (fitsNext bound) with splitComplete bound
  ... | result , equation rewrite equation =
    parts (_ ∷ Split.prefix result) (Split.suffix result)
      (cong (_ ∷_) (Split.reconstruct result))
      (cong suc (Split.prefixLength result)) , refl

  selectionComplete : ∀ {offset count text} (start : Split offset text) →
    split offset text ≡ just start → Fits (suc count) (Split.suffix start) →
    Σ (Location offset count text) (λ result → select offset count text ≡ just result)
  selectionComplete start same bound with splitComplete bound
  ... | extent , equation rewrite same | equation = located start extent , refl

module Matching (A : Set) (_≟_ : DecidableEquality A) where
  data Prefix : List A → List A → Set where
    empty : ∀ {text} → Prefix [] text
    next : ∀ {x needle text} → Prefix needle text → Prefix (x ∷ needle) (x ∷ text)

  data Contains (needle : List A) : List A → Set where
    here : ∀ {text} → Prefix needle text → Contains needle text
    later : ∀ {x text} → Contains needle text → Contains needle (x ∷ text)

  prefix? : (needle text : List A) → Dec (Prefix needle text)
  prefix? [] text = yes empty
  prefix? (x ∷ xs) [] = no (λ ())
  prefix? (x ∷ xs) (y ∷ ys) with x ≟ y
  ... | no unequal = no (λ { (next tail) → unequal refl })
  ... | yes refl with prefix? xs ys
  ...   | yes tail = yes (next tail)
  ...   | no absent = no (λ { (next tail) → absent tail })

  contains? : (needle text : List A) → Dec (Contains needle text)
  contains? needle [] with prefix? needle []
  ... | yes prefix = yes (here prefix)
  ... | no absent = no (λ { (here prefix) → absent prefix })
  contains? needle (x ∷ xs) with prefix? needle (x ∷ xs)
  ... | yes prefix = yes (here prefix)
  ... | no absent with contains? needle xs
  ...   | yes occurrence = yes (later occurrence)
  ...   | no missing = no (λ { (here prefix) → absent prefix ; (later occurrence) → missing occurrence })

  appendedPrefix : ∀ needle suffix → Prefix needle (needle ++ suffix)
  appendedPrefix [] suffix = empty
  appendedPrefix (x ∷ xs) suffix = next (appendedPrefix xs suffix)

  shift : ∀ prefix {needle text} → Contains needle text → Contains needle (prefix ++ text)
  shift [] occurrence = occurrence
  shift (x ∷ xs) occurrence = later (shift xs occurrence)

  selectedQuoteContained : ∀ {offset count text}
    (location : Selection.Location A offset count text) →
    Contains (Selection.quotation A location) text
  selectedQuoteContained location =
    subst (Contains (Selection.quotation A location))
      (sym (Selection.sourceContainsQuotation A location))
      (shift (Selection.Split.prefix (Selection.Location.start location))
        (here (appendedPrefix (Selection.quotation A location)
          (Selection.Split.suffix (Selection.Location.extent location)))))

-- A scalar-aligned quotation remains contiguous under any per-scalar byte
-- encoding, in particular UTF-8. This does not assume an inverse decoder or
-- confuse a JSON-escaped representation with the underlying source string.
module Encoding (A B : Set) (eqA : DecidableEquality A) (eqB : DecidableEquality B)
  (encodeOne : A → List B) where
  module From = Matching A eqA
  module To = Matching B eqB

  encode : List A → List B
  encode [] = []
  encode (x ∷ xs) = encodeOne x ++ encode xs

  encodeAppend : ∀ xs ys → encode (xs ++ ys) ≡ encode xs ++ encode ys
  encodeAppend [] ys = refl
  encodeAppend (x ∷ xs) ys = trans
    (cong (encodeOne x ++_) (encodeAppend xs ys))
    (sym (++-assoc (encodeOne x) (encode xs) (encode ys)))

  prependEqual : ∀ prefix {needle text} → To.Prefix needle text →
    To.Prefix (prefix ++ needle) (prefix ++ text)
  prependEqual [] proof = proof
  prependEqual (x ∷ xs) proof = To.next (prependEqual xs proof)

  prefixEncoded : ∀ {needle text} → From.Prefix needle text →
    To.Prefix (encode needle) (encode text)
  prefixEncoded From.empty = To.empty
  prefixEncoded (From.next {x} proof) = prependEqual (encodeOne x) (prefixEncoded proof)

  containmentEncoded : ∀ {needle text} → From.Contains needle text →
    To.Contains (encode needle) (encode text)
  containmentEncoded (From.here proof) = To.here (prefixEncoded proof)
  containmentEncoded (From.later {x} proof) = To.shift (encodeOne x) (containmentEncoded proof)

  selectedEncodingContained : ∀ {offset count text}
    (location : Selection.Location A offset count text) →
    To.Contains (encode (Selection.quotation A location)) (encode text)
  selectedEncodingContained location = containmentEncoded (From.selectedQuoteContained location)
