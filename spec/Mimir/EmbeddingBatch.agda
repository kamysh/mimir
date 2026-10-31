{-# OPTIONS --safe #-}
-- Align provider records to input positions. A complete result consumes every
-- response row exactly once, covers every input index, and has uniform shape.
-- Scalar finiteness and binary64-to-binary32 rounding are separate contracts.
module Mimir.EmbeddingBatch where

open import Data.List using (List; []; _∷_; length; map)
import Data.List.Relation.Binary.Permutation.Propositional as P
open import Data.Empty using (⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (Vec; []; _∷_; toList)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym)

module Batch (Scalar : Set) (dimension : ℕ) where
  record Row : Set where
    constructor row
    field index : ℕ; values : List Scalar

  data Extract (key : ℕ) : List Row → Row → List Row → Set where
    first : ∀ r rest → key ≡ Row.index r → Extract key (r ∷ rest) r rest
    later : ∀ r rest chosen remaining → key ≢ Row.index r →
      Extract key rest chosen remaining → Extract key (r ∷ rest) chosen (r ∷ remaining)

  record Found (key : ℕ) (rows : List Row) : Set where
    constructor found
    field selected : Row; remaining : List Row; selection : Extract key rows selected remaining
  open Found

  extract : (key : ℕ) (rows : List Row) → Maybe (Found key rows)
  extract key [] = nothing
  extract key (r ∷ rest) with key ≟ Row.index r
  ... | yes same = just (found r rest (first r rest same))
  ... | no different with extract key rest
  ...   | nothing = nothing
  ...   | just (found chosen remaining proof) =
      just (found chosen (r ∷ remaining) (later r rest chosen remaining different proof))

  extractionMatches : ∀ {key rows chosen remaining} → Extract key rows chosen remaining →
    key ≡ Row.index chosen
  extractionMatches (first r rest same) = same
  extractionMatches (later r rest chosen remaining different proof) = extractionMatches proof

  extractionConsumesOne : ∀ {key rows chosen remaining} → Extract key rows chosen remaining →
    length rows ≡ suc (length remaining)
  extractionConsumesOne (first r rest same) = refl
  extractionConsumesOne (later r rest chosen remaining different proof) = cong suc (extractionConsumesOne proof)

  extractionPermutesKeys : ∀ {key rows chosen remaining} → Extract key rows chosen remaining →
    map Row.index rows P.↭ (Row.index chosen ∷ map Row.index remaining)
  extractionPermutesKeys (first r rest same) = P.refl
  extractionPermutesKeys (later r rest chosen remaining different proof) =
    P.trans (P.prep (Row.index r) (extractionPermutesKeys proof))
      (P.swap (Row.index r) (Row.index chosen) P.refl)

  extractComplete : ∀ {key rows chosen remaining} → Extract key rows chosen remaining →
    Σ (Found key rows) (λ result → extract key rows ≡ just result ×
      (selected result ≡ chosen × Found.remaining result ≡ remaining))
  extractComplete {key} (first r rest same) with key ≟ Row.index r
  ... | yes equal = found r rest (first r rest equal) , (refl , (refl , refl))
  ... | no different = ⊥-elim (different same)
  extractComplete {key} (later r rest chosen remaining different proof) with key ≟ Row.index r
  ... | yes same = ⊥-elim (different same)
  ... | no notSame with extractComplete proof
  ...   | found picked leftover selection , (eq , (samePicked , sameRest))
    rewrite eq | samePicked | sameRest =
    found chosen (r ∷ remaining) (later r rest chosen remaining notSame selection) ,
      (refl , (refl , refl))

  record Shaped (count : ℕ) (values : List Scalar) : Set where
    constructor shaped
    field vector : Vec Scalar count; preserved : toList vector ≡ values
  open Shaped

  shape : (count : ℕ) (values : List Scalar) → Maybe (Shaped count values)
  shape zero [] = just (shaped [] refl)
  shape zero (_ ∷ _) = nothing
  shape (suc count) [] = nothing
  shape (suc count) (x ∷ xs) with shape count xs
  ... | nothing = nothing
  ... | just (shaped v same) = just (shaped (x ∷ v) (cong (x ∷_) same))

  shapeVector : ∀ {count} (v : Vec Scalar count) →
    Σ (Shaped count (toList v)) (λ result → shape count (toList v) ≡ just result × vector result ≡ v)
  shapeVector [] = shaped [] refl , (refl , refl)
  shapeVector (x ∷ xs) with shapeVector xs
  ... | shaped v preserved , (eq , same) rewrite eq | same =
    shaped (x ∷ xs) (cong (x ∷_) preserved) , (refl , refl)

  shapeComplete : ∀ {count values} (v : Vec Scalar count) → toList v ≡ values →
    Σ (Shaped count values) (λ result → shape count values ≡ just result × vector result ≡ v)
  shapeComplete v refl = shapeVector v

  -- Indexed by both the input rows and output vectors. The base case requires
  -- zero leftover rows, rejecting duplicates and unexpected provider indices.
  data Aligned : (offset count : ℕ) → List Row → Vec (Vec Scalar dimension) count → Set where
    done : ∀ {offset} → Aligned offset zero [] []
    more : ∀ {offset count rows chosen remaining vectors v} →
      Extract offset rows chosen remaining → toList v ≡ Row.values chosen →
      Aligned (suc offset) count remaining vectors →
      Aligned offset (suc count) rows (v ∷ vectors)

  data Error : Set where missingIndex extraRows wrongDimension : Error

  align : (offset count : ℕ) (rows : List Row) →
    Error ⊎ Σ (Vec (Vec Scalar dimension) count) (Aligned offset count rows)
  align offset zero [] = inj₂ ([] , done)
  align offset zero (_ ∷ _) = inj₁ extraRows
  align offset (suc count) rows with extract offset rows
  ... | nothing = inj₁ missingIndex
  ... | just (found chosen remaining selection) with shape dimension (Row.values chosen)
  ...   | nothing = inj₁ wrongDimension
  ...   | just (shaped v preserved) with align (suc offset) count remaining
  ...     | inj₁ error = inj₁ error
  ...     | inj₂ (vectors , proof) = inj₂ (v ∷ vectors , more selection preserved proof)

  noSilentTruncation : ∀ {offset count rows vectors} → Aligned offset count rows vectors →
    length rows ≡ count
  noSilentTruncation done = refl
  noSilentTruncation (more selection shape tail) =
    trans (extractionConsumesOne selection) (cong suc (noSilentTruncation tail))

  positions : ℕ → ℕ → List ℕ
  positions offset zero = []
  positions offset (suc count) = offset ∷ positions (suc offset) count

  everyInputPositionExactlyOnce : ∀ {offset count rows vectors} → Aligned offset count rows vectors →
    map Row.index rows P.↭ positions offset count
  everyInputPositionExactlyOnce done = P.refl
  everyInputPositionExactlyOnce (more {offset} {count} {chosen = chosen} selection shape tail) =
    P.trans (extractionPermutesKeys selection)
      (P.trans (P.prep (Row.index chosen) (everyInputPositionExactlyOnce tail))
        (P.↭-reflexive (cong (λ key → key ∷ positions (suc offset) count)
          (sym (extractionMatches selection)))))

  -- Every output's source index is the corresponding input position. This
  -- theorem does not assume that the provider returned its rows in order.
  firstOutputHasCorrectIndex : ∀ {offset count rows v vectors} →
    Aligned offset (suc count) rows (v ∷ vectors) →
    Σ Row (λ source → (offset ≡ Row.index source) × (toList v ≡ Row.values source))
  firstOutputHasCorrectIndex (more {chosen = source} selection preserved tail) =
    source , (extractionMatches selection , preserved)

  alignmentComplete : ∀ {offset count rows vectors} → Aligned offset count rows vectors →
    Σ (Aligned offset count rows vectors) (λ proof → align offset count rows ≡ inj₂ (vectors , proof))
  alignmentComplete done = done , refl
  alignmentComplete (more {v = v} selection preserved tail) with extractComplete selection
  ... | found picked leftover selected , (eq , (samePicked , sameRest))
    rewrite eq | samePicked | sameRest with shapeComplete v preserved
  ... | shaped output sameValues , (shapeEq , sameVector)
    rewrite shapeEq | sameVector with alignmentComplete tail
  ... | proof , tailEq rewrite tailEq = more selected sameValues proof , refl
