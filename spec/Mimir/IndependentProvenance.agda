{-# OPTIONS --safe #-}
module Mimir.IndependentProvenance where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (toList)
open import Relation.Nullary using (does)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.LearningCandidates as Candidates
import Mimir.Validation as Validation

data Basis : Set where userInstruction document : Basis

record Provenance : Set where
  constructor provenance
  field basis : Basis; reference : Text

validate : (p : Provenance) → Validation.Checked (Candidates.Trimmed 2048 (Provenance.reference p))
validate p = Candidates.checkTrimmed 2048 (Provenance.reference p)

record Stored : Set where
  constructor stored
  field basis reference : Maybe Text

absent : Maybe Text → Bool
absent nothing = true
absent (just value) = does (value ≟Text toList "null")

data Read : Set where
  noProvenance malformed : Read
  found : Provenance → Read

decode : Stored → Read
decode s with Stored.basis s | Stored.reference s
... | just basis | just reference with does (basis ≟Text toList "user_instruction")
...   | true = found (provenance userInstruction reference)
...   | false with does (basis ≟Text toList "document")
...     | true = found (provenance document reference)
...     | false with absent (just basis) ∧ absent (just reference)
...       | true = noProvenance
...       | false = malformed
decode s | nothing | nothing = noProvenance
decode s | nothing | just reference with absent (just reference)
... | true = noProvenance
... | false = malformed
decode s | just basis | nothing with absent (just basis)
... | true = noProvenance
... | false = malformed
