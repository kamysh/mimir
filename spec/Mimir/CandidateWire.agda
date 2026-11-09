{-# OPTIONS --safe #-}
-- The review candidate interface uses tagged snake_case variants and the
-- MemoryType enum's capitalized spellings. It is not the MCP query's memory
-- filter grammar. Missing memory_type defaults; explicit null does not.
module Mimir.CandidateWire where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (toList)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
open import Mimir.LearningCandidates
open import Mimir.Validation hiding (result)
open import Mimir.StructuredValue
open import Mimir.RecordDecoding
open import Mimir.JsonObjects using (DuplicatePolicy; rejectKnownRepeated; keepLast; forbid)
import Mimir.DocumentStore as Documents
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Unit using (⊤)

readCitation : (Value → Fault ⊎ ℕ) → DuplicatePolicy → Value → Fault ⊎ Documents.Citation
readCitation readID duplicates = readRecord forbid duplicates
  (map toList ("chunk_id" ∷ "document_path" ∷ "quotation" ∷ "explanation" ∷ [])) λ view →
    required (toList "chunk_id") readID view >>= λ id →
    required (toList "document_path") asString view >>= λ document →
    required (toList "quotation") asString view >>= λ quotation →
    required (toList "explanation") asString view >>= λ explanation →
    inj₂ (Documents.citation id document quotation explanation)

encodeCitation : (ℕ → Text) → Documents.Citation → Value
encodeCitation writeID cited = object
  ((toList "chunk_id" , string (writeID (Documents.Citation.chunk cited))) ∷
   (toList "document_path" , string (Documents.Citation.document cited)) ∷
   (toList "quotation" , string (Documents.Citation.quotation cited)) ∷
   (toList "explanation" , string (Documents.Citation.explanation cited)) ∷ [])

memoryText : Memory → Text
memoryText fact = toList "Fact"
memoryText experiential = toList "Experiential"
memoryText working = toList "Working"

readMemoryText : Text → Fault ⊎ Memory
readMemoryText text with text ≟Text toList "Fact"
... | yes _ = inj₂ fact
... | no _ with text ≟Text toList "Experiential"
...   | yes _ = inj₂ experiential
...   | no _ with text ≟Text toList "Working"
...     | yes _ = inj₂ working
...     | no _ = inj₁ (fault [] malformedInput "unknown memory type")

readMemory : Value → Fault ⊎ Memory
readMemory raw = asString raw >>= readMemoryText

memoryRoundTrip : ∀ memory → readMemory (string (memoryText memory)) ≡ inj₂ memory
memoryRoundTrip fact = refl
memoryRoundTrip experiential = refl
memoryRoundTrip working = refl

beliefNames patternNames : List Text
beliefNames = toList "kind" ∷ toList "key" ∷ toList "content" ∷ toList "memory_type" ∷ toList "grounding" ∷ []
patternNames = toList "kind" ∷ toList "key" ∷ toList "situation" ∷ toList "approach" ∷ []

beliefFields : (Value → Fault ⊎ ℕ) → DuplicatePolicy → Object.View → Fault ⊎ Candidate
beliefFields readID duplicates view = required (toList "key") asString view >>= λ name →
  required (toList "content") asString view >>= λ content →
  defaulted (toList "memory_type") experiential readMemory view >>= λ memory →
  defaulted (toList "grounding") [] (readArray (readCitation readID duplicates)) view >>= λ cited →
  inj₂ (belief name content memory cited)

patternFields : Object.View → Fault ⊎ Candidate
patternFields view = required (toList "key") asString view >>= λ name →
  required (toList "situation") asString view >>= λ situation →
  required (toList "approach") asString view >>= λ approach →
  inj₂ (patternCandidate name situation approach)

dispatch : (Value → Fault ⊎ ℕ) → DuplicatePolicy → Value → Text → Fault ⊎ Candidate
dispatch readID duplicates raw tag with tag ≟Text toList "belief"
... | yes _ = readRecord forbid duplicates beliefNames (beliefFields readID duplicates) raw
... | no _ with tag ≟Text toList "pattern"
...   | yes _ = readRecord forbid duplicates patternNames patternFields raw
...   | no _ = inj₁ (fault (key "kind" ∷ []) malformedInput "unknown candidate kind")

decode : (Value → Fault ⊎ ℕ) → DuplicatePolicy → Value → Fault ⊎ Candidate
decode readID duplicates raw = asObject raw >>= λ fields →
  required (toList "kind") asString (Object.normalize fields) >>= dispatch readID duplicates raw

encode : (ℕ → Text) → Candidate → Value
encode writeID (belief name content memory cited) = object
  ((toList "kind" , string (toList "belief")) ∷
   (toList "key" , string name) ∷
   (toList "content" , string content) ∷
   (toList "memory_type" , string (memoryText memory)) ∷ [] ++ citations cited)
  where
  citations : List Documents.Citation → List (Text × Value)
  citations [] = []
  citations cited@(_ ∷ _) = (toList "grounding" , array (map (encodeCitation writeID) cited)) ∷ []
encode writeID (patternCandidate name situation approach) = object
  ((toList "kind" , string (toList "pattern")) ∷
   (toList "key" , string name) ∷
   (toList "situation" , string situation) ∷
   (toList "approach" , string approach) ∷ [])

-- UUID conversion is an external scalar boundary. Require its round trip
-- only for the cited IDs, with no formatter implementation or unrestricted
-- natural-number-to-UUID inverse assumed by this application law.
module RoundTrip (readID : Value → Fault ⊎ ℕ) (writeID : ℕ → Text) where
  Scalar : Documents.Citation → Set
  Scalar cited = readID (string (writeID (Documents.Citation.chunk cited))) ≡ inj₂ (Documents.Citation.chunk cited)

  citation : ∀ duplicates cited → Scalar cited →
    readCitation readID duplicates (encodeCitation writeID cited) ≡ inj₂ cited
  citation rejectKnownRepeated (Documents.citation id path quotedText why) same rewrite same = refl
  citation keepLast (Documents.citation id path quotedText why) same rewrite same = refl

  elements : ∀ duplicates offset cited → All Scalar cited →
    readElementsFrom offset (readCitation readID duplicates) (map (encodeCitation writeID) cited) ≡ inj₂ cited
  elements duplicates offset [] [] = refl
  elements duplicates offset (first ∷ rest) (proof ∷ proofs)
    rewrite citation duplicates first proof | elements duplicates (suc offset) rest proofs = refl

  IDs : Candidate → Set
  IDs (belief name content memory cited) = All Scalar cited
  IDs (patternCandidate name situation approach) = ⊤

  roundTrip : ∀ duplicates value → IDs value → decode readID duplicates (encode writeID value) ≡ inj₂ value
  roundTrip rejectKnownRepeated (belief name content fact []) valid = refl
  roundTrip rejectKnownRepeated (belief name content experiential []) valid = refl
  roundTrip rejectKnownRepeated (belief name content working []) valid = refl
  roundTrip keepLast (belief name content fact []) valid = refl
  roundTrip keepLast (belief name content experiential []) valid = refl
  roundTrip keepLast (belief name content working []) valid = refl
  roundTrip rejectKnownRepeated (belief name content fact cited@(_ ∷ _)) valid rewrite elements rejectKnownRepeated 0 cited valid = refl
  roundTrip rejectKnownRepeated (belief name content experiential cited@(_ ∷ _)) valid rewrite elements rejectKnownRepeated 0 cited valid = refl
  roundTrip rejectKnownRepeated (belief name content working cited@(_ ∷ _)) valid rewrite elements rejectKnownRepeated 0 cited valid = refl
  roundTrip keepLast (belief name content fact cited@(_ ∷ _)) valid rewrite elements keepLast 0 cited valid = refl
  roundTrip keepLast (belief name content experiential cited@(_ ∷ _)) valid rewrite elements keepLast 0 cited valid = refl
  roundTrip keepLast (belief name content working cited@(_ ∷ _)) valid rewrite elements keepLast 0 cited valid = refl
  roundTrip rejectKnownRepeated (patternCandidate name situation approach) valid = refl
  roundTrip keepLast (patternCandidate name situation approach) valid = refl

checkedDecode : (Value → Fault ⊎ ℕ) → DuplicatePolicy → Value → Fault ⊎ (Σ[ c ∈ Candidate ] Valid c)
checkedDecode readID duplicates raw = validateDecoded validate (decode readID duplicates raw)

validCandidateAccepted : ∀ readID writeID duplicates c → RoundTrip.IDs readID writeID c → Valid c →
  Σ[ proof ∈ Valid c ] checkedDecode readID duplicates (encode writeID c) ≡ inj₂ (c , proof)
validCandidateAccepted readID writeID duplicates c ids valid rewrite RoundTrip.roundTrip readID writeID duplicates c ids =
  validDecodedAccepted validate c valid
