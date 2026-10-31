{-# OPTIONS --safe #-}
-- The review candidate interface uses tagged snake_case variants and the
-- MemoryType enum's capitalized spellings. It is not the MCP query's memory
-- filter grammar. Missing memory_type defaults; explicit null does not.
module Mimir.CandidateWire where

open import Data.List using (List; []; _∷_)
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
beliefNames = toList "kind" ∷ toList "key" ∷ toList "content" ∷ toList "memory_type" ∷ []
patternNames = toList "kind" ∷ toList "key" ∷ toList "situation" ∷ toList "approach" ∷ []

beliefFields : Object.View → Fault ⊎ Candidate
beliefFields view = required (toList "key") asString view >>= λ name →
  required (toList "content") asString view >>= λ content →
  defaulted (toList "memory_type") experiential readMemory view >>= λ memory →
  inj₂ (belief name content memory)

patternFields : Object.View → Fault ⊎ Candidate
patternFields view = required (toList "key") asString view >>= λ name →
  required (toList "situation") asString view >>= λ situation →
  required (toList "approach") asString view >>= λ approach →
  inj₂ (patternCandidate name situation approach)

dispatch : DuplicatePolicy → Value → Text → Fault ⊎ Candidate
dispatch duplicates raw tag with tag ≟Text toList "belief"
... | yes _ = readRecord forbid duplicates beliefNames beliefFields raw
... | no _ with tag ≟Text toList "pattern"
...   | yes _ = readRecord forbid duplicates patternNames patternFields raw
...   | no _ = inj₁ (fault (key "kind" ∷ []) malformedInput "unknown candidate kind")

decode : DuplicatePolicy → Value → Fault ⊎ Candidate
decode duplicates raw = asObject raw >>= λ fields →
  required (toList "kind") asString (Object.normalize fields) >>= dispatch duplicates raw

encode : Candidate → Value
encode (belief name content memory) = object
  ((toList "kind" , string (toList "belief")) ∷
   (toList "key" , string name) ∷
   (toList "content" , string content) ∷
   (toList "memory_type" , string (memoryText memory)) ∷ [])
encode (patternCandidate name situation approach) = object
  ((toList "kind" , string (toList "pattern")) ∷
   (toList "key" , string name) ∷
   (toList "situation" , string situation) ∷
   (toList "approach" , string approach) ∷ [])

roundTrip : ∀ duplicates value → decode duplicates (encode value) ≡ inj₂ value
roundTrip rejectKnownRepeated (belief name content fact) = refl
roundTrip rejectKnownRepeated (belief name content experiential) = refl
roundTrip rejectKnownRepeated (belief name content working) = refl
roundTrip rejectKnownRepeated (patternCandidate name situation approach) = refl
roundTrip keepLast (belief name content fact) = refl
roundTrip keepLast (belief name content experiential) = refl
roundTrip keepLast (belief name content working) = refl
roundTrip keepLast (patternCandidate name situation approach) = refl

checkedDecode : DuplicatePolicy → Value → Fault ⊎ (Σ[ c ∈ Candidate ] Valid c)
checkedDecode duplicates raw = validateDecoded validate (decode duplicates raw)

validCandidateAccepted : ∀ duplicates c → Valid c →
  Σ[ proof ∈ Valid c ] checkedDecode duplicates (encode c) ≡ inj₂ (c , proof)
validCandidateAccepted duplicates c valid rewrite roundTrip duplicates c =
  validDecodedAccepted validate c valid
