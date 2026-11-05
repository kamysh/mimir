{-# OPTIONS --safe #-}
-- Lossless structured validation faults. Diagnostic paths are strings or
-- nonnegative array indices; error text is data and is never an instruction.
module Mimir.FaultWire where

open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Integer using (+_)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (toList)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
open import Mimir.Validation
open import Mimir.StructuredValue
open import Mimir.RecordDecoding
open import Mimir.JsonObjects using (forbid; rejectKnownRepeated)

codeName : Code → Text
codeName emptyText = toList "empty_text"
codeName textTooLong = toList "text_too_long"
codeName tooMany = toList "too_many"
codeName duplicate = toList "duplicate"
codeName missingReference = toList "missing_reference"
codeName wrongActor = toList "wrong_actor"
codeName quotationMismatch = toList "quotation_mismatch"
codeName staleRevision = toList "stale_revision"
codeName wrongIdentity = toList "wrong_identity"
codeName invalidNumber = toList "invalid_number"
codeName invalidInterval = toList "invalid_interval"
codeName missingEvidence = toList "missing_evidence"
codeName unsupportedCombination = toList "unsupported_combination"
codeName malformedInput = toList "malformed_input"

codes : List Code
codes = emptyText ∷ textTooLong ∷ tooMany ∷ duplicate ∷ missingReference ∷ wrongActor ∷
  quotationMismatch ∷ staleRevision ∷ wrongIdentity ∷ invalidNumber ∷ invalidInterval ∷
  missingEvidence ∷ unsupportedCombination ∷ malformedInput ∷ []

findCode : Text → List Code → Maybe Code
findCode text [] = nothing
findCode text (c ∷ rest) with text ≟Text codeName c
... | yes _ = just c
... | no _ = findCode text rest

findComplete : ∀ c → findCode (codeName c) codes ≡ just c
findComplete emptyText = refl
findComplete textTooLong = refl
findComplete tooMany = refl
findComplete duplicate = refl
findComplete missingReference = refl
findComplete wrongActor = refl
findComplete quotationMismatch = refl
findComplete staleRevision = refl
findComplete wrongIdentity = refl
findComplete invalidNumber = refl
findComplete invalidInterval = refl
findComplete missingEvidence = refl
findComplete unsupportedCombination = refl
findComplete malformedInput = refl

readCodeText : Text → Fault ⊎ Code
readCodeText text with findCode text codes
... | just c = inj₂ c
... | nothing = inj₁ (fault [] malformedInput "unknown validation fault code")

readCode : Value → Fault ⊎ Code
readCode raw = asString raw >>= readCodeText

codeRoundTrip : ∀ c → readCode (string (codeName c)) ≡ inj₂ c
codeRoundTrip c rewrite findComplete c = refl

encodeSegment : Segment → Value
encodeSegment (fieldKey name) = string name
encodeSegment (index offset) = unsigned offset

readSegment : Value → Fault ⊎ Segment
readSegment (string name) = inj₂ (fieldKey name)
readSegment (unsigned offset) = inj₂ (index offset)
readSegment (signed (+ offset)) = inj₂ (index offset)
readSegment _ = inj₁ (fault [] malformedInput "fault path needs a field name or nonnegative index")

segmentRoundTrip : ∀ segment → readSegment (encodeSegment segment) ≡ inj₂ segment
segmentRoundTrip (fieldKey name) = refl
segmentRoundTrip (index offset) = refl

names : List Text
names = toList "path" ∷ toList "code" ∷ toList "message" ∷ []

readFields : Object.View → Fault ⊎ Fault
readFields view = required (toList "path") (readArray readSegment) view >>= λ path →
  required (toList "code") readCode view >>= λ code →
  required (toList "message") asString view >>= λ message →
  inj₂ (problem path code message)

decode : Value → Fault ⊎ Fault
decode = readRecord forbid rejectKnownRepeated names readFields

encode : Fault → Value
encode failure = object
  ((toList "path" , array (map encodeSegment (Fault.path failure))) ∷
   (toList "code" , string (codeName (Fault.code failure))) ∷
   (toList "message" , string (Fault.explanation failure)) ∷ [])

roundTrip : ∀ failure → decode (encode failure) ≡ inj₂ failure
roundTrip (problem path code message)
  rewrite elementsRoundTrip encodeSegment readSegment segmentRoundTrip 0 path | codeRoundTrip code = refl

-- The model and the durable diagnostic decode the same full value, including
-- arbitrary source-specific explanation text and every indexed path segment.
feedbackRoundTrip : ∀ failure →
  mapResult deliver (decode (encode failure)) ≡ inj₂ (feedback failure failure)
feedbackRoundTrip failure rewrite roundTrip failure = refl
