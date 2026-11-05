{-# OPTIONS --safe #-}
module Mimir.SourceWire where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (toList)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
open import Mimir.SourceSchema
open import Mimir.Validation
open import Mimir.StructuredValue
open import Mimir.RecordDecoding
open import Mimir.JsonObjects using (DuplicatePolicy; rejectKnownRepeated; keepLast; forbid)

provenanceText : Provenance → Text
provenanceText userFeedback = toList "user_feedback"
provenanceText agentReport = toList "agent_report"
provenanceText toolResult = toList "tool_result"

readProvenanceText : Text → Fault ⊎ Provenance
readProvenanceText text with text ≟Text toList "user_feedback"
... | yes _ = inj₂ userFeedback
... | no _ with text ≟Text toList "agent_report"
...   | yes _ = inj₂ agentReport
...   | no _ with text ≟Text toList "tool_result"
...     | yes _ = inj₂ toolResult
...     | no _ = inj₁ (fault [] malformedInput "unknown observation source")

readProvenance : Value → Fault ⊎ Provenance
readProvenance raw = asString raw >>= readProvenanceText

provenanceRoundTrip : ∀ p → readProvenance (string (provenanceText p)) ≡ inj₂ p
provenanceRoundTrip userFeedback = refl
provenanceRoundTrip agentReport = refl
provenanceRoundTrip toolResult = refl

names : List Text
names = toList "source_ref" ∷ toList "actor" ∷ toList "provenance" ∷
  toList "text" ∷ toList "recorded_at" ∷ []

readFields : Object.View → Fault ⊎ Source
readFields view =
  required (toList "source_ref") asString view >>= λ reference →
  required (toList "actor") asString view >>= λ actor →
  required (toList "provenance") readProvenance view >>= λ provenance →
  required (toList "text") asString view >>= λ text →
  optional (toList "recorded_at") asString view >>= λ recordedAt →
  inj₂ (source reference actor text provenance recordedAt)

decode : DuplicatePolicy → Value → Fault ⊎ Source
decode duplicates = readRecord forbid duplicates names readFields

timestampFields : Maybe Text → List (Text × Value)
timestampFields nothing = []
timestampFields (just value) = (toList "recorded_at" , string value) ∷ []

encode : Source → Value
encode s = object
  ((toList "source_ref" , string (Source.reference s)) ∷
   (toList "actor" , string (Source.actor s)) ∷
   (toList "provenance" , string (provenanceText (Source.provenance s))) ∷
   (toList "text" , string (Source.text s)) ∷ timestampFields (Source.recordedAt s))

roundTrip : ∀ duplicates s → decode duplicates (encode s) ≡ inj₂ s
roundTrip rejectKnownRepeated (source reference actor text userFeedback nothing) = refl
roundTrip rejectKnownRepeated (source reference actor text userFeedback (just timestamp)) = refl
roundTrip rejectKnownRepeated (source reference actor text agentReport nothing) = refl
roundTrip rejectKnownRepeated (source reference actor text agentReport (just timestamp)) = refl
roundTrip rejectKnownRepeated (source reference actor text toolResult nothing) = refl
roundTrip rejectKnownRepeated (source reference actor text toolResult (just timestamp)) = refl
roundTrip keepLast (source reference actor text userFeedback nothing) = refl
roundTrip keepLast (source reference actor text userFeedback (just timestamp)) = refl
roundTrip keepLast (source reference actor text agentReport nothing) = refl
roundTrip keepLast (source reference actor text agentReport (just timestamp)) = refl
roundTrip keepLast (source reference actor text toolResult nothing) = refl
roundTrip keepLast (source reference actor text toolResult (just timestamp)) = refl

checkedDecode : DuplicatePolicy → Value → Fault ⊎ (Σ[ s ∈ Source ] SourceValid s)
checkedDecode duplicates raw = validateDecoded validateSource (decode duplicates raw)

validSourceAccepted : ∀ duplicates s → SourceValid s →
  Σ[ proof ∈ SourceValid s ] checkedDecode duplicates (encode s) ≡ inj₂ (s , proof)
validSourceAccepted duplicates s valid rewrite roundTrip duplicates s =
  validDecodedAccepted validateSource s valid
