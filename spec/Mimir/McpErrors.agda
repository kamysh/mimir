{-# OPTIONS --safe #-}
-- Compatible error envelopes retain code/message and add structured refusal
-- data. Unknown/legacy errors remain opaque; an error code alone establishes
-- neither invalid arguments nor absence of database effects.
module Mimir.McpErrors where

open import Data.Integer using (ℤ; -[1+_])
import Data.Integer.Properties as Integer
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.String using (toList)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
open import Mimir.Validation using (Fault; fault; malformedInput)
open import Mimir.StructuredValue
open import Mimir.RecordDecoding
open import Mimir.JsonObjects using (forbid; rejectKnownRepeated)
import Mimir.FaultWire as FaultWire

data RefusalKind : Set where invalidInput candidateConflict undeclaredCandidate : RefusalKind

record Refusal : Set where
  constructor refusal
  field kind : RefusalKind; detail : Fault

record Error : Set where
  constructor error
  field code : ℤ; message : Text; details : Maybe Value

kindName : RefusalKind → Text
kindName invalidInput = toList "invalid_input"
kindName candidateConflict = toList "candidate_conflict"
kindName undeclaredCandidate = toList "undeclared_candidate"

readKindText : Text → Fault ⊎ RefusalKind
readKindText text with text ≟Text kindName invalidInput
... | yes _ = inj₂ invalidInput
... | no _ with text ≟Text kindName candidateConflict
...   | yes _ = inj₂ candidateConflict
...   | no _ with text ≟Text kindName undeclaredCandidate
...     | yes _ = inj₂ undeclaredCandidate
...     | no _ = inj₁ (fault [] malformedInput "unrecognized MCP refusal kind")

readKind : Value → Fault ⊎ RefusalKind
readKind raw = asString raw >>= readKindText

kindRoundTrip : ∀ kind → readKind (string (kindName kind)) ≡ inj₂ kind
kindRoundTrip invalidInput = refl
kindRoundTrip candidateConflict = refl
kindRoundTrip undeclaredCandidate = refl

names : List Text
names = toList "kind" ∷ toList "fault" ∷ []

readFields : Object.View → Fault ⊎ Refusal
readFields view = required (toList "kind") readKind view >>= λ kind →
  required (toList "fault") FaultWire.decode view >>= λ detail → inj₂ (refusal kind detail)

decodeRefusal : Value → Fault ⊎ Refusal
decodeRefusal = readRecord forbid rejectKnownRepeated names readFields

encodeRefusal : Refusal → Value
encodeRefusal r = object
  ((toList "kind" , string (kindName (Refusal.kind r))) ∷
   (toList "fault" , FaultWire.encode (Refusal.detail r)) ∷ [])

refusalRoundTrip : ∀ r → decodeRefusal (encodeRefusal r) ≡ inj₂ r
refusalRoundTrip (refusal kind detail) rewrite kindRoundTrip kind | FaultWire.roundTrip detail = refl

serverCode : ℤ
serverCode = -[1+ 31999 ]

encodeAt : ℤ → Refusal → Error
encodeAt code r = error code (Fault.explanation (Refusal.detail r)) (just (encodeRefusal r))

encode : Refusal → Error
encode = encodeAt serverCode

data Classification : Set where
  rejected : Refusal → Classification
  unclassified : Error → Classification

classifyAt : ℤ → Error → Classification
classifyAt expected e with Error.code e Integer.≟ expected
... | no _ = unclassified e
... | yes _ with Error.details e
...   | nothing = unclassified e
...   | just details with decodeRefusal details
...     | inj₁ failure = unclassified e
...     | inj₂ r = rejected r

classify : Error → Classification
classify = classifyAt serverCode

abstract
  roundTripAt : ∀ expected r → classifyAt expected (encodeAt expected r) ≡ rejected r
  roundTripAt expected r with expected Integer.≟ expected
  ... | no impossible = ⊥-elim (impossible refl)
  ... | yes same rewrite refusalRoundTrip r = refl

roundTrip : ∀ r → classify (encode r) ≡ rejected r
roundTrip r = roundTripAt serverCode r

legacyMessagePreserved : ∀ r → Error.message (encode r) ≡ Fault.explanation (Refusal.detail r)
legacyMessagePreserved r = refl

abstract
  legacyAt : ∀ expected code message → classifyAt expected (error code message nothing) ≡ unclassified (error code message nothing)
  legacyAt expected code message with code Integer.≟ expected
  ... | yes _ = refl
  ... | no _ = refl

legacyIsNotValidation : ∀ code message → classify (error code message nothing) ≡ unclassified (error code message nothing)
legacyIsNotValidation = legacyAt serverCode

data Operation : Set where query review : Operation
data Recovery : Set where
  correctArguments : Fault → Recovery
  reconsiderCandidate : Fault → Recovery
  repairCandidateReference : Fault → Recovery
  inspectReceipt : Error → Recovery
  serviceFailure : Error → Recovery

recover : Operation → Classification → Recovery
recover operation (rejected (refusal invalidInput detail)) = correctArguments detail
recover operation (rejected (refusal candidateConflict detail)) = reconsiderCandidate detail
recover operation (rejected (refusal undeclaredCandidate detail)) = repairCandidateReference detail
recover review (unclassified e) = inspectReceipt e
recover query (unclassified e) = serviceFailure e

unknownReviewFailureReadFirst : ∀ e → recover review (unclassified e) ≡ inspectReceipt e
unknownReviewFailureReadFirst e = refl

-- Server-side construction is justified by the actual state transition.
-- Decoding a remote claim is deliberately not a proof about an unseen world.
record CertifiedRefusal (World : Set) (before after : World) : Set where
  constructor certifiedRefusal
  field report : Refusal; unchanged : after ≡ before

certifiedMeansNoChange : ∀ {World before after} → CertifiedRefusal World before after → after ≡ before
certifiedMeansNoChange = CertifiedRefusal.unchanged

refuseBeforeMutation : ∀ {World} (before : World) r → CertifiedRefusal World before before
refuseBeforeMutation before r = certifiedRefusal r refl

emit : ∀ {World before after} → CertifiedRefusal World before after → Error
emit certified = encode (CertifiedRefusal.report certified)

emittedRefusalPreserved : ∀ {World before after} (certified : CertifiedRefusal World before after) →
  classify (emit certified) ≡ rejected (CertifiedRefusal.report certified)
emittedRefusalPreserved certified = roundTrip (CertifiedRefusal.report certified)

-- Actionable correction is an ordinary tool outcome, not a JSON-RPC failure.
-- A server may claim no business changes only with the corresponding actual
-- state equality. Unknown write outcomes still require receipt inspection.
module AgentCorrection where
  data Location : Set where request arguments configuration : Location

  record Item : Set where
    constructor item
    field
      location : Location
      failure : Fault
      expected suggestedCorrection : Text

  -- A response cannot claim that correction is needed without naming an issue.
  record Claim : Set where
    constructor claim
    field first : Item; rest : List Item

  record Certified (World : Set) (before after : World) : Set where
    constructor certified
    field report : Claim; unchanged : after ≡ before

  changedStateCannotBeCertified : ∀ {World before after} → after ≢ before →
    Certified World before after → ⊥
  changedStateCannotBeCertified changed proof = changed (Certified.unchanged proof)

  locationName : Location → Text
  locationName request = toList "request"
  locationName arguments = toList "arguments"
  locationName configuration = toList "configuration"

  instruction : Text
  instruction = toList "Correct the indicated fields and retry. If a required value is not known, ask the user instead of guessing."

  private
    encodeItem : Item → Value
    encodeItem detail = object
      ((toList "location" , string (locationName (Item.location detail))) ∷
       (toList "fault" , FaultWire.encode (Item.failure detail)) ∷
       (toList "expected" , string (Item.expected detail)) ∷
       (toList "suggested_correction" , string (Item.suggestedCorrection detail)) ∷ [])

  emitCorrection : ∀ {World before after} → Certified World before after → Value
  emitCorrection proof = object
    ((toList "status" , string (toList "needs_input")) ∷
     (toList "business_changes" , string (toList "none")) ∷
     (toList "next_action" , string (toList "correct_request_or_ask_user")) ∷
     (toList "message" , string instruction) ∷
     (toList "issues" , array (map encodeItem (Claim.first report ∷ Claim.rest report))) ∷ [])
    where report = Certified.report proof
