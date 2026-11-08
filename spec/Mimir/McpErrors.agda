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
open import Data.String using (String; toList)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Mimir.Text using (Text; trim)
open import Data.Unit using (⊤; tt)
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

  uuidItem : List Mimir.Validation.Segment → Item
  uuidItem path = item arguments
    (fault path malformedInput "The supplied identifier is not a valid UUID.")
    (toList "A UUID returned by Mimir for the intended record, in a form accepted by the tool's UUID parser.")
    (toList "Copy the stored UUID from the relevant Mimir lookup result. For a new record, omit the ID only if this tool explicitly assigns it. If the intended record is unknown, ask the user. Do not invent an identifier.")

  missingStoredReference : String → Text → Text → Item
  missingStoredReference fieldName explanation lookup = item arguments
    (Mimir.Validation.problem (Mimir.Validation.key fieldName ∷ [])
      Mimir.Validation.missingReference explanation)
    (toList "An identifier of the intended record that is currently stored in Mimir.")
    lookup

  staleRevisionItem : List Mimir.Validation.Segment → Text → Text → Item
  staleRevisionItem path explanation readback = item arguments
    (Mimir.Validation.problem path Mimir.Validation.staleRevision explanation)
    (toList "The current revision returned by Mimir for the same stored experience and review.")
    readback

  beliefReferenceItem : Fault → Item
  beliefReferenceItem detail = item arguments detail
    (toList "A currently stored fact or experiential belief owned by the experience's exact project; global and working beliefs are not learning targets.")
    (toList "Use list_beliefs or query_learning_context for the stated project, inspect the returned project's value and memory type, and select the intended project-owned belief. If the intended reference or project is uncertain, ask the user. Do not invent an ID, move a belief, change the project, or change its memory type to bypass this check.")

  patternReferenceItem : Fault → Item
  patternReferenceItem detail = item arguments detail
    (toList "A currently stored pattern belonging to the experience project, or an untagged global pattern.")
    (toList "Use list_patterns for the experience project and inspect the returned pattern. Select the intended permitted pattern, omit the optional pattern reference only if no pattern was used, or ask the user. Do not invent an ID or move a pattern between projects.")

  itemReferenceItem : Fault → Item
  itemReferenceItem detail = item arguments detail
    (toList "A new learning item with a stable local key and no supplied ID, or an existing item owned by this experience with its original source and actor. Assessment item keys must resolve within that experience.")
    (toList "Call get_experience and get_learning_review with the same experience ID; use experience_history to inspect prior item keys, assigned IDs and recorded authorship. For a new item, supply its stable local key and omit id so PostgreSQL assigns it. Reuse the returned mapping on retries. If the intended item is unknown, ask the user. Do not invent or silently replace an ID, change source_ref or actor, or create another observation to bypass the conflict.")

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

  -- Decode the application response, not JSON syntax. A tag alone cannot
  -- bypass the ordinary tool-result checks or certify the remote database.
  record Decoded : Set where
    constructor decoded
    field message : Text; report : Claim

  nonblank : Value → Fault ⊎ Text
  nonblank raw = asString raw >>= λ text → keep text (trim text)
    where
    keep : Text → Text → Fault ⊎ Text
    keep text [] = inj₁ (fault [] malformedInput "correction guidance must not be blank")
    keep text (_ ∷ _) = inj₂ text

  literal : Text → Value → Fault ⊎ ⊤
  literal expected raw = asString raw >>= λ actual → equal expected actual
    where
    equal : Text → Text → Fault ⊎ ⊤
    equal expected actual with expected ≟Text actual
    ... | yes _ = inj₂ tt
    ... | no _ = inj₁ (fault [] malformedInput "unexpected correction response field value")

  readLocation : Value → Fault ⊎ Location
  readLocation raw = asString raw >>= choose
    where
    choose : Text → Fault ⊎ Location
    choose text with text ≟Text toList "request"
    ... | yes _ = inj₂ request
    ... | no _ with text ≟Text toList "arguments"
    ...   | yes _ = inj₂ arguments
    ...   | no _ with text ≟Text toList "configuration"
    ...     | yes _ = inj₂ configuration
    ...     | no _ = inj₁ (fault [] malformedInput "unknown correction location")

  explainedFault : Value → Fault ⊎ Fault
  explainedFault raw = FaultWire.decode raw >>= λ detail →
    nonblank (string (Fault.explanation detail)) >>= λ _ → inj₂ detail

  readItem : Value → Fault ⊎ Item
  readItem = readRecord forbid rejectKnownRepeated
    (toList "location" ∷ toList "fault" ∷ toList "expected" ∷ toList "suggested_correction" ∷ []) λ fields →
      required (toList "location") readLocation fields >>= λ location →
      required (toList "fault") explainedFault fields >>= λ failure →
      required (toList "expected") nonblank fields >>= λ expected →
      required (toList "suggested_correction") nonblank fields >>= λ suggested →
      inj₂ (item location failure expected suggested)

  readClaim : Value → Fault ⊎ Claim
  readClaim raw = readArray readItem raw >>= requireIssue
    where
    requireIssue : List Item → Fault ⊎ Claim
    requireIssue [] = inj₁ (fault [] malformedInput "a correction response must name an issue")
    requireIssue (first ∷ rest) = inj₂ (claim first rest)

  decode : Value → Fault ⊎ Decoded
  decode = readRecord forbid rejectKnownRepeated
    (toList "status" ∷ toList "business_changes" ∷ toList "next_action" ∷ toList "message" ∷ toList "issues" ∷ []) λ fields →
      required (toList "status") (literal (toList "needs_input")) fields >>= λ _ →
      required (toList "business_changes") (literal (toList "none")) fields >>= λ _ →
      required (toList "next_action") (literal (toList "correct_request_or_ask_user")) fields >>= λ _ →
      required (toList "message") nonblank fields >>= λ message →
      required (toList "issues") readClaim fields >>= λ report → inj₂ (decoded message report)

  inspect : Value → Fault ⊎ Maybe Decoded
  inspect value@(object fields) with Object.normalize fields (toList "status")
  ... | just (string status) with status ≟Text toList "needs_input"
  ...   | yes _ = mapResult just (decode value)
  ...   | no _ = inj₂ nothing
  inspect (object fields) | _ = inj₂ nothing
  inspect _ = inj₂ nothing
