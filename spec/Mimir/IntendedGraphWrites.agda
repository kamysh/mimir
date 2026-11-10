{-# OPTIONS --safe #-}
-- Exact pure expectations for these closed direct-write families. Business
-- values come from their reviewed meanings; no effect script is executed.
module Mimir.IntendedGraphWrites where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.String using (toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.ApplicationStore as Store
import Mimir.DirectGraphRecovery as Direct
import Mimir.GraphDeletion as Delete
import Mimir.GraphWrites as Writes
import Mimir.IntendedPreparation as Preparation
import Mimir.OperationControls as Controls
import Mimir.PublicPatternDeletionRecovery as PatternDeletion
import Mimir.PatternPublicationRecovery as PatternCreation
import Mimir.PublicEncoding as Encoding
import Mimir.PublicRequest as Public
import Mimir.RecoverableStoreStep as Step
import Mimir.StandardLibrary as Library
import Mimir.StructuredValue as Wire
import Mimir.ToolCatalog as Tools
import Mimir.Validation as Validation

data Family : Set where
  insertPattern deletePattern support cause contradiction : Family

tool : Family → Tools.Tool
tool insertPattern = Tools.insertPattern
tool deletePattern = Tools.deletePattern
tool support = Tools.recordSupport
tool cause = Tools.recordCause
tool contradiction = Tools.recordContradiction

writer : ∀ family → Tools.kind (tool family) ≡ Tools.businessWrite
writer insertPattern = refl
writer deletePattern = refl
writer support = refl
writer cause = refl
writer contradiction = refl

module Evaluate (library : Library.Contract) (postgres : Controls.PostgreSQL)
  (format : Encoding.Formatting) where
  module Base = Preparation.Evaluate library postgres
  module C = Base.C
  module Read = Base.Read
  module Decode = Public.Decode library
  module Pattern = PatternDeletion.Registered library using (original; key)
  module PatternIntent = Delete.PatternRecovery using (input; desired; answer)
  module Creation = PatternCreation.Registered library format using (original; key)
  module Encode = Encoding.Encode format using (patternValue)

  Body = Step.Result Validation.Fault
  Expected = Base.Expected Body
  Evaluation = Preparation.ObservationError ⊎ Expected
  Business = Validation.Fault ⊎ (Store.World × Wire.Value)
  BusinessObservation = Preparation.ObservationError ⊎ Business

  missingAllocation : Preparation.ObservationError
  missingAllocation = Preparation.observationError (Validation.fault
    (Validation.key "observations" ∷ Validation.key "pattern_allocation" ∷ []) Validation.missingField
    "The fresh pattern intent needs the actual PostgreSQL identity and creation time from this operation's publication attempt. Capture that receipt for the same token and boundary; do not invent a pattern or turn missing oracle input into a product correction. A saved completed result needs no fresh allocation.")

  private
    reflected : ℕ → Store.World → Body → Expected
    reflected token final reply = Base.expected final (just reply)
      (Base.operationReadback (Read.answer token final))

    refused : Store.World → Validation.Fault → Expected
    refused before fault = Base.expected before (just (Step.needsInput fault))
      (Base.requestCorrection fault)

    -- Original answers and their final marker are metadata, not business
    -- intent. Preserve both on replay, and never republish an incomplete pair.
    publication : ℕ → Text → BusinessObservation → Store.World → Evaluation
    publication token key (inj₁ missing) before = inj₁ missing
    publication token key (inj₂ (inj₁ fault)) before = inj₂ (refused before fault)
    publication token key (inj₂ (inj₂ (changed , answer))) before =
      inj₂ (reflected token final (Step.done answer))
      where
      final = Store.saveAnswer (Store.saveAnswer changed token key answer)
        token Step.resultKey answer

    single : ℕ → Text → BusinessObservation → Store.World → Evaluation
    single token key business before with Store.lookupCancellation before token
    ... | just receipt = inj₂ (reflected token before (Step.cancelled receipt))
    ... | nothing with Store.lookupSaved before token key | Store.lookupSaved before token Step.resultKey
    ... | just saved | just final = inj₂ (reflected token before (Step.done saved))
    ... | just _ | nothing = inj₂ (reflected token before Step.needsRecovery)
    ... | nothing | just _ = inj₂ (reflected token before Step.needsRecovery)
    ... | nothing | nothing = publication token key business before

  patternInsertion : ℕ → Maybe PatternCreation.Metadata → Store.World → Evaluation
  patternInsertion token allocation before with Creation.original token (Step.registration before)
  ... | inj₁ fault = inj₂ (refused before fault)
  ... | inj₂ args = single token (Creation.key token) (captured allocation) before
    where
    captured : Maybe PatternCreation.Metadata → BusinessObservation
    captured nothing = inj₁ missingAllocation
    captured (just received) = inj₂ (inj₂
      (Writes.insertPattern created before , Encode.patternValue created))
      where created = PatternCreation.createdPattern args received

  missingFreshPatternReceiptIsOracleInputError : ∀ token before args →
    Creation.original token (Step.registration before) ≡ inj₂ args →
    Store.lookupCancellation before token ≡ nothing →
    Store.lookupSaved before token (Creation.key token) ≡ nothing →
    Store.lookupSaved before token Step.resultKey ≡ nothing →
    patternInsertion token nothing before ≡ inj₁ missingAllocation
  missingFreshPatternReceiptIsOracleInputError token before args original active noStep noFinal
    rewrite original | active | noStep | noFinal = refl

  patternDeletion : ℕ → Store.World → Evaluation
  patternDeletion token before with Pattern.original token (Step.registration before)
  ... | inj₁ fault = inj₂ (refused before fault)
  ... | inj₂ identity = single token (Pattern.key token)
    (inj₂ (inj₂ (PatternIntent.desired request before , PatternIntent.answer request before))) before
    where request = PatternIntent.input token identity

  module Relationship (kind : Direct.Kind) where
    module R = Direct.Registered library kind using (original; key)
    module B = Direct.Business kind using (checked)

    evaluate : ℕ → Store.World → Evaluation
    evaluate token before with R.original token (Step.registration before)
    ... | inj₁ fault = inj₂ (refused before fault)
    ... | inj₂ requested = single token (R.key token) (inj₂ (proj₁ (B.checked requested before))) before

  business : Family → ℕ → Maybe PatternCreation.Metadata → Store.World → Evaluation
  business insertPattern token allocation = patternInsertion token allocation
  business deletePattern token allocation = patternDeletion token
  business support token allocation = Relationship.evaluate Direct.support token
  business cause token allocation = Relationship.evaluate Direct.cause token
  business contradiction token allocation = Relationship.evaluate Direct.contradiction token

  module With (observed : (call : C.Call) → Base.Observations call)
    (allocated : C.Call → Maybe PatternCreation.Metadata) where
    module Metadata = Base.With observed

    prepared : Family → C.Call → Base.Outcome → Evaluation
    prepared family call (before , C.needsInput fault) =
      inj₂ (Base.expected before nothing (Base.requestCorrection fault))
    prepared family call (before , C.returned outcome) =
      inj₂ (Base.expected before nothing (Base.operationReadback outcome))
    prepared family call (before , C.ready context) = business family (C.Call.token call) (allocated call) before

    evaluate : Family → Wire.Value → Store.World → Evaluation
    evaluate family raw before with Decode.readInvocation (tool family) raw
    ... | inj₁ fault = inj₂ (Base.expected before nothing (Base.requestCorrection fault))
    ... | inj₂ decodedCall = afterMetadata family call (Metadata.admitted call before)
      where
      call = C.admittedWrite (tool family) raw (writer family) decodedCall
      afterMetadata : Family → C.Call → Base.Evaluation → Evaluation
      afterMetadata family call (inj₁ missing) = inj₁ missing
      afterMetadata family call (inj₂ outcome) = prepared family call outcome

    malformedRequestKeepsWorldAndNoBody : ∀ family raw before fault →
      Decode.readInvocation (tool family) raw ≡ inj₁ fault →
      evaluate family raw before ≡ inj₂ (Base.expected before nothing (Base.requestCorrection fault))
    malformedRequestKeepsWorldAndNoBody family raw before fault rejected rewrite rejected = refl
