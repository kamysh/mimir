{-# OPTIONS --safe #-}
-- Exact pure expectations for these closed direct-write families. Business
-- values come from their reviewed meanings; no effect script is executed.
module Mimir.IntendedGraphWrites where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.ApplicationStore as Store
import Mimir.DirectGraphRecovery as Direct
import Mimir.GraphDeletion as Delete
import Mimir.IntendedPreparation as Preparation
import Mimir.OperationControls as Controls
import Mimir.PublicPatternDeletionRecovery as PatternDeletion
import Mimir.PublicRequest as Public
import Mimir.RecoverableStoreStep as Step
import Mimir.StandardLibrary as Library
import Mimir.StructuredValue as Wire
import Mimir.ToolCatalog as Tools
import Mimir.Validation as Validation

data Family : Set where
  deletePattern support cause contradiction : Family

tool : Family → Tools.Tool
tool deletePattern = Tools.deletePattern
tool support = Tools.recordSupport
tool cause = Tools.recordCause
tool contradiction = Tools.recordContradiction

writer : ∀ family → Tools.kind (tool family) ≡ Tools.businessWrite
writer deletePattern = refl
writer support = refl
writer cause = refl
writer contradiction = refl

module Evaluate (library : Library.Contract) (postgres : Controls.PostgreSQL) where
  module Base = Preparation.Evaluate library postgres
  module C = Base.C
  module Read = Base.Read
  module Decode = Public.Decode library
  module Pattern = PatternDeletion.Registered library using (original; key)
  module PatternIntent = Delete.PatternRecovery using (input; desired; answer)

  Body = Step.Result Validation.Fault
  Expected = Base.Expected Body
  Business = Validation.Fault ⊎ (Store.World × Wire.Value)

  private
    reflected : ℕ → Store.World → Body → Expected
    reflected token final reply = Base.expected final (just reply)
      (Base.operationReadback (Read.answer token final))

    refused : Store.World → Validation.Fault → Expected
    refused before fault = Base.expected before (just (Step.needsInput fault))
      (Base.requestCorrection fault)

    -- Original answers and their final marker are metadata, not business
    -- intent. Preserve both on replay, and never republish an incomplete pair.
    publication : ℕ → Text → Business → Store.World → Expected
    publication token key (inj₁ fault) before = refused before fault
    publication token key (inj₂ (changed , answer)) before =
      reflected token final (Step.done answer)
      where
      final = Store.saveAnswer (Store.saveAnswer changed token key answer)
        token Step.resultKey answer

    single : ℕ → Text → Business → Store.World → Expected
    single token key business before with Store.lookupCancellation before token
    ... | just receipt = reflected token before (Step.cancelled receipt)
    ... | nothing with Store.lookupSaved before token key | Store.lookupSaved before token Step.resultKey
    ... | just saved | just final = reflected token before (Step.done saved)
    ... | just _ | nothing = reflected token before Step.needsRecovery
    ... | nothing | just _ = reflected token before Step.needsRecovery
    ... | nothing | nothing = publication token key business before

  patternDeletion : ℕ → Store.World → Expected
  patternDeletion token before with Pattern.original token (Step.registration before)
  ... | inj₁ fault = refused before fault
  ... | inj₂ identity = single token (Pattern.key token)
    (inj₂ (PatternIntent.desired request before , PatternIntent.answer request before)) before
    where request = PatternIntent.input token identity

  module Relationship (kind : Direct.Kind) where
    module R = Direct.Registered library kind using (original; key)
    module B = Direct.Business kind using (checked)

    evaluate : ℕ → Store.World → Expected
    evaluate token before with R.original token (Step.registration before)
    ... | inj₁ fault = refused before fault
    ... | inj₂ requested = single token (R.key token) (proj₁ (B.checked requested before)) before

  business : Family → ℕ → Store.World → Expected
  business deletePattern = patternDeletion
  business support = Relationship.evaluate Direct.support
  business cause = Relationship.evaluate Direct.cause
  business contradiction = Relationship.evaluate Direct.contradiction

  module With (observed : (call : C.Call) → Base.Observations call) where
    module Metadata = Base.With observed

    prepared : Family → ℕ → Base.Outcome → Expected
    prepared family token (before , C.needsInput fault) =
      Base.expected before nothing (Base.requestCorrection fault)
    prepared family token (before , C.returned outcome) =
      Base.expected before nothing (Base.operationReadback outcome)
    prepared family token (before , C.ready context) = business family token before

    evaluate : Family → Wire.Value → Store.World → Expected
    evaluate family raw before with Decode.readInvocation (tool family) raw
    ... | inj₁ fault = Base.expected before nothing (Base.requestCorrection fault)
    ... | inj₂ decodedCall = prepared family (C.Call.token call) (Metadata.admitted call before)
      where call = C.admittedWrite (tool family) raw (writer family) decodedCall

    malformedRequestKeepsWorldAndNoBody : ∀ family raw before fault →
      Decode.readInvocation (tool family) raw ≡ inj₁ fault →
      evaluate family raw before ≡ Base.expected before nothing (Base.requestCorrection fault)
    malformedRequestKeepsWorldAndNoBody family raw before fault rejected rewrite rejected = refl
