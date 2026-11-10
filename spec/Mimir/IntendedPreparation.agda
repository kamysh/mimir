{-# OPTIONS --safe #-}
-- Pure evaluation of the metadata surrounding a public write. Business
-- evaluation is separate: its world and answer come from the operation's
-- independent intent, never from executing an effect script.
module Mimir.IntendedPreparation where

open import Data.Bool using (true; false)
open import Data.Integer using (ℤ)
import Data.List
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Data.String using (String)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.ApplicationStore as Store
import Mimir.OperationControls as Controls
import Mimir.PublicOperationBinding as Binding
import Mimir.PublicRequest as Public
import Mimir.PublicInput as PublicInput
import Mimir.ProjectDeletion as Project
import Mimir.StandardLibrary as Library
import Mimir.PublicEncoding as Encoding
import Mimir.StorageReadBinding as StorageReads
import Mimir.LearningQueryBinding as LearningReads
import Mimir.StructuredValue as Wire
import Mimir.ToolCatalog as Tools
import Mimir.Validation as Validation

-- Missing test observations are not application outcomes. In particular, a
-- missing capture must not manufacture a product request for user input.
data ObservationError : Set where
  observationError : Validation.Fault → ObservationError

module Evaluate (library : Library.Contract) (postgres : Controls.PostgreSQL) where
  module C = Binding.Creating library postgres
  module Read = Controls.Readback library postgres

  -- These are external facts from the same attempted execution, not an
  -- expected world, a desired reply, an admission context or a recovery proof.
  -- The transport adapter is responsible for matching their operation token,
  -- boundary and attempt to the retained observation artifacts.
  record Observations (call : C.Call) : Set where
    field
      currentSettings : C.Settings
      bindingTime : Maybe ℤ
      planEncoding : Maybe (C.PlanEncoding call)

  Outcome = Store.World × C.Result
  Evaluation = ObservationError Data.Sum.⊎ Outcome

  module With (observed : (call : C.Call) → Observations call) where
    missing : String → String → ObservationError
    missing kind explanation = observationError (Validation.fault
      (Validation.key "observations" Data.List.∷ Validation.key kind Data.List.∷ Data.List.[])
      Validation.missingField explanation)

    finishPlan : C.Call → Store.World × C.PlanResult → Evaluation
    finishPlan call (after , C.planned binding model raw) =
      inj₂ (after , C.ready (C.preparedWrite call binding model raw))
    finishPlan call (after , C.planRefused fault) = inj₂ (after , C.needsInput fault)
    finishPlan call (after , C.planCancelled receipt) =
      inj₂ (after , C.returned (Read.answer (C.Call.token call) after))
    finishPlan call (after , C.planUnknown) =
      inj₂ (after , C.returned (Read.answer (C.Call.token call) after))

    -- A stored plan is enough on retry. A new codec observation is required
    -- only when this invocation actually has to publish a new plan.
    publishPlan : C.Call → Wire.Value → Store.World → Evaluation
    publishPlan call settings before with C.binding (C.Call.token call) before
    ... | nothing = finishPlan call (before , C.planUnknown)
    ... | just original with C.matches call settings original
    ... | false = finishPlan call (before , C.planRefused Binding.changedRequest)
    ... | true with Store.lookupCancellation before (C.Call.token call)
    ... | just receipt = finishPlan call (before , C.planCancelled receipt)
    ... | nothing with C.plan (C.Call.token call) before
    ... | just raw = finishPlan call (before , C.existingPlan original raw)
    ... | nothing with Read.savedRows (C.Call.token call) before
    ... | _ Data.List.∷ _ = finishPlan call (before , C.planRefused C.badPlan)
    ... | Data.List.[] with Observations.planEncoding (observed call)
    ... | nothing = inj₁ (missing "plan_encoding"
      "The oracle needs the actual validated standard plan encoding for this new plan. Capture that encoding for the same operation and attempt; do not invent it or report a product correction. Existing saved plans need no fresh encoding receipt.")
    ... | just codecReceipt = finishPlan call (C.saveNewPlan call original codecReceipt before)

    currentPolicy : C.Call → Wire.Value → C.Settings → Store.World → Evaluation
    currentPolicy call original (C.unavailable fault) before = inj₂ (before , C.needsInput fault)
    currentPolicy call original (C.configured current) before with
      Controls.PostgreSQL.jsonbEqual postgres original current
    ... | false = inj₂ (before , C.needsInput C.changedPolicy)
    ... | true = publishPlan call original before

    preparePlan : C.Call → Wire.Value → Store.World → Evaluation
    preparePlan call settings before with C.needsPolicy (C.Call.tool call)
    ... | false = publishPlan call settings before
    ... | true = currentPolicy call settings
      (Observations.currentSettings (observed call)) before

    resume : C.Call → Wire.Value → Store.World → Read.Result → Evaluation
    resume call settings before (Read.awaitingPlan _) = preparePlan call settings before
    resume call settings before (Read.awaitingCompletion _) = preparePlan call settings before
    resume call settings before (Read.pending _ _ _) = preparePlan call settings before
    resume call settings before outcome = inj₂ (before , C.returned outcome)

    finishBinding : C.Call → Wire.Value → Store.World × C.BindingResult → Evaluation
    finishBinding call settings (after , C.bound original) =
      resume call settings after (Read.answer (C.Call.token call) after)
    finishBinding call settings (after , C.changed original) = inj₂ (after , C.needsInput Binding.changedRequest)
    finishBinding call settings (after , C.unknown) = inj₂ (after , C.returned (Read.answer (C.Call.token call) after))
    finishBinding call settings (after , C.cancelled receipt) = inj₂ (after , C.returned (Read.answer (C.Call.token call) after))

    -- Existing binding time is already part of the original world. A fresh
    -- PostgreSQL time must be captured only for a genuinely new binding.
    bind : C.Call → Wire.Value → Store.World → Evaluation
    bind call settings before with C.binding (C.Call.token call) before
    ... | just original = finishBinding call settings
      (C.bind call settings (Store.BindingRow.boundAt original) before)
    ... | nothing with Controls.reservation (C.Call.token call) before
    ... | nothing = finishBinding call settings (before , C.unknown)
    ... | just reservation with Store.lookupCancellation before (C.Call.token call)
    ... | just receipt = finishBinding call settings (before , C.cancelled receipt)
    ... | nothing with Observations.bindingTime (observed call)
    ... | nothing = inj₁ (missing "postgres_writer_clock"
      "The oracle needs the PostgreSQL time actually used for this new binding. Capture it for the same operation and attempt; do not invent a timestamp or turn a missing test observation into a product correction.")
    ... | just time = finishBinding call settings (C.bind call settings time before)

    freshSettings : C.Call → C.Settings → Store.World → Evaluation
    freshSettings call (C.unavailable fault) before = inj₂ (before , C.needsInput fault)
    freshSettings call (C.configured settings) before with
      Public.freshLearningAdmission (C.Call.request call)
    ... | inj₁ fault = inj₂ (before , C.needsInput fault)
    ... | inj₂ tt = bind call settings before

    unbound : C.Call → Store.World → Read.Result → Evaluation
    unbound call before Read.reserved =
      freshSettings call (Observations.currentSettings (observed call)) before
    unbound call before outcome = inj₂ (before , C.returned outcome)

    admitted : C.Call → Store.World → Evaluation
    admitted call before with C.binding (C.Call.token call) before
    ... | just original = bind call (Store.BindingRow.settings original) before
    ... | nothing = unbound call before (Read.answer (C.Call.token call) before)

    evaluate : C.Request → Store.World → Evaluation
    evaluate requested before with C.decode requested
    ... | inj₁ fault = inj₂ (before , C.needsInput fault)
    ... | inj₂ call = admitted call before

    malformedInputUnchanged : ∀ requested before fault →
      C.decode requested ≡ inj₁ fault →
      evaluate requested before ≡ inj₂ (before , C.needsInput fault)
    malformedInputUnchanged requested before fault rejected rewrite rejected = refl

  -- Typed semantic output for the public adapter. A returned null body stays
  -- distinct from admission which never entered the business operation.
  data PublicOutcome : Set where
    requestCorrection : Validation.Fault → PublicOutcome
    operationReadback : Read.Result → PublicOutcome
    directValue : Wire.Value → PublicOutcome

  record Expected (Body : Set) : Set where
    constructor expected
    field
      world : Store.World
      body : Maybe Body
      publicOutcome : PublicOutcome

  module OperationReadback where
    module Decode = Public.Decode library

    -- The complete saved state supplies the answer. This includes malformed
    -- journals and cancellation; neither is replaced with an assumed success.
    read : ℕ → Store.World → Expected Read.Result
    read token before = expected before (just answer) (operationReadback answer)
      where answer = Read.answer token before

    afterToken : Validation.Fault Data.Sum.⊎ ℕ → Store.World → Expected Read.Result
    afterToken (inj₁ fault) before = expected before nothing (requestCorrection fault)
    afterToken (inj₂ token) before = read token before

    evaluate : Wire.Value → Store.World → Expected Read.Result
    evaluate raw before with Decode.readInvocation Tools.operationOutcome raw
    ... | inj₁ fault = expected before nothing (requestCorrection fault)
    ... | inj₂ admitted = afterToken
      (PublicInput.required "operation_token" (PublicInput.readUUID library)
        (Wire.Object.normalize (Decode.Invocation.suppliedFields admitted))) before

    afterTokenKeepsWorld : ∀ received before → Expected.world (afterToken received before) ≡ before
    afterTokenKeepsWorld (inj₁ fault) before = refl
    afterTokenKeepsWorld (inj₂ token) before = refl

    neverChangesWorld : ∀ raw before → Expected.world (evaluate raw before) ≡ before
    neverChangesWorld raw before with Decode.readInvocation Tools.operationOutcome raw
    ... | inj₁ fault = refl
    ... | inj₂ admitted = afterTokenKeepsWorld
      (PublicInput.required "operation_token" (PublicInput.readUUID library)
        (Wire.Object.normalize (Decode.Invocation.suppliedFields admitted))) before

    malformedRequestDoesNotEnterBody : ∀ raw before fault →
      Decode.readInvocation Tools.operationOutcome raw ≡ inj₁ fault →
      evaluate raw before ≡ expected before nothing (requestCorrection fault)
    malformedRequestDoesNotEnterBody raw before fault rejected rewrite rejected = refl

  module ReadOnly (format : Encoding.Formatting) where
    module Basic = StorageReads.BasicReads format using (Request; answer)
    module Experiences = LearningReads.ExperienceReads format using (Request; answer)

    basic : Basic.Request → Store.World → Expected Wire.Value
    basic request before = expected before (just answer) (directValue answer)
      where answer = Basic.answer request before

    experience : Experiences.Request → Store.World → Expected Wire.Value
    experience request before = expected before (just answer) (directValue answer)
      where answer = Experiences.answer request before

  module ProjectDeletion (observed : (call : C.Call) → Observations call) where
    module Metadata = With observed
    module Decode = Public.Decode library

    project : ∀ {raw} → Decode.Invocation Tools.deleteProject raw → Text
    project call = proj₁ (C.readProject (Decode.Invocation.arguments call)
      (Decode.Invocation.request call) (Decode.Invocation.decoded call))

    -- The operation input comes from the original submitted request. The
    -- metadata result cannot replace its token, project or desired outcome.
    prepared : Project.Registered.Input → Outcome → Expected Wire.Value
    prepared request (before , C.needsInput fault) =
      expected before nothing (requestCorrection fault)
    prepared request (before , C.returned outcome) =
      expected before nothing (operationReadback outcome)
    prepared request (before , C.ready context) =
      expected final (just answer)
        (operationReadback (Read.answer (Project.Registered.Input.token request) final))
      where
      final = Project.Registered.intended request before
      answer = Project.Registered.expectedReply request before

    evaluate : Wire.Value → Store.World → ObservationError Data.Sum.⊎ Expected Wire.Value
    evaluate raw before with Decode.readInvocation Tools.deleteProject raw
    ... | inj₁ fault = inj₂ (expected before nothing (requestCorrection fault))
    ... | inj₂ call with Metadata.admitted (C.admittedWrite Tools.deleteProject raw refl call) before
    ... | inj₁ missing = inj₁ missing
    ... | inj₂ outcome = inj₂ (prepared
      (Project.Registered.input (Decode.Invocation.operationToken call) (project call)) outcome)
