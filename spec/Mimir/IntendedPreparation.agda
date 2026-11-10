{-# OPTIONS --safe #-}
-- Pure evaluation of the metadata surrounding a public write. Business
-- evaluation is separate: its world and answer come from the operation's
-- independent intent, never from executing an effect script.
module Mimir.IntendedPreparation where

open import Data.Bool using (true; false)
open import Data.Integer using (ℤ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.ApplicationStore as Store
import Mimir.OperationControls as Controls
import Mimir.PublicOperationBinding as Binding
import Mimir.PublicRequest as Public
import Mimir.ProjectDeletion as Project
import Mimir.StandardLibrary as Library
import Mimir.PublicEncoding as Encoding
import Mimir.StorageReadBinding as StorageReads
import Mimir.LearningQueryBinding as LearningReads
import Mimir.StructuredValue as Wire
import Mimir.ToolCatalog as Tools
import Mimir.Validation as Validation

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
      bindingTime : ℤ
      planEncoding : C.PlanEncoding call

  Outcome = Store.World × C.Result

  module With (observed : (call : C.Call) → Observations call) where
    publishPlan : C.Call → Wire.Value → Store.World → Outcome
    publishPlan call settings before with
      C.prepare call settings (Observations.planEncoding (observed call)) before
    ... | after , C.planned binding model raw =
      after , C.ready (C.preparedWrite call binding model raw)
    ... | after , C.planRefused fault = after , C.needsInput fault
    ... | after , C.planCancelled receipt =
      after , C.returned (Read.answer (C.Call.token call) after)
    ... | after , C.planUnknown =
      after , C.returned (Read.answer (C.Call.token call) after)

    currentPolicy : C.Call → Wire.Value → C.Settings → Store.World → Outcome
    currentPolicy call original (C.unavailable fault) before = before , C.needsInput fault
    currentPolicy call original (C.configured current) before with
      Controls.PostgreSQL.jsonbEqual postgres original current
    ... | false = before , C.needsInput C.changedPolicy
    ... | true = publishPlan call original before

    preparePlan : C.Call → Wire.Value → Store.World → Outcome
    preparePlan call settings before with C.needsPolicy (C.Call.tool call)
    ... | false = publishPlan call settings before
    ... | true = currentPolicy call settings
      (Observations.currentSettings (observed call)) before

    resume : C.Call → Wire.Value → Store.World → Read.Result → Outcome
    resume call settings before (Read.awaitingPlan _) = preparePlan call settings before
    resume call settings before (Read.awaitingCompletion _) = preparePlan call settings before
    resume call settings before (Read.pending _ _ _) = preparePlan call settings before
    resume call settings before outcome = before , C.returned outcome

    bind : C.Call → Wire.Value → Store.World → Outcome
    bind call settings before with
      C.bind call settings (Observations.bindingTime (observed call)) before
    ... | after , C.bound original =
      resume call settings after (Read.answer (C.Call.token call) after)
    ... | after , C.changed original = after , C.needsInput Binding.changedRequest
    ... | after , C.unknown = after , C.returned (Read.answer (C.Call.token call) after)
    ... | after , C.cancelled receipt = after , C.returned (Read.answer (C.Call.token call) after)

    freshSettings : C.Call → C.Settings → Store.World → Outcome
    freshSettings call (C.unavailable fault) before = before , C.needsInput fault
    freshSettings call (C.configured settings) before with
      Public.freshLearningAdmission (C.Call.request call)
    ... | inj₁ fault = before , C.needsInput fault
    ... | inj₂ tt = bind call settings before

    unbound : C.Call → Store.World → Read.Result → Outcome
    unbound call before Read.reserved =
      freshSettings call (Observations.currentSettings (observed call)) before
    unbound call before outcome = before , C.returned outcome

    admitted : C.Call → Store.World → Outcome
    admitted call before with C.binding (C.Call.token call) before
    ... | just original = bind call (Store.BindingRow.settings original) before
    ... | nothing = unbound call before (Read.answer (C.Call.token call) before)

    evaluate : C.Request → Store.World → Outcome
    evaluate requested before with C.decode requested
    ... | inj₁ fault = before , C.needsInput fault
    ... | inj₂ call = admitted call before

    malformedInputUnchanged : ∀ requested before fault →
      C.decode requested ≡ inj₁ fault →
      evaluate requested before ≡ (before , C.needsInput fault)
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

    evaluate : Wire.Value → Store.World → Expected Wire.Value
    evaluate raw before with Decode.readInvocation Tools.deleteProject raw
    ... | inj₁ fault = expected before nothing (requestCorrection fault)
    ... | inj₂ call = prepared
      (Project.Registered.input (Decode.Invocation.operationToken call) (project call))
      (Metadata.admitted (C.admittedWrite Tools.deleteProject raw refl call) before)
