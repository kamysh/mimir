{-# OPTIONS --safe #-}
-- The private CLI route executes the complete registered backfill certificate.
-- Configuration/startup remain ordinary owned I/O; no raw backfill script can
-- enter the business state. Completed historical answers precede model checks.
module Mimir.CLIReembed where

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.String using (toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.ConfigurationPath as Path
import Mimir.ConfigurationSchema as Config
import Mimir.ConfigurationValues as Values
import Mimir.ConfigurationProtocol as Configuration
import Mimir.ConnectionProtocol as Connection
import Mimir.ServiceStartup as Startup
import Mimir.MigrationRuntime as Migration
import Mimir.ApplicationStore as Store
import Mimir.BackfillRecovery as Backfill
import Mimir.BackfillPreparationRecovery as Preparation
import Mimir.BackfillOperationRecovery as BackfillOperation
import Mimir.OperationControls as Controls
import Mimir.PublicEncoding as Encoding
import Mimir.RecoverableStoreStep as Saved
import Mimir.Recovery as Recovery
import Mimir.StandardLibrary as Library
import Mimir.StructuredValue as Wire
import Mimir.Validation as Validation

-- Match native preparation::operation_settings. Credentials and cache paths
-- have no part in the immutable semantic model identity.
providerIdentity : Values.Embeddings → Wire.Value
providerIdentity settings with Values.Embeddings.backend settings
... | Values.local = Encoding.object
  (("backend" , Wire.string (toList "local")) ∷
   ("model" , Wire.string (toList "BAAI/bge-base-en-v1.5")) ∷ [])
... | Values.openai = Encoding.object
  (("backend" , Wire.string (toList "openai")) ∷
   ("model" , Wire.string (Values.Embeddings.model settings)) ∷ [])
... | Values.voyage = Encoding.object
  (("backend" , Wire.string (toList "voyage")) ∷
   ("model" , Wire.string (Values.Embeddings.model settings)) ∷
   ("input_type" , Wire.string (toList "document")) ∷ ("truncation" , Wire.boolean false) ∷ [])

settings : Config.Config → Wire.Value
settings configurationValue = Encoding.object (("embeddings" , optionalIdentity
  (Values.Config.embed (Config.Config.core configurationValue))) ∷ [])
  where
  optionalIdentity : Maybe Values.Embeddings → Wire.Value
  optionalIdentity nothing = Wire.null
  optionalIdentity (just configured) = providerIdentity configured

credentialsDoNotChangeIdentity : ∀ backend model firstKey firstCache secondKey secondCache →
  providerIdentity (Values.embeddings backend model firstKey firstCache) ≡
  providerIdentity (Values.embeddings backend model secondKey secondCache)
credentialsDoNotChangeIdentity Values.local model firstKey firstCache secondKey secondCache = refl
credentialsDoNotChangeIdentity Values.openai model firstKey firstCache secondKey secondCache = refl
credentialsDoNotChangeIdentity Values.voyage model firstKey firstCache secondKey secondCache = refl

data Summary : Set where
  completed : ℕ → Wire.Value → Summary
  needsDecision : ℕ → Validation.Fault → Summary
  needsReadback : ℕ → Summary
  cancelled : ℕ → Store.CancellationRow → Summary

summary : ℕ → Saved.Result Validation.Fault → Summary
summary token (Saved.done value) = completed token value
summary token (Saved.needsInput detail) = needsDecision token detail
summary token Saved.needsRecovery = needsReadback token
summary token (Saved.cancelled value) = cancelled token value

Success : Saved.Result Validation.Fault → Set
Success (Saved.done _) = ⊤
Success (Saved.needsInput _) = ⊥
Success Saved.needsRecovery = ⊥
Success (Saved.cancelled _) = ⊥

module Run (sizeMaximum : ℕ) (path : Path.Path) (environment : Connection.Environment)
  (decimalPort : ℕ → Text) (certificateBlocks : Text → List Text) (unix : Bool)
  (library : Library.Contract) (format : Encoding.Formatting)
  (prefixPostgres : Preparation.PostgreSQL library format)
  (bodyPostgres : Controls.PostgreSQL) (encoding : Backfill.JournalEncoding library) where
  module Operation = BackfillOperation.Registered library format prefixPostgres bodyPostgres encoding
  module Checked = Recovery.CheckedFor Operation.operation Success
  private
    module C = Configuration.Run
    module S configurationValue = Startup.Run (Config.Config.core configurationValue) environment decimalPort certificateBlocks unix
    module M = Migration.Runtime Text Text

  input : ℕ → Config.Config → Preparation.Input
  input token configurationValue = Preparation.input token (settings configurationValue)

  data Failure : Set where
    configurationFailure : Configuration.Failure → Failure
    startupFailure : (configurationValue : Config.Config) → S.Failure configurationValue → Failure
    outputFailure : Text → Failure

  data State : Set where
    loading : ℕ → Configuration.P.Script (Configuration.Failure ⊎ Config.Config) → State
    starting : ℕ → (configurationValue : Config.Config) → S.State configurationValue → State
    embedding : (token : ℕ) → (configurationValue : Config.Config) → S.Service configurationValue →
      (initial : Store.World) → Checked.RunState (input token configurationValue) initial → State
    printing : Summary → State
    finished : State
    failed : Failure → State

  data Event : Set where
    configuration : Configuration.P.Event → Event
    service : (configurationValue : Config.Config) → S.Event configurationValue → Event
    backfill : Operation.E.Event → Store.World → Event
    returned : Event
    output : Text ⊎ ⊤ → Event

  settle : ∀ {request initial} (active : Checked.Active request initial) reply →
    Checked.Active.remaining active ≡ Operation.E.done reply → Checked.RunState request initial
  settle active (Saved.done value) ended = Checked.finish active (Checked.done (Saved.done value) ended tt)
  settle active (Saved.needsInput _) ended = Checked.finish active Checked.retry
  settle active Saved.needsRecovery ended = Checked.finish active Checked.retry
  settle active (Saved.cancelled _) ended = Checked.finish active Checked.retry

  data Step (migrations : M.Inputs) : State → Event → State → Set where
    configReply : ∀ token effect next reply → Step migrations (loading token (Configuration.P.ask effect next))
      (configuration (effect , reply)) (loading token (next reply))
    badConfig : ∀ token error → Step migrations (loading token (Configuration.P.done (inj₁ error))) returned (failed (configurationFailure error))
    configLoaded : ∀ token configurationValue → Step migrations (loading token (Configuration.P.done (inj₂ configurationValue))) returned
      (starting token configurationValue (S.start configurationValue migrations))
    startup : ∀ token configurationValue before event after → S.Step configurationValue before event after →
      Step migrations (starting token configurationValue before) (service configurationValue event) (starting token configurationValue after)
    badService : ∀ token configurationValue error → Step migrations
      (starting token configurationValue (S.failed {configurationValue = configurationValue} error)) returned (failed (startupFailure configurationValue error))
    ready : ∀ token configurationValue service initial → Step migrations
      (starting token configurationValue (S.ready {configurationValue = configurationValue} service)) returned
      (embedding token configurationValue service initial (Checked.start (input token configurationValue) initial))
    observed : ∀ token configurationValue service initial (active : Checked.Active (input token configurationValue) initial)
      effect continuation reply after →
      (exposed : Checked.Active.remaining active ≡ Operation.E.ask effect continuation) →
      (physical : Operation.Atomic (Checked.History.current (Checked.Active.evidence active)) effect reply after) →
      Step migrations (embedding token configurationValue service initial (Checked.running active))
        (backfill (effect , reply) after)
        (embedding token configurationValue service initial (Checked.continue active effect continuation exposed reply after physical))
    settled : ∀ token configurationValue service initial (active : Checked.Active (input token configurationValue) initial) reply →
      (ended : Checked.Active.remaining active ≡ Operation.E.done reply) →
      Step migrations (embedding token configurationValue service initial (Checked.running active)) returned
        (embedding token configurationValue service initial (settle active reply ended))
    reported : ∀ token configurationValue service initial (completion : Checked.Terminal (input token configurationValue) initial) reply →
      Checked.Active.remaining (Checked.Terminal.active completion) ≡ Operation.E.done reply →
      Step migrations (embedding token configurationValue service initial (Checked.stopped completion)) returned
        (printing (summary token reply))
    printed : ∀ value → Step migrations (printing value) (output (inj₂ tt)) finished
    outputFailed : ∀ value error → Step migrations (printing value) (output (inj₁ error)) (failed (outputFailure error))

  start : ℕ → State
  start token = loading token (C.load path)

  -- The printed reply comes from the actual completed physical execution;
  -- even a needs-input/cancelled report retains the operation goal/frame.
  reportedMeetsGoal : ∀ token configurationValue initial (completion : Checked.Terminal (input token configurationValue) initial) reply →
    Checked.Active.remaining (Checked.Terminal.active completion) ≡ Operation.E.done reply →
    Operation.Goal (input token configurationValue) initial
      (Checked.History.current (Checked.Active.evidence (Checked.Terminal.active completion))) reply
  reportedMeetsGoal token configurationValue initial completion reply ended
    with Checked.Terminal.active completion | ended
  ... | Checked.activeState .(Operation.E.done reply) past | refl = Checked.finishedMeetsOriginalIntent past

  data Trace (migrations : M.Inputs) : State → List Event → State → Set where
    empty : ∀ state → Trace migrations state [] state
    more : ∀ before event middle events after → Step migrations before event middle → Trace migrations middle events after →
      Trace migrations before (event ∷ events) after

  exit : State → Maybe ℕ
  exit finished = just 0
  exit (failed _) = just 1
  exit _ = nothing
