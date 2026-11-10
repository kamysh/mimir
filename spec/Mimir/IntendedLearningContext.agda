{-# OPTIONS --safe #-}
-- Learning context is computed by its independent retrieval and assembly
-- functions; neither selected IDs nor desired assessments are oracle inputs.
module Mimir.IntendedLearningContext where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.ApplicationStore as Store
import Mimir.CandidateGraph as Graph
import Mimir.ConfigurationValues as Config
import Mimir.IntendedPreparation as Preparation
import Mimir.LearningContextProtocol as Protocol
import Mimir.PreparedRetrieval as Prepared
import Mimir.PublicInput as Fields
import Mimir.PublicLearningContextRecovery as Learning
import Mimir.PublicRequest as Public
import Mimir.PublicRetrievalRecovery as Retrieval
import Mimir.RecordDecoding as Record
import Mimir.RetrievalRanking as Ranking
import Mimir.StandardLibrary as Library
import Mimir.StorageReadBinding as Database
import Mimir.OperationControls as Controls
import Mimir.StructuredValue as Wire
import Mimir.Validation as Validation
import Mimir.ToolCatalog as Tools

module Evaluate (library : Library.Contract) (postgres : Controls.PostgreSQL)
  (arithmetic : Ranking.F32) (unicode : Ranking.Unicode)
  (database : Database.VectorOperations) (configuration : Config.Config)
  (textBefore : Text → Text → Bool) where
  module Base = Preparation.Evaluate library postgres using
    (Expected; PublicOutcome; expected; learningContextReadback;
     invalidContextAssessment; agentDecision; requestCorrection)
  module Decode = Public.Decode library
  module Search = Retrieval.Run arithmetic unicode database configuration using
    (Result; Receipt; completed; noCandidates; notConfigured; observed; preparation; candidates; answer)
  module Context = Learning.Run arithmetic unicode database configuration textBefore using
    (Result; needsInput; contextResult; attach; query; admitted)
  module Assembly = Protocol.Assembly unicode textBefore using (response; invalidAssessment)

  Expected = Base.Expected Context.Result
  Evaluation = Preparation.ObservationError ⊎ Expected
  ProviderReply = Text ⊎ List Store.Vector

  record Observations : Set where
    field snapshotRead : Maybe ⊤
          embedding : Maybe ProviderReply

  missing : String → Preparation.ObservationError
  missing receiptField = Preparation.observationError (Validation.fault
    (Validation.key "observations" ∷ Validation.key receiptField ∷ []) Validation.missingField
    "Capture the actual acknowledged snapshot/provider receipt for this learning-context query and attempt. Do not invent a read, vector, selected beliefs, procedures or assessment values, or report missing oracle input as a product correction.")

  outcome : Context.Result → Base.PublicOutcome
  outcome (Context.needsInput requested diagnostic) = Base.agentDecision diagnostic
  outcome (Context.contextResult source (Assembly.response value)) = Base.learningContextReadback value
  outcome (Context.contextResult source Assembly.invalidAssessment) = Base.invalidContextAssessment

  returned : Store.World → Context.Result → Expected
  returned before result = Base.expected before (just result) (outcome result)

  fromReceipt : ∀ requested before {cfg} → Search.Receipt cfg (Context.query requested) before → Expected
  fromReceipt requested before {cfg} receipt = returned before (Context.attach requested source)
    where
    source = Search.completed cfg (Context.query requested) before receipt
      (Search.answer (Context.query requested) before (Search.preparation receipt))

  preparedAt : ∀ requested before (found : List Graph.BeliefValues) →
    Search.candidates (Context.query requested) before ≡ found → Observations → Evaluation
  preparedAt requested before [] selected observed = inj₂ (fromReceipt requested before
    (Search.noCandidates (Config.Config.embed configuration) (Context.query requested) before selected))
  preparedAt requested before (_ ∷ _) selected observed with Config.Config.embed configuration
  ... | nothing = inj₂ (fromReceipt requested before (Search.notConfigured (Context.query requested) before))
  ... | just configured with Observations.embedding observed
  ... | nothing = inj₁ (missing "query_embedding")
  ... | just response = inj₂ (fromReceipt requested before (Search.observed configured (Context.query requested) before response))

  prepared : Learning.Request → Store.World → Observations → Evaluation
  prepared requested before observed = preparedAt requested before
    (Search.candidates (Context.query requested) before) refl observed

  query : Learning.Request → Store.World → Observations → Evaluation
  query requested before observed with Context.admitted requested
  ... | false = inj₂ (returned before (Context.needsInput requested Learning.projectCorrection))
  ... | true with Observations.snapshotRead observed
  ... | nothing = inj₁ (missing "snapshot_read")
  ... | just tt = prepared requested before observed

  request : Wire.Object.View → Validation.Fault ⊎ Learning.Request
  request fields = Record._>>=_ (Fields.required "context" Wire.asString fields) λ context →
    Record._>>=_ (Fields.required "project" Wire.asString fields) λ project →
    Record.mapResult (Learning.contextSearch context project) (Decode.selection "limit" fields)

  afterRequest : Validation.Fault ⊎ Learning.Request → Store.World → Observations → Evaluation
  afterRequest (inj₁ fault) before observed = inj₂ (Base.expected before nothing (Base.requestCorrection fault))
  afterRequest (inj₂ requested) before observed = query requested before observed

  evaluate : Wire.Value → Store.World → Observations → Evaluation
  evaluate raw before observed with Decode.readInvocation Tools.queryLearningContext raw
  ... | inj₁ fault = inj₂ (Base.expected before nothing (Base.requestCorrection fault))
  ... | inj₂ admitted = afterRequest
    (request (Wire.Object.normalize (Decode.Invocation.suppliedFields admitted))) before observed

  malformedRequestDoesNotEnterBody : ∀ raw before observed fault →
    Decode.readInvocation Tools.queryLearningContext raw ≡ inj₁ fault →
    evaluate raw before observed ≡ inj₂ (Base.expected before nothing (Base.requestCorrection fault))
  malformedRequestDoesNotEnterBody raw before observed fault rejected rewrite rejected = refl

  refusedProjectNeedsNoReceipts : ∀ requested before observed → Context.admitted requested ≡ false →
    query requested before observed ≡ inj₂ (returned before (Context.needsInput requested Learning.projectCorrection))
  refusedProjectNeedsNoReceipts requested before observed refused rewrite refused = refl

  missingSnapshotIsOracleInputError : ∀ requested before observed → Context.admitted requested ≡ true →
    Observations.snapshotRead observed ≡ nothing → query requested before observed ≡ inj₁ (missing "snapshot_read")
  missingSnapshotIsOracleInputError requested before observed allowed absent rewrite allowed | absent = refl

  KeepsWorld : Store.World → Evaluation → Set
  KeepsWorld before (inj₁ missingObservation) = ⊤
  KeepsWorld before (inj₂ result) = Base.Expected.world result ≡ before

  preparedAtKeepsWorld : ∀ requested before found selected observed →
    KeepsWorld before (preparedAt requested before found selected observed)
  preparedAtKeepsWorld requested before [] selected observed = refl
  preparedAtKeepsWorld requested before (_ ∷ _) selected observed with Config.Config.embed configuration
  ... | nothing = refl
  ... | just configured with Observations.embedding observed
  ... | nothing = tt
  ... | just response = refl

  preparedKeepsWorld : ∀ requested before observed → KeepsWorld before (prepared requested before observed)
  preparedKeepsWorld requested before observed = preparedAtKeepsWorld requested before
    (Search.candidates (Context.query requested) before) refl observed

  queryKeepsWorld : ∀ requested before observed → KeepsWorld before (query requested before observed)
  queryKeepsWorld requested before observed with Context.admitted requested
  ... | false = refl
  ... | true with Observations.snapshotRead observed
  ... | nothing = tt
  ... | just tt = preparedKeepsWorld requested before observed

  afterRequestKeepsWorld : ∀ received before observed → KeepsWorld before (afterRequest received before observed)
  afterRequestKeepsWorld (inj₁ fault) before observed = refl
  afterRequestKeepsWorld (inj₂ requested) before observed = queryKeepsWorld requested before observed

  neverChangesWorld : ∀ raw before observed → KeepsWorld before (evaluate raw before observed)
  neverChangesWorld raw before observed with Decode.readInvocation Tools.queryLearningContext raw
  ... | inj₁ fault = refl
  ... | inj₂ admitted = afterRequestKeepsWorld
    (request (Wire.Object.normalize (Decode.Invocation.suppliedFields admitted))) before observed
