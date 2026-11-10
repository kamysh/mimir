{-# OPTIONS --safe #-}
-- Pure expectations retain complete selected beliefs, ordered evidence and
-- factual semantic-availability coverage from the existing retrieval intent.
module Mimir.IntendedRetrieval where

open import Data.Bool using (false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String; toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.ApplicationStore as Store
import Mimir.ConfigurationValues as Config
import Mimir.IntendedPreparation as Preparation
import Mimir.PreparedRetrieval as Prepared
import Mimir.PublicInput as Fields
import Mimir.PublicRequest as Public
import Mimir.PublicRetrievalRecovery as Search
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
  (database : Database.VectorOperations) (configuration : Config.Config) where
  module Base = Preparation.Evaluate library postgres
    using (Expected; expected; retrievalReadback; requestCorrection)
  module Decode = Public.Decode library
  module Business = Search.Run arithmetic unicode database configuration
    using (candidates; answer)

  Expected = Base.Expected Search.Response
  Evaluation = Preparation.ObservationError ⊎ Expected
  ProviderReply = Text ⊎ List Store.Vector

  record Observations : Set where
    field snapshotRead : Maybe ⊤
          embedding : Maybe ProviderReply

  missing : String → Preparation.ObservationError
  missing receiptField = Preparation.observationError (Validation.fault
    (Validation.key "observations" ∷ Validation.key receiptField ∷ []) Validation.missingField
    "Capture the actual acknowledged snapshot/provider receipt for this query and attempt. Do not invent a read, vector, semantic availability or expected ranked beliefs, or turn missing oracle input into a product correction.")

  returned : Search.Request → Store.World → Prepared.Preparation → Expected
  returned requested before preparation = Base.expected before (just answer) (Base.retrievalReadback answer)
    where answer = Business.answer requested before preparation

  prepared : Search.Request → Store.World → Observations → Evaluation
  prepared requested before observed with Business.candidates requested before
  ... | [] = inj₂ (returned requested before Prepared.unconfigured)
  ... | _ ∷ _ with Config.Config.embed configuration
  ... | nothing = inj₂ (returned requested before Prepared.unconfigured)
  ... | just configured with Observations.embedding observed
  ... | nothing = inj₁ (missing "query_embedding")
  ... | just response = inj₂ (returned requested before (Prepared.observed response))

  query : Search.Request → Store.World → Observations → Evaluation
  query requested before observed with Observations.snapshotRead observed
  ... | nothing = inj₁ (missing "snapshot_read")
  ... | just tt = prepared requested before observed

  request : Wire.Object.View → Validation.Fault ⊎ Search.Request
  request fields = Record._>>=_ (Fields.required "context" Wire.asString fields) λ context →
    Record._>>=_ (Public.memoryField (toList "prefer_type") fields) λ preference →
    Record._>>=_ (Decode.selection "limit" fields) λ selection →
    Record.mapResult (λ perBelief → Search.fromFields context selection (Decode.project fields) preference
      (Fields.loose "include_evidence" false Wire.asBoolean fields) perBelief)
      (Decode.selection "evidence_per_belief" fields)

  afterRequest : Validation.Fault ⊎ Search.Request → Store.World → Observations → Evaluation
  afterRequest (inj₁ fault) before observed = inj₂ (Base.expected before nothing (Base.requestCorrection fault))
  afterRequest (inj₂ requested) before observed = query requested before observed

  evaluate : Wire.Value → Store.World → Observations → Evaluation
  evaluate raw before observed with Decode.readInvocation Tools.queryRelevant raw
  ... | inj₁ fault = inj₂ (Base.expected before nothing (Base.requestCorrection fault))
  ... | inj₂ admitted = afterRequest
    (request (Wire.Object.normalize (Decode.Invocation.suppliedFields admitted))) before observed

  malformedRequestDoesNotEnterBody : ∀ raw before observed fault →
    Decode.readInvocation Tools.queryRelevant raw ≡ inj₁ fault →
    evaluate raw before observed ≡ inj₂ (Base.expected before nothing (Base.requestCorrection fault))
  malformedRequestDoesNotEnterBody raw before observed fault rejected rewrite rejected = refl

  noCandidatesNeedNoEmbedding : ∀ requested before observed → Business.candidates requested before ≡ [] →
    prepared requested before observed ≡ inj₂ (returned requested before Prepared.unconfigured)
  noCandidatesNeedNoEmbedding requested before observed absent rewrite absent = refl

  missingSnapshotIsOracleInputError : ∀ requested before observed → Observations.snapshotRead observed ≡ nothing →
    query requested before observed ≡ inj₁ (missing "snapshot_read")
  missingSnapshotIsOracleInputError requested before observed absent rewrite absent = refl

  KeepsWorld : Store.World → Evaluation → Set
  KeepsWorld before (inj₁ missingObservation) = ⊤
  KeepsWorld before (inj₂ result) = Base.Expected.world result ≡ before

  preparedKeepsWorld : ∀ requested before observed → KeepsWorld before (prepared requested before observed)
  preparedKeepsWorld requested before observed with Business.candidates requested before
  ... | [] = refl
  ... | _ ∷ _ with Config.Config.embed configuration
  ... | nothing = refl
  ... | just configured with Observations.embedding observed
  ... | nothing = tt
  ... | just response = refl

  queryKeepsWorld : ∀ requested before observed → KeepsWorld before (query requested before observed)
  queryKeepsWorld requested before observed with Observations.snapshotRead observed
  ... | nothing = tt
  ... | just tt = preparedKeepsWorld requested before observed

  afterRequestKeepsWorld : ∀ received before observed → KeepsWorld before (afterRequest received before observed)
  afterRequestKeepsWorld (inj₁ fault) before observed = refl
  afterRequestKeepsWorld (inj₂ requested) before observed = queryKeepsWorld requested before observed

  neverChangesWorld : ∀ raw before observed → KeepsWorld before (evaluate raw before observed)
  neverChangesWorld raw before observed with Decode.readInvocation Tools.queryRelevant raw
  ... | inj₁ fault = refl
  ... | inj₂ admitted = afterRequestKeepsWorld
    (request (Wire.Object.normalize (Decode.Invocation.suppliedFields admitted))) before observed
