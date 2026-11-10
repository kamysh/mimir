{-# OPTIONS --safe #-}
-- Query passages come from the independent stored-world selector. Provider
-- and read failures are observations, never desired vectors or result rows.
module Mimir.IntendedDocumentQuery where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.ApplicationStore as Store
import Mimir.ConfigurationValues as Config
import Mimir.DocumentQuery as Query
import Mimir.IntendedPreparation as Preparation
import Mimir.PublicDocumentQueryRecovery as Document
import Mimir.PublicInput as Fields
import Mimir.PublicRequest as Public
import Mimir.RecordDecoding as Record
import Mimir.StandardLibrary as Library
import Mimir.StorageReadBinding as Database
import Mimir.OperationControls as Controls
import Mimir.StructuredValue as Wire
import Mimir.ToolCatalog as Tools
import Mimir.Validation as Validation

module Evaluate (library : Library.Contract) (postgres : Controls.PostgreSQL)
  (database : Database.VectorOperations) (configuration : Config.Config) where
  module Base = Preparation.Evaluate library postgres
  module Decode = Public.Decode library
  module Business = Document.Run database configuration using (answer)

  Expected = Base.Expected Query.Result
  Evaluation = Preparation.ObservationError ⊎ Expected
  ProviderReply = Text ⊎ List Store.Vector

  -- These are the actual receipts for this configured query and attempt.
  -- A successful read uses the original consistent World; no second World,
  -- desired passages or computed answer can be supplied by the caller.
  record Observations : Set where
    field embedding : Maybe ProviderReply
          databaseRead : Maybe (Text ⊎ ⊤)

  missing : String → Preparation.ObservationError
  missing receiptField = Preparation.observationError (Validation.fault
    (Validation.key "observations" ∷ Validation.key receiptField ∷ []) Validation.missingField
    "Capture this query's actual configured provider/read receipt for the same attempt. Do not invent a vector, read success or expected passages, or turn missing test input into a product correction.")

  returned : Store.World → Query.Result → Expected
  returned before reply = Base.expected before (just reply) (Base.documentQueryReadback reply)

  read : Document.Request → Store.World → ProviderReply → Observations → Evaluation
  read requested before response observed with Observations.databaseRead observed
  ... | nothing = inj₁ (missing "database_read")
  ... | just (inj₁ failure) = inj₂ (returned before (Query.failed failure))
  ... | just (inj₂ tt) = inj₂ (returned before (Business.answer requested before response))

  prepare : Document.Request → Store.World → ProviderReply → Observations → Evaluation
  prepare requested before response observed with Query.prepare response
  ... | inj₁ issue = inj₂ (returned before (Query.preparationRequired issue))
  ... | inj₂ vector = read requested before response observed

  query : Document.Request → Store.World → Observations → Evaluation
  query requested before observed with Config.Config.embed configuration
  ... | nothing = inj₂ (returned before (Query.preparationRequired Query.notConfigured))
  ... | just configured with Observations.embedding observed
  ... | nothing = inj₁ (missing "query_embedding")
  ... | just response = prepare requested before response observed

  request : Wire.Object.View → Validation.Fault ⊎ Document.Request
  request fields = Record._>>=_ (Fields.required "context" Wire.asString fields) λ context →
    Record.mapResult (λ selection → Document.query context (Decode.project fields) selection)
      (Decode.selection "limit" fields)

  afterRequest : Validation.Fault ⊎ Document.Request → Store.World → Observations → Evaluation
  afterRequest (inj₁ fault) before observed = inj₂ (Base.expected before nothing (Base.requestCorrection fault))
  afterRequest (inj₂ requested) before observed = query requested before observed

  evaluate : Wire.Value → Store.World → Observations → Evaluation
  evaluate raw before observed with Decode.readInvocation Tools.queryDocument raw
  ... | inj₁ fault = inj₂ (Base.expected before nothing (Base.requestCorrection fault))
  ... | inj₂ admitted = afterRequest
    (request (Wire.Object.normalize (Decode.Invocation.suppliedFields admitted))) before observed

  malformedRequestDoesNotEnterBody : ∀ raw before observed fault →
    Decode.readInvocation Tools.queryDocument raw ≡ inj₁ fault →
    evaluate raw before observed ≡ inj₂ (Base.expected before nothing (Base.requestCorrection fault))
  malformedRequestDoesNotEnterBody raw before observed fault rejected rewrite rejected = refl

  noConfigurationNeedsNoReceipts : ∀ requested before observed →
    Config.Config.embed configuration ≡ nothing →
    query requested before observed ≡ inj₂ (returned before (Query.preparationRequired Query.notConfigured))
  noConfigurationNeedsNoReceipts requested before observed unconfigured rewrite unconfigured = refl

  refusedPreparationNeedsNoRead : ∀ requested before response observed issue →
    Query.prepare response ≡ inj₁ issue →
    prepare requested before response observed ≡ inj₂ (returned before (Query.preparationRequired issue))
  refusedPreparationNeedsNoRead requested before response observed issue refused rewrite refused = refl

  KeepsWorld : Store.World → Evaluation → Set
  KeepsWorld before (inj₁ missingObservation) = ⊤
  KeepsWorld before (inj₂ result) = Base.Expected.world result ≡ before

  readKeepsWorld : ∀ requested before response observed → KeepsWorld before (read requested before response observed)
  readKeepsWorld requested before response observed with Observations.databaseRead observed
  ... | nothing = tt
  ... | just (inj₁ failure) = refl
  ... | just (inj₂ tt) = refl

  prepareKeepsWorld : ∀ requested before response observed → KeepsWorld before (prepare requested before response observed)
  prepareKeepsWorld requested before response observed with Query.prepare response
  ... | inj₁ issue = refl
  ... | inj₂ vector = readKeepsWorld requested before response observed

  queryKeepsWorld : ∀ requested before observed → KeepsWorld before (query requested before observed)
  queryKeepsWorld requested before observed with Config.Config.embed configuration
  ... | nothing = refl
  ... | just configured with Observations.embedding observed
  ... | nothing = tt
  ... | just response = prepareKeepsWorld requested before response observed

  afterRequestKeepsWorld : ∀ received before observed → KeepsWorld before (afterRequest received before observed)
  afterRequestKeepsWorld (inj₁ fault) before observed = refl
  afterRequestKeepsWorld (inj₂ requested) before observed = queryKeepsWorld requested before observed

  neverChangesWorld : ∀ raw before observed → KeepsWorld before (evaluate raw before observed)
  neverChangesWorld raw before observed with Decode.readInvocation Tools.queryDocument raw
  ... | inj₁ fault = refl
  ... | inj₂ admitted = afterRequestKeepsWorld
    (request (Wire.Object.normalize (Decode.Invocation.suppliedFields admitted))) before observed
