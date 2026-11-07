{-# OPTIONS --safe #-}
-- The configured backend owns its cache across calls. Success exposes only
-- vectors produced by that backend's loading/batching/alignment protocol.
-- Binary32-to-Float widening and provider numeric conversion are standard
-- numeric dependencies; they are not Mimir policy or fresh axioms.
module Mimir.EmbeddingService where

open import Data.List using (List; []; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Data.Float.Base as Float
import Data.Vec as Vec
import Mimir.EmbeddingBackend as Backend
import Mimir.EmbeddingLifecycle as Lifecycle
import Mimir.RetrievalRanking as Ranking
import Mimir.ConfigurationValues as Config
import Mimir.ConfigurationPath as Path
import Mimir.ApplicationStore as Store
import Mimir.StructuredValue as JSON
import Mimir.Validation as Validation

module Run (float : Ranking.F32) (dimension maximumIndex : ℕ)
  (numeric : JSON.Value → Validation.Fault ⊎ Ranking.F32.Value float)
  (widen : Ranking.F32.Value float → Float.Float)
  (home : Maybe Path.NativePath) (withExtension : Path.Path → Text → Path.Path)
  (pid : Text) where
  private
    module L = Lifecycle.Local float
    module R = Lifecycle.Remote float dimension maximumIndex numeric

  data Failure : Set where
    disabled missingHome cancelled : Failure
    localFailure : Text → Failure
    remoteFailure : R.Failure → Failure

  Result = Failure ⊎ List Store.Vector

  vectors : ∀ {n} → List (Vec.Vec (Ranking.F32.Value float) n) → List Store.Vector
  vectors values = map (λ value → map widen (Vec.toList value)) values

  localResult : Text ⊎ List L.A.Vector → Result
  localResult (inj₁ error) = inj₁ (localFailure error)
  localResult (inj₂ values) = inj₂ (vectors values)

  remoteResult : R.Failure ⊎ List R.R.Vector → Result
  remoteResult (inj₁ error) = inj₁ (remoteFailure error)
  remoteResult (inj₂ values) = inj₂ (vectors values)

  key : Maybe Text → Text
  key nothing = []
  key (just value) = value

  data LocalTrace (base : Path.Path) (batchSize : ℕ) (texts : List Text) : L.State → L.State → Set where
    done : ∀ state → LocalTrace base batchSize texts state state
    step : ∀ before middle after → L.Step withExtension pid base batchSize texts before middle →
      LocalTrace base batchSize texts middle after → LocalTrace base batchSize texts before after

  data Call : Maybe Config.Embeddings → Backend.CacheState → List Text → Backend.CacheState → Result → Set where
    noBackend : ∀ cache texts → Call nothing cache texts cache (inj₁ disabled)
    localEmpty : ∀ cfg cache → Config.Embeddings.backend cfg ≡ Config.local →
      Call (just cfg) cache [] cache (inj₂ [])
    noHome : ∀ cfg first rest → Config.Embeddings.backend cfg ≡ Config.local →
      Lifecycle.root (Config.Embeddings.cacheDirectory cfg) home ≡ nothing →
      Call (just cfg) Backend.unloaded (Data.List._∷_ first rest) Backend.unloaded (inj₁ missingHome)
    reuseLocal : ∀ cfg texts base after result → Config.Embeddings.backend cfg ≡ Config.local →
      LocalTrace base (Config.Embeddings.batchSize cfg) texts (L.start Backend.ready texts) (L.returned after result) →
      Call (just cfg) Backend.ready texts after (localResult result)
    poisonedLocal : ∀ cfg texts base after result → Config.Embeddings.backend cfg ≡ Config.local →
      LocalTrace base (Config.Embeddings.batchSize cfg) texts (L.start Backend.poisoned texts) (L.returned after result) →
      Call (just cfg) Backend.poisoned texts after (localResult result)
    localCall : ∀ cfg cache texts base after result → Config.Embeddings.backend cfg ≡ Config.local →
      Lifecycle.root (Config.Embeddings.cacheDirectory cfg) home ≡ just base →
      LocalTrace base (Config.Embeddings.batchSize cfg) texts (L.start cache texts) (L.returned after result) →
      Call (just cfg) cache texts after (localResult result)
    localStopped : ∀ cfg cache texts base receipt → Config.Embeddings.backend cfg ≡ Config.local →
      LocalTrace base (Config.Embeddings.batchSize cfg) texts (L.start cache texts) (L.stopped receipt) →
      Call (just cfg) cache texts Backend.unloaded (inj₁ cancelled)
    remoteCall : ∀ cfg cache texts url events result →
      Backend.endpoint (Config.Embeddings.backend cfg) ≡ just url →
      R.P.Runs (R.run (Config.Embeddings.backend cfg) (key (Config.Embeddings.apiKey cfg))
        (Config.Embeddings.model cfg) texts) events result →
      Call (just cfg) cache texts cache (remoteResult result)

  remoteNeverChangesLocalCache : ∀ cfg cache texts url events result
    (endpoint : Backend.endpoint (Config.Embeddings.backend cfg) ≡ just url)
    (execution : R.P.Runs (R.run (Config.Embeddings.backend cfg) (key (Config.Embeddings.apiKey cfg))
      (Config.Embeddings.model cfg) texts) events result) →
    Call (just cfg) cache texts cache (remoteResult result)
  remoteNeverChangesLocalCache cfg cache texts url events result endpoint execution =
    remoteCall cfg cache texts url events result endpoint execution
