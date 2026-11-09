{-# OPTIONS --safe #-}
-- Belief insertion/backfill connects configured backend calls, physical vector
-- writes, actual graph reads and automatic grounding. A backend error retains
-- its resulting cache state; prior acknowledged database writes are retained.
module Mimir.BeliefEmbeddingStorage where

open import Data.Float.Base using (Float; _-_)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)
open import Data.Maybe using (Maybe; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; trans; sym)
open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Mimir.Text using (Text)
import Mimir.EmbeddingBackend as Backend
import Mimir.EmbeddingService as Embedding
import Mimir.BeliefEmbedding as B
import Mimir.ConfigurationValues as Config
import Mimir.ConfigurationPath as Path
import Mimir.RetrievalRanking as Ranking
import Mimir.StructuredValue as JSON
import Mimir.Validation as Validation
import Mimir.ApplicationStore as Store
import Mimir.StorageSemantics as Semantics
import Mimir.StorageReadBinding as Read
import Mimir.GraphRecords as Records
import Mimir.DatabaseReadCommitted as Committed
import Mimir.DatabaseTransaction as DB
import Mimir.McpErrors as Errors
import Mimir.EmbeddingLifecycle as Lifecycle
import Mimir.CandidateGraph as G
import Mimir.PosteriorComputation as Posterior

module Bound (database maximumIndex : ℕ) (calculator : Posterior.Calculator) (float : Ranking.F32)
  (numeric : JSON.Value → Validation.Fault ⊎ Ranking.F32.Value float)
  (widen : Ranking.F32.Value float → Float)
  (home : Maybe Path.NativePath) (withExtension : Path.Path → Text → Path.Path) (pid : Text)
  (configured : Maybe Config.Embeddings) (ops : Read.VectorOperations)
  (reads : Committed.Contract Store.World) where
  private
    module E = Embedding.Run float 768 maximumIndex numeric widen home withExtension pid
    module R = Committed.Contract reads
    module Vectors = Read.Vectors ops
    module Atomic = B.Atomic database calculator

  module WithErrors (display : E.Failure → Text) where
    result : E.Result → Text ⊎ List Store.Vector
    result (inj₁ error) = inj₁ (display error)
    result (inj₂ vectors) = inj₂ vectors

    -- The acknowledged subscription precedes the initial database read.
    -- Its external handle is an observation, not an invented owner identity.
    record SubscribedRead : Set where
      constructor subscribedRead
      field subscription : ℕ
            events : List B.OwnerSubscription.E.Event
            acknowledged : B.OwnerSubscription.E.Runs (B.OwnerSubscription.start database)
              events (inj₂ subscription)
            observation : R.Read

    record Active (belief : G.BeliefValues) (read : SubscribedRead) : Set where
      field
        present : B.ownsPreparation belief
          (Store.World.embeddingOwners (R.snapshot (SubscribedRead.observation read))) ≡ true

    missingOwnerCannotStart : ∀ belief read → B.ownsPreparation belief
      (Store.World.embeddingOwners (R.snapshot (SubscribedRead.observation read))) ≡ false →
      Active belief read → ⊥
    missingOwnerCannotStart belief read missing active
      with Relation.Binary.PropositionalEquality.trans
        (Relation.Binary.PropositionalEquality.sym (Active.present active)) missing
    ... | ()

    record BackfillActive (belief : G.BeliefValues) (read : SubscribedRead) : Set where
      field present : B.ownsBackfill belief (R.snapshot (SubscribedRead.observation read)) ≡ true

    missingBackfillCannotStart : ∀ belief read →
      B.ownsBackfill belief (R.snapshot (SubscribedRead.observation read)) ≡ false →
      BackfillActive belief read → ⊥
    missingBackfillCannotStart belief read missing active
      with trans (sym (BackfillActive.present active)) missing
    ... | ()

    data Receipt : Backend.CacheState → (effect : B.Effect) → B.Reply effect → Backend.CacheState → Set where
      embedded : ∀ before belief read after reply → BackfillActive belief read →
        E.Call configured before (G.BeliefValues.content belief ∷ []) after reply →
        Receipt before (B.backfillEmbedding belief) (result reply) after
      backfillRevoked : ∀ before belief read stopped observation reply → BackfillActive belief read →
        B.ownsBackfill belief (R.snapshot observation) ≡ false →
        E.Call configured before (G.BeliefValues.content belief ∷ []) stopped (inj₁ E.cancelled) →
        Receipt before (B.backfillEmbedding belief) (inj₁ reply) stopped
      backfillMissing : ∀ cache belief read reply →
        B.ownsBackfill belief (R.snapshot (SubscribedRead.observation read)) ≡ false →
        Receipt cache (B.backfillEmbedding belief) (inj₁ reply) cache
      backfillSubscriptionFailed : ∀ cache belief events error →
        B.OwnerSubscription.E.Runs (B.OwnerSubscription.start database) events (inj₁ error) →
        Receipt cache (B.backfillEmbedding belief) (inj₁ error) cache
      preparedEmbedding : ∀ before belief read after reply → Active belief read →
        E.Call configured before (G.BeliefValues.content belief ∷ []) after reply →
        Receipt before (B.prepareEmbedding belief) (result reply) after
      preparationRevoked : ∀ before belief read stopped observation reply → Active belief read →
        B.ownsPreparation belief (Store.World.embeddingOwners (R.snapshot observation)) ≡ false →
        E.Call configured before (G.BeliefValues.content belief ∷ []) stopped (inj₁ E.cancelled) →
        Receipt before (B.prepareEmbedding belief) (inj₁ reply) stopped
      subscriptionFailed : ∀ cache belief events error →
        B.OwnerSubscription.E.Runs (B.OwnerSubscription.start database) events (inj₁ error) →
        Receipt cache (B.prepareEmbedding belief) (inj₁ error) cache
      written : ∀ cache id vector before after →
        Semantics.StatementPublication (Semantics.beliefVector id vector) before DB.committed after →
        Receipt cache (B.upsert id vector) (inj₂ tt) cache
      supported : ∀ cache belief vector observation ids
        (selected : Vectors.Selected vector nothing nothing (Store.World.chunkVectors (R.snapshot observation)) ids) →
        Receipt cache (B.supportingPassages belief vector)
          (B.selectSupport belief (R.snapshot observation) (map
            (λ row → proj₁ row , 1.0 - Read.VectorOperations.cosineDistance ops vector (Data.Product.proj₂ row))
            (Vectors.Selected.sorted selected))) cache
      published : ∀ cache belief origin prepared before proposed after value events →
        Atomic.intended belief origin prepared before ≡ Atomic.T.replace proposed value →
        DB.Atomic before proposed DB.committed after →
        Atomic.T.E.Runs (Atomic.Run.Execution.start belief origin prepared) events (Atomic.T.applied value) →
        Receipt cache (B.publishPrepared belief origin prepared) (inj₂ (inj₂ value)) cache
      publicationRefused : ∀ cache belief origin prepared before after reason cleanup events
        (report : Errors.AgentCorrection.Certified Store.World before after) →
        Atomic.intended belief origin prepared before ≡ Atomic.T.reject reason →
        Atomic.T.E.Runs (Atomic.Run.Execution.start belief origin prepared) events (Atomic.T.refused reason cleanup) →
        Receipt cache (B.publishPrepared belief origin prepared)
          (inj₂ (inj₁ (Errors.AgentCorrection.Certified.report report))) cache
      supportFailed : ∀ cache belief vector error → Receipt cache (B.supportingPassages belief vector) (inj₁ error) cache
      publicationFailed : ∀ cache belief origin prepared error → Receipt cache (B.publishPrepared belief origin prepared) (inj₁ error) cache
      beliefs : ∀ cache observation → Receipt cache B.listBeliefs
        (inj₂ (Records.listBeliefs nothing nothing (Store.beliefs (R.snapshot observation)))) cache
      existing : ∀ cache observation ids → ids ↭ map proj₁ (Store.World.beliefVectors (R.snapshot observation)) →
        Receipt cache B.embeddedIDs (inj₂ ids) cache
      progress : ∀ cache belief reply → Receipt cache (B.progress belief) reply cache
      writeFailed : ∀ cache id vector error → Receipt cache (B.upsert id vector) (inj₁ error) cache
      beliefsFailed : ∀ cache error → Receipt cache B.listBeliefs (inj₁ error) cache
      existingFailed : ∀ cache error → Receipt cache B.embeddedIDs (inj₁ error) cache

    data Runs {A : Set} : Backend.CacheState → B.E.Script A → List B.E.Event → Backend.CacheState → A → Set where
      returned : ∀ cache value → Runs cache (B.E.done value) [] cache value
      replied : ∀ before effect next reply middle events after value → Receipt before effect reply middle →
        Runs middle (next reply) events after value → Runs before (B.E.ask effect next) ((effect , reply) ∷ events) after value
