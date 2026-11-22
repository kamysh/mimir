{-# OPTIONS --safe #-}
-- Concrete paired document write set. Chunk deletion, vector deletion, new
-- chunks/vectors and removal of obsolete GROUNDS/CONTAINS associations publish
-- together. DocumentLoading adds recalculation for removed weighted evidence
-- to this structural write set before publication.
module Mimir.DocumentPublication where

open import Data.Bool using (Bool; true; false; not; _∨_)
open import Data.Bool.ListAction using (all)
open import Data.Float.Base using (Float; isNaN; isInfinite)
open import Data.List using (List; []; _∷_; _++_; map; filterᵇ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Vec using (Vec; toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
open import Relation.Nullary using (does)
import Mimir.ApplicationStore as Store
import Mimir.DocumentStore as Documents
import Mimir.EmbeddingBatch as Embeddings
import Mimir.CandidateRegistry as Registry
import Mimir.Validation as Validation
import Mimir.RetrievalRanking as Ranking
import Mimir.DatabaseTransaction as Database

module Publication (dimension : ℕ) where
  module D = Documents.Storage Float dimension
  module B = Embeddings.Batch Float dimension

  shape : List Store.Vector → Maybe (List D.Vector)
  shape [] = just []
  shape ([] ∷ vs) = nothing
  shape ((first ∷ rest) ∷ vs) with all (λ value → not (isNaN value ∨ isInfinite value)) (first ∷ rest)
  ... | false = nothing
  ... | true with B.shape dimension (first ∷ rest) | shape vs
  ...   | nothing | _ = nothing
  ...   | _ | nothing = nothing
  ...   | just shapedValue | just remaining = just (B.Shaped.vector shapedValue ∷ remaining)

  align : List Documents.Chunk → List Store.Vector → Maybe D.Store
  align chunks vectors with shape vectors
  ... | nothing = nothing
  ... | just shapedValue = D.align chunks shapedValue

  clear : Text → Store.World → Store.World
  clear path before = Store.removeChunkVectors ids (Store.removeChunks ids before)
    where ids = Store.documentIDs path before

  publish : Text → D.Store → Store.World → Store.World
  publish path entries before = record cleared
    { chunks = D.graphView entries ++ Store.World.chunks cleared
    ; chunkVectors = map (λ { (id , v) → id , toList v }) (D.vectorView entries) ++ Store.World.chunkVectors cleared }
    where cleared = clear path before

  indexRowsPreserveBeliefs : ∀ path entries before →
    Store.nodes (publish path entries before) ≡ Store.nodes before
  indexRowsPreserveBeliefs path entries before = refl

  clearingIndexRowsPreservesBeliefs : ∀ path before →
    Store.nodes (clear path before) ≡ Store.nodes before
  clearingIndexRowsPreservesBeliefs path before = refl

  data Plan : Set where
    invalidEmbeddingShape wrongDocument : Plan
    invalidIdentity : Validation.Fault → Plan
    replace : D.Store → Store.World → Plan

  -- A duplicated generated ID cannot be treated as an injective UUID oracle.
  -- Validate proposed chunk identities against retained chunks before writing.
  plan : Text → List Documents.Chunk → List Store.Vector → Store.World → Plan
  plan path chunks vectors before with align chunks vectors | all (λ chunk → does (Documents.Chunk.document chunk ≟Text path)) chunks
  ... | nothing | _ = invalidEmbeddingShape
  ... | just _ | false = wrongDocument
  ... | just entries | true with Registry.IDs.checkUnique (map Documents.Chunk.identity
    (Store.World.chunks (publish path entries before)))
  ...   | Validation.rejected failure invalid = invalidIdentity failure
  ...   | Validation.accepted valid = replace entries (publish path entries before)

  newPairIDsAgree : ∀ entries → map Documents.Chunk.identity (D.graphView entries) ≡ map proj₁ (D.vectorView entries)
  newPairIDsAgree = D.projectionsAgree

  -- Atomic publication is the database contract; a completed commit is reported.
  Published : Store.World → Store.World → Database.Receipt → Store.World → Set
  Published = Database.Atomic

  abortedKeepsOld : ∀ before proposed actual → Published before proposed Database.aborted actual → actual ≡ before
  abortedKeepsOld before proposed .before Database.abortedNone = refl
