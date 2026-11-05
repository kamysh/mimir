{-# OPTIONS --safe #-}
-- Concrete paired document write set. Chunk deletion, vector deletion, new
-- chunks/vectors and removal of obsolete GROUNDS/CONTAINS associations publish
-- together. This preserves DocumentStore's existing atomicity requirement;
-- the current sequential Rust loader does not yet refine this contract.
module Mimir.DocumentPublication where

open import Data.Bool using (Bool; true; false; not)
open import Data.Float.Base using (Float)
open import Data.List using (List; []; _∷_; _++_; map; filterᵇ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Vec using (Vec; toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
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
  shape (v ∷ vs) with B.shape dimension v | shape vs
  ... | nothing | _ = nothing
  ... | _ | nothing = nothing
  ... | just shaped | just rest = just (B.Shaped.vector shaped ∷ rest)

  align : List Documents.Chunk → List Store.Vector → Maybe D.Store
  align chunks vectors with shape vectors
  ... | nothing = nothing
  ... | just shaped = D.align chunks shaped

  clear : Text → Store.World → Store.World
  clear path before = Store.removeChunkVectors ids (Store.removeChunks ids before)
    where ids = Store.documentIDs path before

  publish : Text → D.Store → Store.World → Store.World
  publish path entries before = record cleared
    { chunks = D.graphView entries ++ Store.World.chunks cleared
    ; chunkVectors = map (λ { (id , v) → id , toList v }) (D.vectorView entries) ++ Store.World.chunkVectors cleared }
    where cleared = clear path before

  data Plan : Set where
    invalidEmbeddingShape : Plan
    invalidIdentity : Validation.Fault → Plan
    replace : D.Store → Store.World → Plan

  -- A duplicated generated ID cannot be treated as an injective UUID oracle.
  -- Validate proposed chunk identities against retained chunks before writing.
  plan : Text → List Documents.Chunk → List Store.Vector → Store.World → Plan
  plan path chunks vectors before with align chunks vectors
  ... | nothing = invalidEmbeddingShape
  ... | just entries with Registry.IDs.checkUnique (map Documents.Chunk.identity
    (Store.World.chunks (publish path entries before)))
  ...   | Validation.rejected failure invalid = invalidIdentity failure
  ...   | Validation.accepted valid = replace entries (publish path entries before)

  newPairIDsAgree : ∀ entries → map Documents.Chunk.identity (D.graphView entries) ≡ map proj₁ (D.vectorView entries)
  newPairIDsAgree = D.projectionsAgree

  -- Atomic publication is the approved database contract, not an assertion that
  -- a lost commit acknowledgement proves rollback or that SQL is already correct.
  Published : Store.World → Store.World → Database.Receipt → Store.World → Set
  Published = Database.Atomic

  abortedKeepsOld : ∀ before proposed actual → Published before proposed Database.aborted actual → actual ≡ before
  abortedKeepsOld before proposed .before Database.abortedNone = refl
