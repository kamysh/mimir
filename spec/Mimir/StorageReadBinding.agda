{-# OPTIONS --safe #-}
-- Bind read effects to the selected table/graph view at each READ COMMITTED
-- statement. Pgvector cosine evaluation and PostgreSQL float ordering are
-- dependency operations; Mimir owns filtering, the selected table and LIMIT.
module Mimir.StorageReadBinding where

open import Data.Bool using (Bool; true)
open import Data.Float.Base using (Float)
open import Data.List using (List; []; _∷_; map; filterᵇ)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; trans)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.ApplicationStore as Store
import Mimir.DocumentStore as Documents
import Mimir.RetrievalRanking as Ranking
import Mimir.RetrievalProtocol as Retrieval
import Mimir.RetrievalReadContract as RetrievalReads
import Mimir.DocumentQuery as Query
import Mimir.EvidenceRead as Evidence
import Mimir.StorageSemantics as Semantics
import Mimir.GraphReadProtocol as Graph
import Mimir.GraphRecords as Records
import Mimir.InferenceProtocol as Inference
import Mimir.DatabaseReadCommitted as Committed

eligibleVectors : Maybe (List ℕ) → List (ℕ × Store.Vector) → List (ℕ × Store.Vector)
eligibleVectors nothing rows = rows
eligibleVectors (just ids) rows = filterᵇ (λ row → Ranking.member (proj₁ row) ids) rows

record VectorOperations : Set where
  field cosineDistance : Store.Vector → Store.Vector → Float
        databaseLessEqual : Float → Float → Bool

module Vectors (ops : VectorOperations) where
  data Ordered (query : Store.Vector) : List (ℕ × Store.Vector) → Set where
    empty : Ordered query []
    one : ∀ row → Ordered query (row ∷ [])
    more : ∀ first second rest →
      VectorOperations.databaseLessEqual ops
        (VectorOperations.cosineDistance ops query (proj₂ first))
        (VectorOperations.cosineDistance ops query (proj₂ second)) ≡ true →
      Ordered query (second ∷ rest) → Ordered query (first ∷ second ∷ rest)

  -- Equal-distance rows may appear in either order. IDs are SQL table keys;
  -- absent graph endpoints are not prefiltered by vector-only SQL statements.
  record Selected (query : Store.Vector) (limit : Ranking.Selection) (filter : Maybe (List ℕ))
    (rows : List (ℕ × Store.Vector)) (result : List ℕ) : Set where
    field sorted : List (ℕ × Store.Vector)
          complete : sorted ↭ eligibleVectors filter rows
          ordered : Ordered query sorted
          capped : result ≡ Ranking.cap limit (map proj₁ sorted)

projectChunks : Text → Store.World → List ℕ
projectChunks project snapshot = map Documents.Chunk.identity
  (filterᵇ (λ chunk → same (Documents.Chunk.project chunk)) (Store.World.chunks snapshot))
  where
  same : Maybe Text → Bool
  same nothing = Data.Bool.false
  same (just actual) = does (actual ≟Text project)

evidenceGrounds : List ℕ → Store.World → List Store.Ground
evidenceGrounds ids snapshot = filterᵇ (λ ground → Ranking.member (Store.Ground.belief ground) ids)
  (Semantics.groundRows snapshot)

EvidenceMeaning : Store.World → (effect : Evidence.Effect) → Evidence.Reply effect → Set
EvidenceMeaning snapshot (Evidence.readGrounds ids) (inj₁ error) = ⊤
EvidenceMeaning snapshot (Evidence.readGrounds ids) (inj₂ rows) = rows ↭ evidenceGrounds ids snapshot
EvidenceMeaning snapshot (Evidence.readChunk id) (inj₁ error) = ⊤
EvidenceMeaning snapshot (Evidence.readChunk id) (inj₂ row) = row ≡ Store.chunk id (Store.World.chunks snapshot)
EvidenceMeaning snapshot (Evidence.openSnapshot belief) (inj₁ error) = ⊤
EvidenceMeaning snapshot (Evidence.openSnapshot belief) (inj₂ (tx , first , rows)) =
  first ≡ snapshot × rows ↭ evidenceGrounds (belief ∷ []) snapshot
EvidenceMeaning snapshot (Evidence.readSnapshotChunk tx first id) (inj₁ error) = ⊤
EvidenceMeaning snapshot (Evidence.readSnapshotChunk tx first id) (inj₂ row) =
  snapshot ≡ first × row ≡ Store.chunk id (Store.World.chunks snapshot)
EvidenceMeaning snapshot (Evidence.closeSnapshot tx) reply = ⊤

module Read (ops : VectorOperations) where
  module V = Vectors ops

  data DocumentMeaning (snapshot : Store.World) : (effect : Query.Effect) → Query.Reply effect → Set where
    project : ∀ project rows → rows ↭ projectChunks project snapshot →
      DocumentMeaning snapshot (Query.projectChunkIDs project) (inj₂ rows)
    projectFailed : ∀ project error → DocumentMeaning snapshot (Query.projectChunkIDs project) (inj₁ error)
    vectors : ∀ query limit filter ids → V.Selected query limit filter (Store.World.chunkVectors snapshot) ids →
      DocumentMeaning snapshot (Query.queryVectors query limit filter) (inj₂ ids)
    vectorsFailed : ∀ query limit filter error → DocumentMeaning snapshot (Query.queryVectors query limit filter) (inj₁ error)
    chunk : ∀ id → DocumentMeaning snapshot (Query.getChunk id) (inj₂ (Store.chunk id (Store.World.chunks snapshot)))
    chunkFailed : ∀ id error → DocumentMeaning snapshot (Query.getChunk id) (inj₁ error)

  RetrievalMeaning : (state : Retrieval.State) → Store.World → Retrieval.Reply state → Set
  RetrievalMeaning state@(Retrieval.vectorQuery requestValue retired beliefs token vector) snapshot (inj₁ error) = ⊤
  RetrievalMeaning state@(Retrieval.vectorQuery requestValue retired beliefs token vector) snapshot (inj₂ ids)
    with Retrieval.command state
  ... | just (Retrieval.queryVector query limit filter) = V.Selected query limit filter (Store.World.beliefVectors snapshot) ids
  ... | _ = Data.Empty.⊥
    where import Data.Empty
  RetrievalMeaning state snapshot reply = RetrievalReads.ReadMeaning state snapshot reply

-- A distinct event is retained for each observed database effect. Ordinary
-- reads do not imply one session-wide snapshot. Page reads explicitly start a
-- read-only REPEATABLE READ transaction: the second SELECT sees the first
-- SELECT's snapshot, under PostgreSQL's external isolation contract.
module Observed (reads : Committed.Contract Store.World) where
  open Committed.Contract reads

  GraphReply : (effect : Graph.Effect) → Graph.Reply effect → Set
  GraphReply (Graph.select handle statement) (inj₁ error) = ⊤
  GraphReply (Graph.select handle statement) (inj₂ observedWorld) = Σ Read (λ read → observedWorld ≡ snapshot read)
  GraphReply Graph.beginRead reply = ⊤
  GraphReply (Graph.openPage project memory) (inj₁ error) = ⊤
  GraphReply (Graph.openPage project memory) (inj₂ (tx , first)) = Σ Read (λ read → first ≡ snapshot read)
  GraphReply (Graph.pageSnapshotRows tx first project memory limit offset) (inj₁ error) = ⊤
  GraphReply (Graph.pageSnapshotRows tx first project memory limit offset) (inj₂ second) = second ≡ first
  GraphReply (Graph.dropTransaction tx) reply = ⊤

  pageReplyUsesItsOriginalSnapshot : ∀ tx first second project memory limit offset →
    GraphReply (Graph.pageSnapshotRows tx first project memory limit offset) (inj₂ second) →
    Records.pageResult project memory limit offset
      (Data.List.length (Records.listBeliefs project memory (Store.beliefs first))) (Store.beliefs second) ≡
    Graph.pageAnswer project memory limit offset first
  pageReplyUsesItsOriginalSnapshot tx first second project memory limit offset stable =
    Graph.pageUsesCountSnapshot project memory limit offset first second stable

  EvidenceReply : (effect : Evidence.Effect) → Evidence.Reply effect → Set
  EvidenceReply (Evidence.readGrounds ids) (inj₁ error) = ⊤
  EvidenceReply (Evidence.readChunk id) (inj₁ error) = ⊤
  EvidenceReply (Evidence.openSnapshot belief) (inj₁ error) = ⊤
  EvidenceReply (Evidence.readSnapshotChunk tx first id) (inj₁ error) = ⊤
  EvidenceReply (Evidence.closeSnapshot tx) reply = ⊤
  EvidenceReply effect reply = Σ Read (λ read → EvidenceMeaning (snapshot read) effect reply)

  passageUsesSelectedSnapshot : ∀ tx first id row →
    EvidenceReply (Evidence.readSnapshotChunk tx first id) (inj₂ row) →
    row ≡ Store.chunk id (Store.World.chunks first)
  passageUsesSelectedSnapshot tx first id row (read , stable , selected) =
    trans selected (cong (λ world → Store.chunk id (Store.World.chunks world)) stable)

  SuccessfulInferenceReply : (databaseSum : List Float → Float) → (effect : Inference.Effect) → Inference.Reply effect → Set
  SuccessfulInferenceReply databaseSum effect reply = Σ Read (λ read → Semantics.InferenceRead databaseSum (snapshot read) effect reply)
