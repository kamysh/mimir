{-# OPTIONS --safe #-}
-- Concrete database-read meanings for the retrieval machine. A fresh snapshot
-- is supplied per read; these contracts do not assert repeatable-read isolation.
module Mimir.RetrievalReadContract where

open import Data.List using (List; []; _∷_; concatMap)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)
open import Data.Maybe using (nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Data.Nat using (ℕ)
import Mimir.RetrievalProtocol as Protocol
import Mimir.RetrievalRanking as Ranking
import Mimir.GraphPaths as Paths
import Mimir.GraphRecords as Records
import Mimir.ApplicationStore as Store
import Mimir.LearningStore as Learning
import Mimir.ReviewPreparationPublication as Publication
import Mimir.LearningRecompute as Recompute
import Mimir.ReviewSchema as Review

retired : Store.World → List ℕ
retired state = Ranking.unique (concatMap Review.Review.superseded
  (Recompute.activeReviewsScoped nothing (Learning.identities learn) (Publication.World.ledger pub)))
  where learn = Store.World.learning state; pub = Learning.World.publication learn

ReadMeaning : (phase : Protocol.State) → Store.World → Protocol.Reply phase → Set
ReadMeaning (Protocol.overlay request) state (inj₁ error) = ⊤
ReadMeaning (Protocol.overlay request) state (inj₂ ids) = ids ↭ retired state
ReadMeaning (Protocol.beliefs request superseded) state (inj₁ error) = ⊤
ReadMeaning (Protocol.beliefs request superseded) state (inj₂ rows) = rows ↭
  Records.listBeliefs (Protocol.Request.project request) nothing (Store.beliefs state)
ReadMeaning (Protocol.closure context seed remaining) state (inj₁ error) = ⊤
ReadMeaning (Protocol.closure context seed remaining) state (inj₂ rows) =
  Paths.Returned (Paths.allDownstream seed) (Store.beliefs state)
    (Publication.World.edges (Learning.World.publication (Store.World.learning state))) rows
ReadMeaning (Protocol.neighbors context project seed remaining frontier next) state (inj₁ error) = ⊤
ReadMeaning (Protocol.neighbors context project seed remaining frontier next) state (inj₂ rows) =
  Paths.Returned (Paths.directScoped seed project) (Store.beliefs state)
    (Publication.World.edges (Learning.World.publication (Store.World.learning state))) rows
-- Model generation, pgvector approximate retrieval and terminal states have
-- their own external boundaries; this predicate does not purport to constrain
-- their replies. The machine still fixes query, filter, pool and failure use.
ReadMeaning (Protocol.embedding request superseded all token) state reply = ⊤
ReadMeaning (Protocol.vectorQuery request superseded all token vector) state reply = ⊤
ReadMeaning (Protocol.finished result) state reply = ⊤
ReadMeaning (Protocol.failed message) state reply = ⊤
