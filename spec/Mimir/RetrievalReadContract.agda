{-# OPTIONS --safe #-}
-- Concrete database-read meanings. One fresh snapshot is supplied per batch;
-- later consumption of its results does not perform a new database read.
module Mimir.RetrievalReadContract where

open import Data.List using (List; []; _∷_; concatMap)
open import Data.List using (map)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)
open import Data.Maybe using (nothing; just)
open import Data.Product using (_×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)
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
ReadMeaning (Protocol.overlay requestValue) state (inj₁ error) = ⊤
ReadMeaning (Protocol.overlay requestValue) state (inj₂ ids) = ids ↭ retired state
ReadMeaning (Protocol.beliefs requestValue superseded) state (inj₁ error) = ⊤
ReadMeaning (Protocol.beliefs requestValue superseded) state (inj₂ rows) = rows ↭
  Records.listBeliefs (Protocol.Request.project requestValue) nothing (Store.beliefs state)
ReadMeaning (Protocol.closure retrievalContext seed remaining) state (inj₁ error) = ⊤
ReadMeaning (Protocol.closure retrievalContext seed remaining) state (inj₂ rows) =
  Paths.Returned (Paths.allDownstream seed) (Store.beliefs state)
    (Publication.World.edges (Learning.World.publication (Store.World.learning state))) rows
ReadMeaning (Protocol.prefetch retrievalContext project ids) state (inj₁ error) = ⊤
ReadMeaning (Protocol.prefetch retrievalContext project ids) state (inj₂ rows) =
  (map proj₁ rows ≡ ids) × All (λ pair → Paths.Returned
    (Paths.directScoped (proj₁ pair) project) (Store.beliefs state)
    (Publication.World.edges (Learning.World.publication (Store.World.learning state))) (proj₂ pair)) rows
ReadMeaning (Protocol.neighbors retrievalContext project seed remaining frontier next) state (inj₁ error) = ⊤
ReadMeaning (Protocol.neighbors retrievalContext project seed remaining frontier next) state (inj₂ rows)
  with Protocol.lookup seed (Protocol.Context.cached retrievalContext)
... | just cached = rows ≡ cached
... | nothing = Paths.Returned (Paths.directScoped seed project) (Store.beliefs state)
    (Publication.World.edges (Learning.World.publication (Store.World.learning state))) rows
-- Model generation, pgvector approximate retrieval and terminal states have
-- their own external boundaries; this predicate does not purport to constrain
-- their replies. The machine still fixes query, filter, pool and failure use.
ReadMeaning (Protocol.embedding requestValue superseded all token) state reply = ⊤
ReadMeaning (Protocol.vectorQuery requestValue superseded all token vector) state reply = ⊤
ReadMeaning (Protocol.finished result) state reply = ⊤
ReadMeaning (Protocol.failed message) state reply = ⊤
