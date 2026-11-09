{-# OPTIONS --safe #-}
-- Explicit identity deletion uses the same advisory lock as learning writes.
-- Candidate retirement, detach, vector deletion and affected posterior updates
-- are one proposed publication. Historical observations are not rewritten.
module Mimir.GraphDeletion where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map; filterᵇ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_)
open import Relation.Nullary using (does)
open import Mimir.Text using (Text)
import Mimir.ApplicationStore as Store
import Mimir.CandidateGraph as Graph
import Mimir.GraphRecords as Records
import Mimir.RetrievalRanking as Ranking
import Mimir.ReviewEdges as Edges
import Mimir.LearningRecompute as Recompute
import Mimir.PosteriorComputation as Posterior
import Mimir.LearningStore as Learning
import Mimir.ReviewPreparationPublication as Publication
import Mimir.LearningTransaction as Transaction

data Kind : Set where belief patternNode : Kind

exists : Kind → ℕ → Store.World → Bool
exists belief id state with Ranking.lookup id (Store.beliefs state)
... | nothing = false
... | just _ = true
exists patternNode id state with Records.getPattern id (Store.patterns (Store.nodes state))
... | nothing = false
... | just _ = true

children : ℕ → Store.World → List ℕ
children id state = Ranking.unique (map Edges.Edge.to
  (filterᵇ (λ e → does (id ≟ Edges.Edge.from e))
    (Publication.World.edges (Learning.World.publication (Store.World.learning state)))))

data Failure : Set where
  storageFailure : Text → Failure
  foreignTarget invalidNumericInput invalidNumericWrite : Failure

  numericalDecision : Posterior.State → List Posterior.State → Failure

module Operation (database : ℕ) (calculator : Posterior.Calculator) where
  module T = Transaction.Over Store.World Bool Failure database 671942183

  finish : Store.World → Recompute.Result → T.Decision
  finish state (Recompute.recomputed nodes warning) = T.replace (Store.setNodes nodes state) true
  finish state Recompute.foreignTarget = T.reject foreignTarget
  finish state Recompute.invalidNumericInput = T.reject invalidNumericInput
  finish state Recompute.invalidNumericWrite = T.reject invalidNumericWrite
  finish state (Recompute.needsDecision counts history) = T.reject (numericalDecision counts history)

  delete : Kind → ℕ → Store.World → T.Decision
  delete kind id state with exists kind id state
  ... | false = T.replay false
  ... | true with kind
  ...   | patternNode = T.replace (Store.removeNodes (id ∷ []) true state) true
  ...   | belief = finish proposed (Recompute.runGlobal calculator (children id state)
    (Store.nodes proposed) (Publication.World.edges pub)
    (Recompute.activeReviewsScoped nothing (Learning.identities learn) (Publication.World.ledger pub))
    (Store.groundingMasses proposed))
    where
    proposed = Store.removeBeliefVectors (id ∷ []) (Store.removeNodes (id ∷ []) true state)
    learn = Store.World.learning proposed
    pub = Learning.World.publication learn

  module Run (kind : Kind) (id : ℕ) where
    module P = T.Plan (delete kind id)
    module Laws = T.Laws (delete kind id)
    start = P.start

    lockBeforeMutation : T.Scoped T.outside start
    lockBeforeMutation = Laws.startScoped
