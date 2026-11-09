{-# OPTIONS --safe #-}
-- Explicit identity deletion uses the same advisory lock as learning writes.
-- Candidate retirement, detach, vector deletion and affected posterior updates
-- are one proposed publication. Historical observations are not rewritten.
module Mimir.GraphDeletion where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map; filterᵇ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (does)
open import Data.Empty using (⊥)
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
import Mimir.Recovery as Recovery
import Mimir.StructuredValue as Wire

data Kind : Set where belief patternNode : Kind

exists : Kind → ℕ → Store.World → Bool
exists belief id state with Ranking.lookup id (Store.beliefs state)
... | nothing = false
... | just _ = true
exists patternNode id state with Records.getPattern id (Store.patterns (Store.nodes state))
... | nothing = false
... | just _ = true

-- The outcome is stated on the complete application world. Retirement and
-- detaching references are part of removing this identity; experience history,
-- documents, vectors and every unrelated operation row survive.
module PatternRecovery where
  record Input : Set where
    constructor input
    field token identity : ℕ

  key : Input → Text
  key _ = toList "[\"store.delete_pattern\",null]"

  resultKey : Text
  resultKey = toList "@operation-result"

  distinct : ∀ request → key request ≡ resultKey → ⊥
  distinct request ()

  desired : Input → Store.World → Store.World
  desired request before with exists patternNode (Input.identity request) before
  ... | false = before
  ... | true = Store.removeNodes (Input.identity request ∷ []) true before

  answer : Input → Store.World → Wire.Value
  answer request before = Wire.object
    ((toList "deleted" , Wire.boolean (exists patternNode (Input.identity request) before)) ∷ [])

  apply : Input → Store.World → Store.World × Wire.Value
  apply request before = desired request before , answer request before

  preservesJournal : ∀ request before →
    Store.World.operations (desired request before) ≡ Store.World.operations before
  preservesJournal request before with exists patternNode (Input.identity request) before
  ... | false = refl
  ... | true = refl

  module Saved = Recovery.StoreFinalStep Input Input.token key resultKey distinct apply preservesJournal

  intended : Input → Store.World → Store.World
  intended request before with Store.lookupCancellation before (Input.token request)
  ... | just _ = before
  ... | nothing with Store.lookupSaved before (Input.token request) (key request)
    | Store.lookupSaved before (Input.token request) resultKey
  ... | nothing | nothing = Store.saveAnswer
    (Store.saveAnswer (desired request before) (Input.token request) (key request) (answer request before))
    (Input.token request) resultKey (answer request before)
  ... | just _ | just _ = before
  ... | just _ | nothing = before
  ... | nothing | just _ = before

  expectedReply : Input → Store.World → Saved.Result
  expectedReply request before with Store.lookupCancellation before (Input.token request)
  ... | just original = Saved.cancelled original
  ... | nothing with Store.lookupSaved before (Input.token request) (key request)
    | Store.lookupSaved before (Input.token request) resultKey
  ... | just saved | just _ = Saved.done saved
  ... | nothing | nothing = Saved.done (answer request before)
  ... | just _ | nothing = Saved.needsRecovery
  ... | nothing | just _ = Saved.needsRecovery

  intent : Saved.G.Intent Input
  intent = record { intended = intended; expectedReply = expectedReply }

  correct : ∀ request before → Saved.execute request before ≡
    Saved.G.expected intent (Saved.G.invocation request before)
  correct request before with Store.lookupCancellation before (Input.token request)
  ... | just _ = refl
  ... | nothing with Store.lookupSaved before (Input.token request) (key request)
    | Store.lookupSaved before (Input.token request) resultKey
  ... | just _ | just _ = refl
  ... | nothing | nothing = refl
  ... | just _ | nothing = refl
  ... | nothing | just _ = refl

  operation : Recovery.Recoverable Store.World Input
  operation = Saved.recoverable intent correct

  module Checked = Recovery.Recoverable operation

  Goal : Input → Store.World → Store.World → Saved.Result → Set
  Goal request initial final reply =
    (final , reply) ≡ (intended request initial , expectedReply request initial)

  certified : Recovery.RecoverableFor Store.World Input Saved.Result Goal
  certified = record
    { Effect = Checked.Effect; Reply = Checked.Reply; script = Checked.script
    ; Atomic = Checked.Atomic; converges = Checked.converges; progress = Checked.progress }

  module Run = Recovery.CheckedFor certified

  -- The generic interruption relation includes every prefix and a commit
  -- whose acknowledgement was lost. Both the state and original reply agree.
  retryReachesOriginalOutcome = Checked.converges

  bothOriginalAnswersReadable : ∀ request before →
    Store.lookupSaved before (Input.token request) (key request) ≡ nothing →
    Store.lookupSaved before (Input.token request) resultKey ≡ nothing →
    Store.lookupSaved (Saved.publication request before) (Input.token request) (key request) ≡
      just (answer request before) ×
    Store.lookupSaved (Saved.publication request before) (Input.token request) resultKey ≡
      just (answer request before)
  bothOriginalAnswersReadable request before stepAbsent resultAbsent =
    Saved.publishedStepReadable request before stepAbsent ,
    Saved.publishedResultReadable request before resultAbsent

  unrelatedTables : ∀ request before →
    (Store.World.chunks (desired request before) ,
     Store.World.beliefVectors (desired request before) ,
     Store.World.chunkVectors (desired request before) ,
     Store.World.history (desired request before) ,
     Store.World.embeddingOwners (desired request before)) ≡
    (Store.World.chunks before , Store.World.beliefVectors before ,
     Store.World.chunkVectors before , Store.World.history before , Store.World.embeddingOwners before)
  unrelatedTables request before with exists patternNode (Input.identity request) before
  ... | false = refl
  ... | true = refl

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
