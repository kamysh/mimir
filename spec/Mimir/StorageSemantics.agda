{-# OPTIONS --safe #-}
-- Physical meanings of service effects. READ COMMITTED supplies the snapshot
-- for each statement; these definitions supply Mimir's selection/write set.
-- External errors remain possible and never serve as successful receipts.
module Mimir.StorageSemantics where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Float.Base using (Float; _+_; _*_)
open import Data.List using (List; []; _∷_; map; filterᵇ; foldl)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_)
open import Data.Integer using (ℤ)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Nullary using (does; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.ApplicationStore as Store
import Mimir.LearningStore as Learning
import Mimir.ReviewPreparationPublication as Publication
import Mimir.CandidateGraph as Graph
import Mimir.ReviewEdges as Edge
import Mimir.ReviewSchema as Review
import Mimir.GraphWrites as Write
import Mimir.GraphRecords as Records
import Mimir.GraphPaths as Paths
import Mimir.GraphNumerics as Numeric
import Mimir.InferenceProtocol as Inference
import Mimir.LearningRecompute as Recompute
import Mimir.PosteriorComputation as Posterior
import Mimir.ApplicationFloat as FloatValue
import Mimir.RetrievalRanking as Ranking
import Mimir.BeliefEmbedding as Embedding
import Mimir.IndependentProvenance as Origin
import Mimir.GroundingPublication as Ground
import Mimir.GraphDeletion as Deletion
import Mimir.DatabaseTransaction as DB
import Mimir.EvidenceValidity as Evidence
open import Data.List.Relation.Unary.All using (All)

edges : Store.World → List Edge.Edge
edges state = Publication.World.edges (Learning.World.publication (Store.World.learning state))

activeReviews : Store.World → List Review.Review
activeReviews state = Recompute.activeReviewsScoped nothing (Learning.identities learning)
  (Publication.World.ledger (Learning.World.publication learning))
  where learning = Store.learningView state

-- Only graph-live endpoints participate in MATCH. Legacy dangling references
-- can be represented in World but cannot become evidence of a successful join.
liveGround : Store.World → Store.Ground → Bool
liveGround state groundRow with Store.chunk (Store.Ground.chunk groundRow) (Store.World.chunks state)
  | Ranking.lookup (Store.Ground.belief groundRow) (Store.beliefs state)
... | just _ | just _ = true
... | _ | _ = false

groundRows : Store.World → List Store.Ground
groundRows state = filterᵇ (liveGround state) (Store.World.grounds state)

-- PostgreSQL/AGE sum is the dependency boundary. Mimir multiplies its result
-- by EVIDENCE_MASS_K=1 and maps exactly the joined, grouped belief identities.
groundTotals : (List Float → Float) → Store.World → List (ℕ × Float)
groundTotals databaseSum state = map total ids
  where
  rows = groundRows state
  ids = Ranking.unique (map Store.Ground.belief rows)
  total : ℕ → ℕ × Float
  total id = id , databaseSum (map Store.Ground.weight
    (filterᵇ (λ row → does (id ≟ Store.Ground.belief row)) rows)) * 1.0

incoming : List ℕ → Store.World → Maybe (List Inference.Incoming)
incoming ids state = go (edges state)
  where
  go : List Edge.Edge → Maybe (List Inference.Incoming)
  go [] = just []
  go (edgeRow ∷ rest) with Ranking.member (Edge.Edge.to edgeRow) ids
  ... | false = go rest
  ... | true with Ranking.lookup (Edge.Edge.from edgeRow) (Store.beliefs state)
    | Ranking.lookup (Edge.Edge.to edgeRow) (Store.beliefs state)
  ...   | nothing | _ = go rest
  ...   | just _ | nothing = go rest
  ...   | just source | just target with FloatValue.number (Edge.Edge.weight edgeRow) | go rest
  ...     | just weight | just later = just (Inference.incoming
    (Posterior.edge (Edge.Edge.from edgeRow) (Edge.Edge.to edgeRow) (Edge.Edge.relation edgeRow) weight)
    (Posterior.mean (Posterior.beta (Graph.BeliefValues.alpha source) (Graph.BeliefValues.beta source))) ∷ later)
  ...     | _ | _ = nothing

bothVisible : Maybe Text → Store.World → Edge.Edge → Bool
bothVisible scope state edgeRow with Ranking.lookup (Edge.Edge.from edgeRow) (Store.beliefs state)
  | Ranking.lookup (Edge.Edge.to edgeRow) (Store.beliefs state)
... | just source | just target = Ranking.visible scope (Graph.BeliefValues.project source) ∧
  Ranking.visible scope (Graph.BeliefValues.project target)
... | _ | _ = false

selectedEdges : Review.Relation → Maybe Text → Store.World → List Edge.Edge
selectedEdges relation scope state = filterᵇ (λ edgeRow →
  does (Review.relationCode relation ≟ Review.relationCode (Edge.Edge.relation edgeRow)) ∧
  bothVisible scope state edgeRow) (edges state)

contradictions : Maybe Text → Store.World → List (ℕ × ℕ)
contradictions scope state = map (λ edgeRow → Edge.Edge.from edgeRow , Edge.Edge.to edgeRow)
  (selectedEdges Review.contradicts scope state)

defeats : Maybe Text → Store.World → List Numeric.Defeat
defeats scope state = go (selectedEdges Review.defeats scope state)
  where
  go : List Edge.Edge → List Numeric.Defeat
  go [] = []
  go (edgeRow ∷ rest) with Ranking.lookup (Edge.Edge.from edgeRow) (Store.beliefs state)
  ... | nothing = go rest
  ... | just source = Numeric.defeat (Edge.Edge.from edgeRow) (Edge.Edge.to edgeRow)
    (Graph.BeliefValues.created source) ∷ go rest

pathQuery : ℕ → Bool → Paths.Query
pathQuery id false = Paths.allDownstream id
pathQuery id true = Paths.causalDownstream id

data InferenceRead (databaseSum : List Float → Float) (snapshot : Store.World) :
  (effect : Inference.Effect) → Inference.Reply effect → Set where
  readBelief : ∀ id → InferenceRead databaseSum snapshot (Inference.getBelief id)
    (inj₂ (Ranking.lookup id (Store.beliefs snapshot)))
  readIntervention : ∀ id tx → InferenceRead databaseSum snapshot (Inference.openIntervention id)
    (inj₂ (tx , snapshot , Ranking.lookup id (Store.beliefs snapshot)))
  readInSnapshot : ∀ tx first effect reply → snapshot ≡ first →
    InferenceRead databaseSum snapshot effect reply →
    InferenceRead databaseSum snapshot (Inference.inSnapshot tx first effect) reply
  readDescendants : ∀ id causal rows →
    Paths.Returned (pathQuery id causal) (Store.beliefs snapshot) (edges snapshot) rows →
    InferenceRead databaseSum snapshot (Inference.descendants id causal) (inj₂ rows)
  readReviews : InferenceRead databaseSum snapshot Inference.activeReviews (inj₂ (activeReviews snapshot))
  readGrounds : InferenceRead databaseSum snapshot Inference.groundingMasses (inj₂ (groundTotals databaseSum snapshot))
  readParents : ∀ ids rows → incoming ids snapshot ≡ just rows →
    InferenceRead databaseSum snapshot (Inference.incomingEdges ids) (inj₂ rows)
  readBeliefs : ∀ scope → InferenceRead databaseSum snapshot (Inference.listBeliefs scope)
    (inj₂ (Records.listBeliefs scope nothing (Store.beliefs snapshot)))
  readContradictions : ∀ scope tx → InferenceRead databaseSum snapshot (Inference.openContradictions scope)
    (inj₂ (tx , snapshot , contradictions scope snapshot))
  readSnapshotBeliefs : ∀ tx first scope → snapshot ≡ first →
    InferenceRead databaseSum snapshot (Inference.snapshotBeliefs tx first scope)
      (inj₂ (Records.listBeliefs scope nothing (Store.beliefs snapshot)))
  readDefeats : ∀ scope → InferenceRead databaseSum snapshot (Inference.defeatTimes scope)
    (inj₂ (defeats scope snapshot))

data Statement : Set where
  insertBelief : Graph.BeliefValues → Maybe Origin.Provenance → Statement
  beliefVector : ℕ → Store.Vector → Statement
  posterior : ℤ → Posterior.State → Statement

apply : Statement → Store.World → Store.World
apply (insertBelief belief origin) = Write.insertBelief belief origin
apply (beliefVector id vector) state = record state
  { beliefVectors = Store.putVector id vector (Store.World.beliefVectors state) }
apply (posterior publicationTime writes) state = Store.setNodes (Recompute.applyAt publicationTime writes (Store.nodes state)) state

AdmittedStatement : Statement → Store.World → Set
AdmittedStatement (insertBelief belief origin) before = Evidence.ValidBelief belief
AdmittedStatement (beliefVector id vector) before =
  Σ Graph.BeliefValues (λ belief → Ranking.lookup id (Store.beliefs before) ≡ just belief)
AdmittedStatement (posterior publicationTime writes) before = Posterior.ValidState writes

record StatementPublication (statement : Statement) (before : Store.World)
  (receipt : DB.Receipt) (after : Store.World) : Set where
  field
    admitted : AdmittedStatement statement before
    publication : DB.Atomic before (apply statement before) receipt after

-- The checked target is from the same transaction as the vector write. A
-- result computed before deletion cannot recreate its vector afterwards.
missingBeliefCannotPublishVector : ∀ id vector before receipt after →
  Ranking.lookup id (Store.beliefs before) ≡ nothing →
  StatementPublication (beliefVector id vector) before receipt after → ⊥
missingBeliefCannotPublishVector id vector before receipt after absent evidence
  with Ranking.lookup id (Store.beliefs before)
     | absent
     | StatementPublication.admitted evidence
... | nothing | refl | belief , ()
... | just belief | () | _

-- A failed/lost acknowledgement has the same invariant on either possible
-- published state. Admission never licenses replacing the original priors.
posteriorPublicationPreservesValidity : ∀ publicationTime writes before receipt after →
  StatementPublication (posterior publicationTime writes) before receipt after →
  All Evidence.ValidNode (Store.nodes before) → All Evidence.ValidNode (Store.nodes after)
posteriorPublicationPreservesValidity publicationTime writes before receipt after evidence valid =
  DB.invariantPreserved (λ state → All Evidence.ValidNode (Store.nodes state))
    (StatementPublication.publication evidence) valid
    (Recompute.applyAtPreservesValidity publicationTime writes (Store.nodes before)
      (StatementPublication.admitted evidence) valid)

posteriorPublicationPreservesOriginals : ∀ publicationTime writes before receipt after →
  StatementPublication (posterior publicationTime writes) before receipt after →
  Recompute.originals (Store.nodes after) ≡ Recompute.originals (Store.nodes before)
posteriorPublicationPreservesOriginals publicationTime writes before receipt after evidence =
  DB.invariantPreserved
    (λ state → Recompute.originals (Store.nodes state) ≡ Recompute.originals (Store.nodes before))
    (StatementPublication.publication evidence) refl
    (Recompute.applyAtPreservesOriginals publicationTime writes (Store.nodes before))

-- A learning-only proposed state never overwrites document/vector/grounding
-- storage. These physical writes remain in the same database transaction.
LearningPublication : Store.World → Learning.World → DB.Receipt → Store.World → Set
LearningPublication before proposed receipt after = DB.Atomic before (Store.installLearning proposed before) receipt after

module Bound (database : ℕ) (calculator : Posterior.Calculator) (publicationTime : ℤ) where
  module G = Ground.Operation database calculator publicationTime
  module D = Deletion.Operation database calculator publicationTime

  data GroundSuccess (chunk belief : ℕ) (weight : Float) : Set where
    committed : ∀ events → G.T.E.Runs (G.Run.P.start (Ground.add chunk belief weight)) events (G.T.applied tt) →
      GroundSuccess chunk belief weight
    replayed : ∀ events cleanup → G.T.E.Runs (G.Run.P.start (Ground.add chunk belief weight)) events (G.T.replayed tt cleanup) →
      GroundSuccess chunk belief weight

  data Deleted (id : ℕ) (value : Bool) : Set where
    committed : ∀ events → D.T.E.Runs (D.Run.start Deletion.belief id) events (D.T.applied value) → Deleted id value
    replayed : ∀ events cleanup → D.T.E.Runs (D.Run.start Deletion.belief id) events (D.T.replayed value cleanup) → Deleted id value

  data EmbeddingWrite : Embedding.Effect → Store.World → Store.World → Set where
    upserted : ∀ id values before after → StatementPublication (beliefVector id values) before DB.committed after →
      EmbeddingWrite (Embedding.upsert id values) before after

vectorWritePreservesLearning : ∀ id vector state →
  Store.World.learning (apply (beliefVector id vector) state) ≡ Store.World.learning state
vectorWritePreservesLearning id vector state = refl

posteriorWritePreservesEvidence : ∀ publicationTime writes state →
  Store.World.grounds (apply (posterior publicationTime writes) state) ≡ Store.World.grounds state
posteriorWritePreservesEvidence publicationTime writes state = refl

learningCommitPreservesOtherStores : ∀ before proposed receipt after →
  LearningPublication before proposed receipt after →
  (Store.World.chunks after ≡ Store.World.chunks before) ×
  (Store.World.beliefVectors after ≡ Store.World.beliefVectors before) ×
  (Store.World.chunkVectors after ≡ Store.World.chunkVectors before) ×
  (Store.World.grounds after ≡ Store.World.grounds before)
learningCommitPreservesOtherStores before proposed receipt after publication =
  DB.invariantPreserved (λ state →
    (Store.World.chunks state ≡ Store.World.chunks before) ×
    (Store.World.beliefVectors state ≡ Store.World.beliefVectors before) ×
    (Store.World.chunkVectors state ≡ Store.World.chunkVectors before) ×
    (Store.World.grounds state ≡ Store.World.grounds before))
    publication (refl , refl , refl , refl) (refl , refl , refl , refl)
