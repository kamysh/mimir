{-# OPTIONS --safe #-}
-- Read effects observe their own statement snapshots; numerical persistence
-- acknowledges the exact posterior write set; sweep deletion runs the complete
-- deletion transaction. Clock, HashMap iteration and chrono are dependencies.
module Mimir.InferenceStorageBinding where

open import Data.List using (List; []; _∷_; map; filterᵇ; concatMap)
open import Data.Float.Base using (Float)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false; not)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Binary.PropositionalEquality using (sym; subst)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)
import Data.List.Relation.Unary.Any as Any
open import Data.Empty using (⊥)
import Mimir.ApplicationStore as Store
import Mimir.InferenceProtocol as I
import Mimir.StorageSemantics as S
import Mimir.StorageReadBinding as Read
import Mimir.DatabaseReadCommitted as Committed
import Mimir.DatabaseTransaction as DB
import Mimir.PosteriorComputation as P
import Mimir.LearningRecompute as Recompute
import Mimir.CandidateGraph as Graph
import Mimir.ReviewSchema as Review
import Mimir.ReviewEdges as Edges
import Mimir.GraphNumerics as Numeric
import Mimir.RetrievalRanking as Ranking
import Mimir.Recovery as Recovery
import Data.List.Relation.Binary.Permutation.Propositional as Permutation

-- Numerical intent is derived from the request and the complete initial
-- world. It is independent of pass counts and of the solver's chosen iterate.
module NumericalOutcome (databaseSum : List Float → Float) where
  data Request : Set where
    propagate : ℕ → Request
    intervention : ℕ → Float → Request
    recompute : List ℕ → Request

  data PreparationIssue : Set where
    missingSeed : ℕ → PreparationIssue
    invalidIntervention : Float → PreparationIssue
    invalidStoredInputs : PreparationIssue

  record Context : Set where
    constructor context
    field
      readOnly : Bool
      seed : P.Seed
      external : P.External
      edges : List P.Edge
      targets : List P.Node

  causal : ℕ → Edges.Edge → Bool
  causal seed edgeRow with Edges.Edge.relation edgeRow
  ... | Review.causes = not (does (seed ≟ Edges.Edge.to edgeRow))
  ... | _ = false

  selectEdges : Bool → ℕ → List Edges.Edge → List Edges.Edge
  selectEdges false identity edges = edges
  selectEdges true identity edges = filterᵇ (causal identity) edges

  prepareSelected : Bool → P.Seed → List Edges.Edge → List Graph.BeliefValues →
    Store.World → PreparationIssue ⊎ Context
  prepareSelected readOnly seed rawEdges selected snapshot with
    I.prepare (concatMap Review.Review.feedbacks (S.activeReviews snapshot))
      (S.groundTotals databaseSum snapshot) selected
    | Recompute.prepareEdges (map Graph.BeliefValues.identity selected) rawEdges
  ... | nothing | _ = inj₁ invalidStoredInputs
  ... | just nodes | nothing = inj₁ invalidStoredInputs
  ... | just nodes | just incoming = inj₂ (context readOnly seed
    (Recompute.external (map P.Node.identity nodes) (Store.beliefs snapshot)) incoming nodes)

  seeded : Bool → ℕ → Float → Store.World → PreparationIssue ⊎ Context
  seeded readOnly identity value snapshot = prepareSelected readOnly (just (identity , value))
    incoming selected snapshot
    where
    incoming = selectEdges readOnly identity (S.edges snapshot)
    reached = Recompute.closureScoped nothing (Store.beliefs snapshot) incoming (identity ∷ [])
    selected = filterᵇ (λ b → not (does (identity ≟ Graph.BeliefValues.identity b)))
      (Recompute.selected reached (Store.beliefs snapshot))

  prepare : Request → Store.World → PreparationIssue ⊎ Context
  prepare (propagate identity) snapshot with Ranking.lookup identity (Store.beliefs snapshot)
  ... | nothing = inj₁ (missingSeed identity)
  ... | just belief = seeded false identity (Graph.BeliefValues.probability belief) snapshot
  prepare (intervention identity value) snapshot with Numeric.probability value
  ... | false = inj₁ (invalidIntervention value)
  ... | true with Ranking.lookup identity (Store.beliefs snapshot)
  ...   | nothing = inj₁ (missingSeed identity)
  ...   | just _ = seeded true identity value snapshot
  prepare (recompute roots) snapshot with
    Recompute.prepareNodes (concatMap Review.Review.feedbacks (S.activeReviews snapshot))
      (S.groundTotals databaseSum snapshot) selected
    | Recompute.prepareEdges (map Graph.BeliefValues.identity selected) (S.edges snapshot)
    where
    selected = Recompute.selected
      (Recompute.closureScoped nothing (Store.beliefs snapshot) (S.edges snapshot) roots)
      (Store.beliefs snapshot)
  ... | nothing | _ = inj₁ invalidStoredInputs
  ... | just nodes | nothing = inj₁ invalidStoredInputs
  ... | just nodes | just incoming = inj₂ (context false nothing
    (Recompute.external (map P.Node.identity nodes) (Store.beliefs snapshot)) incoming nodes)

  ordered : Context → List P.Node
  ordered selected = P.order (Context.seed selected) (Context.targets selected)

  writes : Context → P.State → P.State
  writes selected = P.updates (ordered selected)

  proposed : Context → Store.World → P.State → Store.World
  proposed selected before counts with Context.readOnly selected
  ... | true = before
  ... | false = Store.setNodes (Recompute.apply (writes selected counts) (Store.nodes before)) before

  -- Every stored component is retained in this equality. Only the declared
  -- posterior fields may differ; cached values are derived by apply.
  Completed : Context → Store.World → Store.World → List (ℕ × Float) → Set
  Completed selected before after reply = Σ (List P.Edge) (λ incoming →
    incoming ↭ Context.edges selected × Σ P.State (λ counts →
    P.ValidState counts ×
    map proj₁ counts ≡ map P.Node.identity (ordered selected) ×
    P.PosteriorGoal (Context.seed selected) (Context.external selected)
      incoming (ordered selected) counts ×
    after ≡ proposed selected before counts ×
    reply ≡ Numeric.project (writes selected counts)))

  completedHasEveryPosterior : ∀ selected before after reply → Completed selected before after reply →
    Σ (List P.Edge) (λ incoming → incoming ↭ Context.edges selected ×
      Σ P.State (λ counts → P.PosteriorGoal (Context.seed selected) (Context.external selected)
        incoming (ordered selected) counts))
  completedHasEveryPosterior selected before after reply (incoming , allInputs , counts , valid , shape , complete , framed , answered) =
    incoming , allInputs , counts , complete

  readOnlyCompletionPreservesWholeWorld : ∀ selected before after reply →
    Context.readOnly selected ≡ true → Completed selected before after reply → after ≡ before
  readOnlyCompletionPreservesWholeWorld selected before after reply readOnly
    (incoming , allInputs , counts , valid , shape , complete , framed , answered) rewrite readOnly = framed

  -- This projection is only a preservation theorem. Completed still compares
  -- the COMPLETE final world with the specified posterior update above.
  withoutNodes : Store.World → Store.World
  withoutNodes = Store.setNodes []

  completedPreservesOtherStoreComponents : ∀ selected before after reply →
    Completed selected before after reply → withoutNodes after ≡ withoutNodes before
  completedPreservesOtherStoreComponents selected before after reply
    (incoming , allInputs , counts , valid , shape , complete , framed , answered) with Context.readOnly selected
  ... | true = cong withoutNodes framed
  ... | false rewrite framed = refl

  module Cycle (selected : Context) (incoming : List P.Edge) where
    module C = P.Cyclic (Context.seed selected) (Context.external selected) incoming (ordered selected)

    Repeated : P.State → List P.State → Set
    Repeated repeated visited = Σ (Any.Any (repeated ≡_) visited) (λ seen →
      Σ (P.PosteriorGoal (Context.seed selected) (Context.external selected)
        incoming (ordered selected) repeated → ⊥) (λ incomplete →
      C.Runs (C.begin (P.initial (ordered selected)))
        (C.needsDecision repeated visited seen incomplete)))

    Invalid : P.State → Set
    Invalid counts = C.Runs (C.begin (P.initial (ordered selected))) (C.invalid counts)

  data Result : Set where
    unavailable : PreparationIssue → Result
    calculated : List (ℕ × Float) → Result
    needsDecision : P.State → List P.State → Result
    invalidCalculation : P.State → Result
    rejectedReport : P.CalculationReport → Result

  PreparedGoal : Context → Store.World → Store.World → Result → Set
  PreparedGoal selected before after (unavailable issue) = ⊥
  PreparedGoal selected before after (calculated reply) = Completed selected before after reply
  PreparedGoal selected before after (needsDecision repeated visited) =
    after ≡ before × Σ (List P.Edge) (λ incoming →
      incoming ↭ Context.edges selected × Cycle.Repeated selected incoming repeated visited)
  PreparedGoal selected before after (invalidCalculation counts) =
    after ≡ before × Σ (List P.Edge) (λ incoming →
      incoming ↭ Context.edges selected × Cycle.Invalid selected incoming counts)
  PreparedGoal selected before after (rejectedReport report) =
    after ≡ before × A.check report ≡ A.rejected
    where module A = P.Assess (Context.seed selected) (Context.external selected)
            (Context.edges selected) (Context.targets selected)

  -- The request and initial store select the requirement. There is no goal
  -- field for an operation to replace with a weaker condition. A publication
  -- wrapper must additionally retain its registered saved replies; this is
  -- the numerical business condition that wrapper has to establish.
  Goal : Request → Store.World → Store.World → Result → Set
  Goal request before after reply with prepare request before
  ... | inj₁ issue = after ≡ before × reply ≡ unavailable issue
  ... | inj₂ selected = PreparedGoal selected before after reply

  decisionCannotChangeStoredData : ∀ selected before after repeated visited →
    PreparedGoal selected before after (needsDecision repeated visited) → after ≡ before
  decisionCannotChangeStoredData selected before after repeated visited (unchanged , seen) = unchanged

-- Querying a counterfactual never publishes its projected posteriors. The
-- raw calculator is untrusted: complete answers owe every posterior equation,
-- while a rejected report or actual cycle repetition returns its evidence.
module InterventionRecovery (databaseSum : List Float → Float) (calculator : P.Calculator) where
  module N = NumericalOutcome databaseSum

  record Input : Set where
    constructor input
    field identity : ℕ; value : Float

  request : Input → N.Request
  request query = N.intervention (Input.identity query) (Input.value query)

  selectedIsReadOnly : ∀ seed edges selected before chosen →
    N.prepareSelected true seed edges selected before ≡ inj₂ chosen →
    N.Context.readOnly chosen ≡ true
  selectedIsReadOnly seed edges selected before chosen observed with
    I.prepare (concatMap Review.Review.feedbacks (S.activeReviews before))
      (S.groundTotals databaseSum before) selected
    | Recompute.prepareEdges (map Graph.BeliefValues.identity selected) edges
  ... | nothing | _ with observed
  ...   | ()
  selectedIsReadOnly seed edges selected before chosen observed | just nodes | nothing with observed
  ... | ()
  selectedIsReadOnly seed edges selected before ._ refl | just nodes | just incoming = refl

  preparedIsReadOnly : ∀ query before selected →
    N.prepare (request query) before ≡ inj₂ selected → N.Context.readOnly selected ≡ true
  preparedIsReadOnly query before selected observed with Numeric.probability (Input.value query)
  ... | false with observed
  ...   | ()
  preparedIsReadOnly query before selected observed | true with Ranking.lookup (Input.identity query) (Store.beliefs before)
  ... | nothing with observed
  ...   | ()
  preparedIsReadOnly query before selected observed | true | just belief =
    selectedIsReadOnly (just (identity , Input.value query)) incoming targets before selected observed
    where
    identity = Input.identity query
    incoming = N.selectEdges true identity (S.edges before)
    reached = Recompute.closureScoped nothing (Store.beliefs before) incoming (identity ∷ [])
    targets = filterᵇ (λ b → not (does (identity ≟ Graph.BeliefValues.identity b)))
      (Recompute.selected reached (Store.beliefs before))

  fromReport : N.Context → P.CalculationReport → N.Result
  fromReport selected report = finish (A.check report)
    where
    module A = P.Assess (N.Context.seed selected) (N.Context.external selected)
      (N.Context.edges selected) (N.Context.targets selected)
    finish : A.Verdict → N.Result
    finish A.rejected = N.rejectedReport report
    finish checked@(A.accepted final valid shape complete) = N.calculated (Numeric.project (A.writes checked))
    finish (A.repeated final visited seen incomplete steps) = N.needsDecision final visited

  report : N.Context → P.CalculationReport
  report selected = calculator (N.Context.seed selected) (N.Context.external selected)
    (N.Context.edges selected) (N.Context.targets selected)

  answer : Input → Store.World → N.Result
  answer query before with N.prepare (request query) before
  ... | inj₁ issue = N.unavailable issue
  ... | inj₂ selected = fromReport selected (report selected)

  reportMeetsGoal : ∀ selected before → N.Context.readOnly selected ≡ true → ∀ raw →
    N.PreparedGoal selected before before (fromReport selected raw)
  reportMeetsGoal selected before readOnly raw with A.check raw in checked
    where module A = P.Assess (N.Context.seed selected) (N.Context.external selected)
            (N.Context.edges selected) (N.Context.targets selected)
  ... | P.Assess.rejected = refl , checked
  ... | P.Assess.accepted final valid shape complete rewrite readOnly =
    N.Context.edges selected , Permutation.refl , final , valid , shape , complete , refl , refl
  ... | P.Assess.repeated final visited seen incomplete steps =
    refl , N.Context.edges selected , Permutation.refl , seen , incomplete , steps

  answerMeetsGoal : ∀ query before → N.Goal (request query) before before (answer query before)
  answerMeetsGoal query before with N.prepare (request query) before in prepared
  ... | inj₁ issue = refl , refl
  ... | inj₂ selected = reportMeetsGoal selected before (preparedIsReadOnly query before selected prepared) (report selected)

  module QueryRead = Recovery.ReadOnly answer
  module R = QueryRead.Checked

  Goal : Input → Store.World → Store.World → N.Result → Set
  Goal query before after result = N.Goal (request query) before after result

  completedMeetsGoal : ∀ query before after result →
    R.X.Completed (R.script query) before after result → Goal query before after result
  completedMeetsGoal query before after result completion
    with R.completedMeetsIntent query before after result completion
  ... | refl = answerMeetsGoal query before

  completedPreservesWholeWorld : ∀ query before after result →
    R.X.Completed (R.script query) before after result → after ≡ before
  completedPreservesWholeWorld query before after result completion =
    cong proj₁ (R.completedMeetsIntent query before after result completion)

  operation : Recovery.RecoverableFor Store.World Input N.Result Goal
  operation = record
    { Effect = R.Effect; Reply = R.Reply; script = R.script; Atomic = R.Atomic
    ; progress = R.progress
    ; converges = λ query initial interrupted final result interruption completion →
        subst (λ before → Goal query before final result)
          (QueryRead.interruptedPreservesAllState query initial interrupted interruption)
          (completedMeetsGoal query interrupted final result completion)
    }

  module Run = Recovery.CheckedFor operation

module Bound (database : ℕ) (calculator : P.Calculator) (sum : List Float → Float) (reads : Committed.Contract Store.World) where
  private
    module R = Read.Observed reads
    module B = S.Bound database calculator

  data External : I.Effect → Set where
    clock : External I.clock
    iteration : ∀ ids → External (I.hashIteration ids)
    calculation : ∀ seed external edges nodes → External (I.calculatePosterior seed external edges nodes)
    snapshotClosed : ∀ tx → External (I.closeContradictions tx)

  data Receipt : (effect : I.Effect) → I.Reply effect → Set where
    selected : ∀ effect reply → R.SuccessfulInferenceReply sum effect reply → Receipt effect reply
    dependency : ∀ effect → External effect → (reply : I.Reply effect) → Receipt effect reply
    persisted : ∀ writes before receipt after → S.StatementPublication (S.posterior writes) before receipt after →
      Receipt (I.persistBeta writes) (inj₂ receipt)
    deleted : ∀ id value → B.Deleted id value → Receipt (I.deleteBelief id) (inj₂ value)
    beliefFailed : ∀ id error → Receipt (I.getBelief id) (inj₁ error)
    descendantsFailed : ∀ id causal error → Receipt (I.descendants id causal) (inj₁ error)
    reviewsFailed : ∀ error → Receipt I.activeReviews (inj₁ error)
    groundsFailed : ∀ error → Receipt I.groundingMasses (inj₁ error)
    incomingFailed : ∀ ids error → Receipt (I.incomingEdges ids) (inj₁ error)
    listFailed : ∀ scope error → Receipt (I.listBeliefs scope) (inj₁ error)
    contradictionsFailed : ∀ scope error → Receipt (I.openContradictions scope) (inj₁ error)
    snapshotBeliefsFailed : ∀ tx first scope error → Receipt (I.snapshotBeliefs tx first scope) (inj₁ error)
    defeatsFailed : ∀ scope error → Receipt (I.defeatTimes scope) (inj₁ error)
    persistenceFailed : ∀ writes error → Receipt (I.persistBeta writes) (inj₁ error)
    deletionFailed : ∀ id error → Receipt (I.deleteBelief id) (inj₁ error)
