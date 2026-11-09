{-# OPTIONS --safe #-}
-- Service orchestration for propagation, intervention, decay, contradictions
-- and defeated-belief sweep. Ordinary reads are separate observations;
-- contradictions and intervention inputs explicitly share read-only snapshots.
-- The dependency owns I/O; application numerical decisions are concrete.
module Mimir.InferenceProtocol where

open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.Float.Base using (Float; _+_)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_; map; concatMap; filterᵇ; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _≟_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (does)
open import Mimir.Text using (Text)
import Mimir.Effects as Effects
import Mimir.RetrievalRanking as Ranking
import Mimir.CandidateGraph as G
import Mimir.PosteriorComputation as P
import Mimir.GraphNumerics as N
import Mimir.LearningRecompute as L
import Mimir.ReviewSchema as Reviews
import Mimir.DatabaseTransaction as DB
import Mimir.EvidenceValidity as Evidence
import Mimir.ApplicationStore as Store
import Mimir.McpErrors as Errors
import Mimir.Validation as Validation
module Correction = Errors.AgentCorrection

record Incoming : Set where
  constructor incoming
  field edge : P.Edge; sourceMean : Float

data Request : Set where
  propagate : ℕ → Request
  intervention : ℕ → Float → Request
  decay : Maybe Text → Float → Request
  contradictions : Maybe Text → Request
  sweep : Maybe Text → Float → ℤ → Request -- grace in nanoseconds

data Effect : Set where
  getBelief : ℕ → Effect
  descendants : ℕ → Bool → Effect -- GraphPaths contract: mixed closure / causal-only closure, both unbounded
  activeReviews groundingMasses : Effect
  incomingEdges : List ℕ → Effect
  listBeliefs : Maybe Text → Effect
  defeatTimes : Maybe Text → Effect
  openContradictions : Maybe Text → Effect
  snapshotBeliefs : ℕ → Store.World → Maybe Text → Effect
  closeContradictions : ℕ → Effect
  openIntervention : ℕ → Effect
  inSnapshot : ℕ → Store.World → Effect → Effect
  closeIntervention : ℕ → Effect
  clock : Effect
  hashIteration : List ℕ → Effect
  calculatePosterior : P.Seed → P.External → List P.Edge → List P.Node → Effect
  persistBeta : ℤ → P.State → Effect
  deleteBelief : ℕ → Effect -- GraphDeletion.Operation, including its transaction

Reply : Effect → Set
Reply (getBelief id) = Text ⊎ Maybe G.BeliefValues
Reply (descendants id causal) = Text ⊎ List G.BeliefValues
Reply activeReviews = Text ⊎ List Reviews.Review
Reply groundingMasses = Text ⊎ List (ℕ × Float)
Reply (incomingEdges ids) = Text ⊎ List Incoming
Reply (listBeliefs project) = Text ⊎ List G.BeliefValues
Reply (openContradictions project) = Text ⊎ (ℕ × Store.World × List (ℕ × ℕ))
Reply (snapshotBeliefs tx first project) = Text ⊎ List G.BeliefValues
Reply (closeContradictions tx) = ⊤
Reply (openIntervention id) = Text ⊎ (ℕ × Store.World × Maybe G.BeliefValues)
Reply (inSnapshot tx first effect) = Reply effect
Reply (closeIntervention tx) = ⊤
Reply (defeatTimes project) = Text ⊎ (Correction.Claim ⊎ List N.Defeat)
Reply clock = ℤ
Reply (hashIteration ids) = Σ (List ℕ) (λ order → order ↭ ids)
Reply (calculatePosterior seed external edges nodes) = P.CalculationReport
Reply (persistBeta publicationTime writes) = Text ⊎ DB.Receipt
Reply (deleteBelief id) = Text ⊎ Bool

module E = Effects.Protocol Effect Reply
open E

data Result : Set where
  failed : Text → Result
  needsInput : Correction.Claim → Result
  missingBelief invalidProbability invalidDecay invalidNumericInput invalidNumericWrite : Result
  publicationUncertain publicationAborted : Result
  projected propagated : List (ℕ × Float) → Bool → Result
  changed deleted : ℕ → Result
  pairs : List (ℕ × ℕ) → Result
  numericalDecision : P.State → List P.State → Result

closeRead : ℕ → Result → Script Result
closeRead tx result = ask (closeContradictions tx) (λ _ → done result)

read : (effect : Effect) → ∀ {A} → Reply effect ≡ (Text ⊎ A) → (A → Script Result) → Script Result
read effect {A} same next = ask effect (λ response → receive (subst (λ X → X) same response))
  where
  receive : Text ⊎ A → Script Result
  receive (inj₁ error) = done (failed error)
  receive (inj₂ value) = next value

external : List ℕ → List Incoming → P.External
external ids [] = []
external ids (r ∷ rows) with Ranking.member (P.Edge.source (Incoming.edge r)) ids
... | true = external ids rows
... | false = (P.Edge.source (Incoming.edge r) , Incoming.sourceMean r) ∷ external ids rows

-- Service propagation adds ground first, then learning mass. Learning review
-- publication uses its own mass aggregation order in LearningRecompute.
prepare : List Reviews.Feedback → List (ℕ × Float) → List G.BeliefValues → Maybe (List P.Node)
prepare feedback ground [] = just []
prepare feedback ground (b ∷ bs) with L.feedbackMass (G.BeliefValues.identity b) feedback (P.beta 0.0 0.0)
  | prepare feedback ground bs
... | nothing | _ = nothing
... | just mass | nothing = nothing
... | just mass | just rest with Evidence.validBelief b
...   | false = nothing
...   | true = just (P.node (G.BeliefValues.identity b)
  (P.beta ((G.BeliefValues.alpha0 b + N.massOf (G.BeliefValues.identity b) ground) + P.Beta.alpha mass)
    (G.BeliefValues.beta0 b + P.Beta.negative mass))
  (P.beta (G.BeliefValues.alpha b) (G.BeliefValues.beta b)) ∷ rest)

persistAt : ℤ → P.State → Result → Script Result
persistAt publicationTime writes success with L.validWrites writes
... | false = done invalidNumericWrite
... | true = ask (persistBeta publicationTime writes) (λ
  { (inj₁ error) → done (failed error)
  ; (inj₂ DB.committed) → done success
  ; (inj₂ DB.aborted) → done publicationAborted
  ; (inj₂ DB.acknowledgementLost) → done publicationUncertain })

persist : P.State → Result → Script Result
persist writes success = ask clock (λ publicationTime → persistAt publicationTime writes success)

module Calculation (seed : P.Seed) (external : P.External)
  (edges : List P.Edge) (nodes : List P.Node) where
  module A = P.Assess seed external edges nodes

  finish : Bool → A.Verdict → Script Result
  finish causal A.rejected = done invalidNumericWrite
  finish causal (A.repeated final visited seen incomplete steps) = done (numericalDecision final visited)
  finish causal outcome@(A.accepted final valid shape complete) with causal
  ... | true = done (projected (N.project (A.writes outcome)) false)
  ... | false = persist (A.writes outcome) (propagated (N.project (A.writes outcome)) false)

  -- No effect is exposed after a checked incomplete repetition. In
  -- particular persistBeta cannot be reached, for any repeat or history.
  repetitionCannotPersist : ∀ causal final visited seen incomplete steps events reply →
    E.Runs (finish causal (A.repeated final visited seen incomplete steps)) events reply →
    events ≡ [] × reply ≡ numericalDecision final visited
  repetitionCannotPersist causal final visited seen incomplete steps events reply execution =
    E.completedCannotProduceEffects execution

  start : Bool → Script Result
  start causal = ask (calculatePosterior seed external edges nodes) (λ report → finish causal (A.check report))

calculate : Bool → ℕ → Float → List G.BeliefValues → List Reviews.Review →
  List (ℕ × Float) → List Incoming → Script Result
calculate causal id value beliefs reviews ground incomingRows with prepare (concatMap Reviews.Review.feedbacks reviews) ground beliefs
... | nothing = done invalidNumericInput
... | just nodes with causal
...   | true = Calculation.start (just (id , value)) ext
  (filterᵇ (N.surgical id) (map Incoming.edge incomingRows)) nodes true
  where ext = external (id ∷ map G.BeliefValues.identity beliefs) incomingRows
...   | false = Calculation.start (just (id , value)) ext (map Incoming.edge incomingRows) nodes false
  where ext = external (id ∷ map G.BeliefValues.identity beliefs) incomingRows

afterSeed : Bool → ℕ → Float → Script Result
afterSeed causal id value = read (descendants id causal) refl (λ beliefs →
  read activeReviews refl (λ reviews → read groundingMasses refl (λ ground →
    read (incomingEdges (map G.BeliefValues.identity beliefs Data.List.++ (id ∷ []))) refl
      (calculate causal id value beliefs reviews ground))))
  where open import Relation.Binary.PropositionalEquality using (refl)

closeProjection : ℕ → Result → Script Result
closeProjection tx result = ask (closeIntervention tx) (λ _ → done result)

readAt : ℕ → Store.World → (effect : Effect) → ∀ {A} → Reply effect ≡ (Text ⊎ A) →
  (A → Script Result) → Script Result
readAt tx first effect {A} same next = ask (inSnapshot tx first effect)
  (λ response → receive (subst (λ X → X) same response))
  where
  receive : Text ⊎ A → Script Result
  receive (inj₁ error) = closeProjection tx (failed error)
  receive (inj₂ value) = next value

projectFrom : ℕ → Store.World → ℕ → Float → Script Result
projectFrom tx first id value = readAt tx first (descendants id true) refl (λ beliefs →
  readAt tx first activeReviews refl (λ reviews → readAt tx first groundingMasses refl (λ ground →
    readAt tx first (incomingEdges (map G.BeliefValues.identity beliefs Data.List.++ (id ∷ []))) refl
      (λ incomingRows → calculate true id value beliefs reviews ground incomingRows >>= closeProjection tx))))

sweepDeletes : ℕ → List ℕ → Script Result
sweepDeletes count [] = done (deleted count)
sweepDeletes count (id ∷ ids) = read (deleteBelief id) refl (λ
  { true → sweepDeletes (suc count) ids ; false → sweepDeletes count ids })
  where open import Relation.Binary.PropositionalEquality using (refl)

start : Request → Script Result
start (propagate id) = read (getBelief id) refl (λ
  { nothing → done missingBelief ; (just b) → afterSeed false id (G.BeliefValues.probability b) })
  where open import Relation.Binary.PropositionalEquality using (refl)
start (intervention id value) with N.probability value
... | false = done invalidProbability
... | true = ask (openIntervention id) (λ
  { (inj₁ error) → done (failed error)
  ; (inj₂ (tx , first , nothing)) → closeProjection tx missingBelief
  ; (inj₂ (tx , first , just b)) → projectFrom tx first id value })
  where open import Relation.Binary.PropositionalEquality using (refl)
start (decay project factor) = read (listBeliefs project) refl (λ beliefs →
  read groundingMasses refl (λ ground → ask clock (λ now → decide beliefs now (N.decay now factor ground beliefs))))
  where
  open import Relation.Binary.PropositionalEquality using (refl)
  decide : List G.BeliefValues → ℤ → Maybe P.State → Script Result
  decide beliefs now nothing = done invalidDecay
  decide beliefs now (just writes) = persistAt now writes (changed (N.changedCount beliefs writes))
start (contradictions project) = read (openContradictions project) refl decide
  where
  open import Relation.Binary.PropositionalEquality using (refl)
  decide : ℕ × Store.World × List (ℕ × ℕ) → Script Result
  decide (tx , first , []) = closeRead tx (pairs [])
  decide (tx , first , candidates@(_ ∷ _)) = ask (snapshotBeliefs tx first project) (λ
    { (inj₁ error) → closeRead tx (failed error)
    ; (inj₂ beliefs) → closeRead tx (pairs (N.activeContradictions beliefs candidates)) })
start (sweep project threshold grace) with N.probability threshold
... | false = done invalidProbability
... | true = read (defeatTimes project) refl decide
  where
  open import Relation.Binary.PropositionalEquality using (refl)
  decide : Correction.Claim ⊎ List N.Defeat → Script Result
  decide (inj₁ issue) = done (needsInput issue)
  decide (inj₂ []) = done (deleted 0)
  decide (inj₂ edges@(_ ∷ _)) = read (listBeliefs project) refl (λ beliefs → ask clock (λ now →
    ask (hashIteration (Ranking.unique (map N.Defeat.target edges))) (λ { (order , sameMembers) →
      sweepDeletes 0 (N.expiredTargets now grace threshold beliefs edges order) })))

-- An invalid threshold cannot even read the store, whatever the project,
-- retention policy or replies a caller might otherwise supply.
invalidSweepHasNoEffects : ∀ project threshold grace events result →
  N.probability threshold ≡ false →
  E.Runs (start (sweep project threshold grace)) events result →
  events ≡ [] × result ≡ invalidProbability
invalidSweepHasNoEffects project threshold grace events result rejected run
  rewrite rejected = E.completedCannotProduceEffects run
