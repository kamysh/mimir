{-# OPTIONS --safe #-}
-- Service orchestration for propagation, intervention, decay, contradictions
-- and defeated-belief sweep. Every read is a separate observation. The
-- dependency owns I/O; all application numerical decisions are concrete.
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
  contradictionPairs defeatTimes : Maybe Text → Effect
  clock : Effect
  hashIteration : List ℕ → Effect
  persistBeta : P.State → Effect
  deleteBelief : ℕ → Effect -- GraphDeletion.Operation, including its transaction

Reply : Effect → Set
Reply (getBelief id) = Text ⊎ Maybe G.BeliefValues
Reply (descendants id causal) = Text ⊎ List G.BeliefValues
Reply activeReviews = Text ⊎ List Reviews.Review
Reply groundingMasses = Text ⊎ List (ℕ × Float)
Reply (incomingEdges ids) = Text ⊎ List Incoming
Reply (listBeliefs project) = Text ⊎ List G.BeliefValues
Reply (contradictionPairs project) = Text ⊎ List (ℕ × ℕ)
Reply (defeatTimes project) = Text ⊎ List N.Defeat
Reply clock = ℤ
Reply (hashIteration ids) = Σ (List ℕ) (λ order → order ↭ ids)
Reply (persistBeta writes) = Text ⊎ DB.Receipt
Reply (deleteBelief id) = Text ⊎ Bool

module E = Effects.Protocol Effect Reply
open E

data Result : Set where
  failed : Text → Result
  missingBelief invalidProbability invalidDecay invalidNumericInput invalidNumericWrite : Result
  publicationUncertain publicationAborted : Result
  projected propagated : List (ℕ × Float) → Bool → Result
  changed deleted : ℕ → Result
  pairs : List (ℕ × ℕ) → Result

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

persist : P.State → Result → Script Result
persist writes success with L.validWrites writes
... | false = done invalidNumericWrite
... | true = ask (persistBeta writes) (λ
  { (inj₁ error) → done (failed error)
  ; (inj₂ DB.committed) → done success
  ; (inj₂ DB.aborted) → done publicationAborted
  ; (inj₂ DB.acknowledgementLost) → done publicationUncertain })

finishPropagation : Bool → P.Result → Script Result
finishPropagation causal outcome with P.Result.numericFailure outcome
... | true = done invalidNumericWrite
... | false with causal
...   | true = done (projected (N.project (P.Result.writes outcome)) (P.Result.iterationLimitReached outcome))
...   | false = persist (P.Result.writes outcome)
  (propagated (N.project (P.Result.writes outcome)) (P.Result.iterationLimitReached outcome))

calculate : Bool → ℕ → Float → List G.BeliefValues → List Reviews.Review →
  List (ℕ × Float) → List Incoming → Script Result
calculate causal id value beliefs reviews ground incomingRows with prepare (concatMap Reviews.Review.feedbacks reviews) ground beliefs
... | nothing = done invalidNumericInput
... | just nodes with causal
...   | true = finishPropagation true (N.intervene id value nodes (map Incoming.edge incomingRows) ext)
  where ext = external (id ∷ map G.BeliefValues.identity beliefs) incomingRows
...   | false = finishPropagation false (P.run (just (id , value)) ext (map Incoming.edge incomingRows) nodes)
  where ext = external (id ∷ map G.BeliefValues.identity beliefs) incomingRows

afterSeed : Bool → ℕ → Float → Script Result
afterSeed causal id value = read (descendants id causal) refl (λ beliefs →
  read activeReviews refl (λ reviews → read groundingMasses refl (λ ground →
    read (incomingEdges (map G.BeliefValues.identity beliefs Data.List.++ (id ∷ []))) refl
      (calculate causal id value beliefs reviews ground))))
  where open import Relation.Binary.PropositionalEquality using (refl)

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
... | true = read (getBelief id) refl (λ
  { nothing → done missingBelief ; (just b) → afterSeed true id value })
  where open import Relation.Binary.PropositionalEquality using (refl)
start (decay project factor) = read (listBeliefs project) refl (λ beliefs →
  read groundingMasses refl (λ ground → ask clock (λ now → decide (N.decay now factor ground beliefs))))
  where
  open import Relation.Binary.PropositionalEquality using (refl)
  decide : Maybe P.State → Script Result
  decide nothing = done invalidDecay
  decide (just writes) = persist writes (changed (length writes))
start (contradictions project) = read (contradictionPairs project) refl decide
  where
  open import Relation.Binary.PropositionalEquality using (refl)
  decide : List (ℕ × ℕ) → Script Result
  decide [] = done (pairs [])
  decide candidates@(_ ∷ _) = read (listBeliefs project) refl
    (λ beliefs → done (pairs (N.activeContradictions beliefs candidates)))
start (sweep project threshold grace) = read (defeatTimes project) refl decide
  where
  open import Relation.Binary.PropositionalEquality using (refl)
  decide : List N.Defeat → Script Result
  decide [] = done (deleted 0)
  decide edges@(_ ∷ _) = read (listBeliefs project) refl (λ beliefs → ask clock (λ now →
    ask (hashIteration (Ranking.unique (map N.Defeat.target edges))) (λ { (order , sameMembers) →
      sweepDeletes 0 (N.expiredTargets now grace threshold beliefs edges order) })))
