{-# OPTIONS --safe #-}
-- Service orchestration for propagation, intervention, decay, contradictions
-- and defeated-belief sweep. Every read is a separate observation. The
-- dependency owns I/O and calculation. Recovery does not prescribe a solver.
module Mimir.InferenceProtocol where

open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.Float.Base using (Float; _+_)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_; map; concatMap; filterᵇ; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Mimir.UUIDGroups using (UUID)
open import Data.Product using (Σ; _×_; _,_)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Nullary using (does; ¬_)
open import Mimir.Text using (Text)
import Mimir.Effects as Effects
import Mimir.ApplicationStore as Store
open import Relation.Binary.PropositionalEquality using (trans)
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
  propagate : UUID → Request
  intervention : UUID → Float → Request
  decay : Maybe Text → Float → Request
  contradictions : Maybe Text → Request
  sweep : Maybe Text → Float → ℤ → Request -- grace in nanoseconds
  sweepHours : Maybe Text → Float → Float → Request

data Effect : Set where
  getBelief : UUID → Effect
  descendants : UUID → Bool → Effect -- GraphPaths contract: mixed closure / causal-only closure, both unbounded
  activeReviews groundingMasses : Effect
  incomingEdges : List UUID → Effect
  listBeliefs : Maybe Text → Effect
  contradictionPairs defeatTimes : Maybe Text → Effect
  clock : Effect
  convertGraceHours : Float → Effect
  hashIteration : List UUID → Effect
  computeBeta : Bool → P.Seed → P.External → List P.Edge → List P.Node → Effect
  -- Publication occurs inside the enclosing operation transaction.
  persistBeta : P.State → Effect
  deleteBeliefs : List UUID → Effect -- one transaction for the whole selection

Reply : Effect → Set
Reply (getBelief id) = Text ⊎ Maybe G.BeliefValues
Reply (descendants id causal) = Text ⊎ List G.BeliefValues
Reply activeReviews = Text ⊎ List Reviews.Review
Reply groundingMasses = Text ⊎ List (UUID × Float)
Reply (incomingEdges ids) = Text ⊎ List Incoming
Reply (listBeliefs project) = Text ⊎ List G.BeliefValues
Reply (contradictionPairs project) = Text ⊎ List (UUID × UUID)
Reply (defeatTimes project) = Text ⊎ List N.Defeat
Reply clock = ℤ
-- Standard round(hours*60), Rust saturating i64 conversion and chrono minutes.
-- Conversion occurs only after nonempty defeats, beliefs and the clock read.
Reply (convertGraceHours hours) = Maybe ℤ
Reply (hashIteration ids) = Σ (List UUID) (λ order → order ↭ ids)
Reply (computeBeta causal seed external edges nodes) = Text ⊎ P.Result
Reply (persistBeta writes) = Text ⊎ DB.Receipt
Reply (deleteBeliefs ids) = Text ⊎ ℕ

module E = Effects.Protocol Effect Reply
open E

data Result : Set where
  failed : Text → Result
  missingBelief invalidProbability invalidDecay invalidNumericInput invalidNumericWrite : Result
  publicationAborted : Result
  durationOutOfRange : Result
  projected propagated : List (UUID × Float) → Bool → Result
  changed deleted : ℕ → Result
  pairs : List (UUID × UUID) → Result

receiveRead : ∀ {A : Set} → (A → Script Result) → Text ⊎ A → Script Result
receiveRead next (inj₁ error) = done (failed error)
receiveRead next (inj₂ value) = next value

read : (effect : Effect) → ∀ {A} → Reply effect ≡ (Text ⊎ A) → (A → Script Result) → Script Result
read effect same next = ask effect (λ response → receiveRead next (subst (λ X → X) same response))

external : List UUID → List Incoming → P.External
external ids [] = []
external ids (r ∷ rows) with Ranking.member (P.Edge.source (Incoming.edge r)) ids
... | true = external ids rows
... | false = (P.Edge.source (Incoming.edge r) , Incoming.sourceMean r) ∷ external ids rows

-- Service propagation adds ground first, then learning mass. Learning review
-- publication uses its own mass aggregation order in LearningRecompute.
prepare : List Reviews.Feedback → List (UUID × Float) → List G.BeliefValues → Maybe (List P.Node)
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
  ; (inj₂ DB.aborted) → done publicationAborted })

finishPropagation : Bool → P.Result → Script Result
finishPropagation causal outcome with P.Result.numericFailure outcome
... | true = done invalidNumericWrite
... | false with causal
...   | true = done (projected (N.project (P.Result.writes outcome)) false)
...   | false = persist (P.Result.writes outcome)
  (propagated (N.project (P.Result.writes outcome)) false)

calculationEdges : Bool → UUID → List Incoming → List P.Edge
calculationEdges true id rows = filterᵇ (N.surgical id) (map Incoming.edge rows)
calculationEdges false id rows = map Incoming.edge rows

calculate : Bool → UUID → Float → List G.BeliefValues → List Reviews.Review →
  List (UUID × Float) → List Incoming → Script Result
calculate causal id value beliefs reviews ground incomingRows with prepare (concatMap Reviews.Review.feedbacks reviews) ground beliefs
... | nothing = done invalidNumericInput
... | just nodes = read (computeBeta causal (just (id , value)) ext (calculationEdges causal id incomingRows) nodes)
  refl (finishPropagation causal)
  where ext = external (id ∷ map G.BeliefValues.identity beliefs) incomingRows

afterSeed : Bool → UUID → Float → Script Result
afterSeed causal id value = read (descendants id causal) refl (λ beliefs →
  read activeReviews refl (λ reviews → read groundingMasses refl (λ ground →
    read (incomingEdges (map G.BeliefValues.identity beliefs Data.List.++ (id ∷ []))) refl
      (calculate causal id value beliefs reviews ground))))
  where open import Relation.Binary.PropositionalEquality using (refl)

sweepDeletes : List UUID → Script Result
sweepDeletes [] = done (deleted 0)
sweepDeletes ids@(_ ∷ _) = read (deleteBeliefs ids) refl (λ count → done (deleted count))
  where open import Relation.Binary.PropositionalEquality using (refl)

propagation : UUID → Script Result
propagation id = read (getBelief id) refl (λ
  { nothing → done missingBelief
  ; (just belief) → afterSeed false id (G.BeliefValues.probability belief) })

decayDecision : Float → List G.BeliefValues → List (UUID × Float) → ℤ → Script Result
decayDecision factor beliefs ground now with N.decay now factor ground beliefs
... | nothing = done invalidDecay
... | just writes = persist writes (changed (length writes))

selectedDeletes : Float → ℤ → List N.Defeat → List G.BeliefValues → ℤ → Script Result
selectedDeletes threshold grace edges beliefs now =
  ask (hashIteration (Ranking.unique (map N.Defeat.target edges))) (λ { (order , sameMembers) →
    sweepDeletes (N.expiredTargets now grace threshold beliefs edges order) })

afterDuration : Float → List N.Defeat → List G.BeliefValues → ℤ → Maybe ℤ → Script Result
afterDuration threshold edges beliefs now nothing = done durationOutOfRange
afterDuration threshold edges beliefs now (just grace) = selectedDeletes threshold grace edges beliefs now

start : Request → Script Result
start (propagate id) = propagation id
start (intervention id value) with N.probability value
... | false = done invalidProbability
... | true = read (getBelief id) refl (λ
  { nothing → done missingBelief ; (just b) → afterSeed true id value })
  where open import Relation.Binary.PropositionalEquality using (refl)
start (decay project factor) = read (listBeliefs project) refl (λ beliefs →
  read groundingMasses refl (λ ground → ask clock (decayDecision factor beliefs ground)))
start (contradictions project) = read (contradictionPairs project) refl decide
  where
  open import Relation.Binary.PropositionalEquality using (refl)
  decide : List (UUID × UUID) → Script Result
  decide [] = done (pairs [])
  decide candidates@(_ ∷ _) = read (listBeliefs project) refl
    (λ beliefs → done (pairs (N.activeContradictions beliefs candidates)))
start (sweep project threshold grace) = read (defeatTimes project) refl decide
  where
  open import Relation.Binary.PropositionalEquality using (refl)
  decide : List N.Defeat → Script Result
  decide [] = done (deleted 0)
  decide edges@(_ ∷ _) = read (listBeliefs project) refl (λ beliefs → ask clock (λ now →
    selectedDeletes threshold grace edges beliefs now))
start (sweepHours project threshold hours) = read (defeatTimes project) refl decide
  where
  decide : List N.Defeat → Script Result
  decide [] = done (deleted 0)
  decide edges@(_ ∷ _) = read (listBeliefs project) refl (λ beliefs → ask clock (λ now →
    ask (convertGraceHours hours) (afterDuration threshold edges beliefs now)))

-- Read-only requests cannot acquire a publication effect merely by being
-- registered as queries. This witness is consumed by the recovery dispatcher.
Observation : Effect → Set
Observation (persistBeta writes) = ⊥
Observation (deleteBeliefs ids) = ⊥
Observation (getBelief id) = ⊤
Observation (descendants id causal) = ⊤
Observation activeReviews = ⊤
Observation groundingMasses = ⊤
Observation (incomingEdges ids) = ⊤
Observation (listBeliefs project) = ⊤
Observation (contradictionPairs project) = ⊤
Observation (defeatTimes project) = ⊤
Observation clock = ⊤
Observation (convertGraceHours hours) = ⊤
Observation (hashIteration ids) = ⊤
Observation (computeBeta causal seed external edges nodes) = ⊤

data OnlyReads : Script Result → Set where
  noEffects : ∀ result → OnlyReads (done result)
  observation : ∀ {effect next} → Observation effect →
    (∀ reply → OnlyReads (next reply)) → OnlyReads (ask effect next)

ReadEffect = Σ Effect Observation
ReadReply : ReadEffect → Set
ReadReply (effect , witness) = Reply effect
module ReadProtocol = Effects.Protocol ReadEffect ReadReply

onlyReads : ∀ {program} → OnlyReads program → ReadProtocol.Script Result
onlyReads (noEffects result) = ReadProtocol.done result
onlyReads (observation {effect = effect} witness next) =
  ReadProtocol.ask (effect , witness) (λ reply → onlyReads (next reply))

readObservation : (effect : Effect) → ∀ {A} (same : Reply effect ≡ (Text ⊎ A)) →
  Observation effect → (next : A → Script Result) →
  (∀ value → OnlyReads (next value)) → OnlyReads (read effect same next)
readObservation effect {A} same witness next proofs = observation witness
  (λ reply → receiveProof (subst (λ X → X) same reply))
  where
  receiveProof : (response : Text ⊎ A) → OnlyReads (receiveRead next response)
  receiveProof (inj₁ detail) = noEffects (failed detail)
  receiveProof (inj₂ value) = proofs value

projectionIsReadOnly : ∀ outcome → OnlyReads (finishPropagation true outcome)
projectionIsReadOnly outcome with P.Result.numericFailure outcome
... | true = noEffects invalidNumericWrite
... | false = noEffects (projected (N.project (P.Result.writes outcome)) false)

calculationIsReadOnly : ∀ id value beliefs reviews ground incomingRows →
  OnlyReads (calculate true id value beliefs reviews ground incomingRows)
calculationIsReadOnly id value beliefs reviews ground incomingRows
  with prepare (concatMap Reviews.Review.feedbacks reviews) ground beliefs
... | nothing = noEffects invalidNumericInput
... | just nodes = readObservation (computeBeta true (just (id , value))
  (external (id ∷ map G.BeliefValues.identity beliefs) incomingRows) (calculationEdges true id incomingRows) nodes)
  refl tt _ projectionIsReadOnly

seedIsReadOnly : ∀ id value → OnlyReads (afterSeed true id value)
seedIsReadOnly id value = readObservation (descendants id true) refl tt _ λ beliefs →
  readObservation activeReviews refl tt _ λ reviews →
  readObservation groundingMasses refl tt _ λ ground →
  readObservation (incomingEdges (map G.BeliefValues.identity beliefs Data.List.++ (id ∷ []))) refl tt _
    (calculationIsReadOnly id value beliefs reviews ground)

interventionIsReadOnly : ∀ id value → OnlyReads (start (intervention id value))
interventionIsReadOnly id value with N.probability value
... | false = noEffects invalidProbability
... | true = readObservation (getBelief id) refl tt _ λ where
  nothing → noEffects missingBelief
  (just belief) → seedIsReadOnly id value

contradictionsAreReadOnly : ∀ project → OnlyReads (start (contradictions project))
contradictionsAreReadOnly project = readObservation (contradictionPairs project) refl tt _ λ where
  [] → noEffects (pairs [])
  candidates@(_ ∷ _) → readObservation (listBeliefs project) refl tt _
    (λ beliefs → noEffects (pairs (N.activeContradictions beliefs candidates)))

data ReadRequest : Set where
  interventionView : UUID → Float → ReadRequest
  contradictionsView : Maybe Text → ReadRequest

readStart : ReadRequest → ReadProtocol.Script Result
readStart (interventionView id value) = onlyReads (interventionIsReadOnly id value)
readStart (contradictionsView project) = onlyReads (contradictionsAreReadOnly project)

-- These statements describe private work inside an enclosing transaction.
-- Their worlds are not independently published business states.
data PrivateStep (before : Store.World) : (effect : Effect) → Reply effect → Store.World → Set where
  observed : ∀ {effect reply} → Observation effect → PrivateStep before effect reply before
  publicationFailed : ∀ {writes detail} → PrivateStep before (persistBeta writes) (inj₁ detail) before
  publication : ∀ {writes receipt after} →
    DB.Atomic before (Store.setNodes (L.apply writes (Store.nodes before)) before) receipt after →
    PrivateStep before (persistBeta writes) (inj₂ receipt) after

data PrivateRuns : Script Result → Store.World → List E.Event → Store.World → Result → Set where
  returned : ∀ result before → PrivateRuns (done result) before [] before result
  replied : ∀ effect next reply before middle events after result → PrivateStep before effect reply middle →
    PrivateRuns (next reply) middle events after result →
    PrivateRuns (ask effect next) before ((effect , reply) ∷ events) after result

privateStepPreservesLinks : ∀ {before effect reply after} → PrivateStep before effect reply after →
  Store.edges after ≡ Store.edges before
privateStepPreservesLinks (observed _) = refl
privateStepPreservesLinks publicationFailed = refl
privateStepPreservesLinks (publication DB.committedAll) = refl
privateStepPreservesLinks (publication DB.abortedNone) = refl

privateCalculationPreservesLinks : ∀ {script before events after result} →
  PrivateRuns script before events after result → Store.edges after ≡ Store.edges before
privateCalculationPreservesLinks (returned result before) = refl
privateCalculationPreservesLinks (replied effect next reply before middle events after result statement rest) =
  trans (privateCalculationPreservesLinks rest) (privateStepPreservesLinks statement)

Successful : Result → Set
Successful (propagated _ false) = ⊤
Successful (projected _ false) = ⊤
Successful (changed _) = ⊤
Successful (deleted _) = ⊤
Successful (pairs _) = ⊤
Successful _ = ⊥

-- Preparation may read prerequisites, but all writes form one final
-- transaction. In particular it cannot publish and subsequently fail.
data OnePublication : Script Result → Set where
  finished : ∀ result → OnePublication (done result)
  observing : ∀ {effect next} → Observation effect →
    (∀ reply → OnePublication (next reply)) → OnePublication (ask effect next)
  posteriors : ∀ writes result → Successful result → OnePublication (persist writes result)
  selection : ∀ ids → OnePublication (sweepDeletes ids)

data Publication : Set where
  update : (writes : P.State) → (result : Result) → Successful result → Publication
  removeSelection : List UUID → Publication

data Preparation : Set where
  noPublication : Result → Preparation
  publish : Publication → Preparation

prepareOne : ∀ {program} → OnePublication program → ReadProtocol.Script Preparation
prepareOne (finished result) = ReadProtocol.done (noPublication result)
prepareOne (observing {effect = effect} witness next) =
  ReadProtocol.ask (effect , witness) (λ reply → prepareOne (next reply))
prepareOne (posteriors writes result success) with L.validWrites writes
... | false = ReadProtocol.done (noPublication invalidNumericWrite)
... | true = ReadProtocol.done (publish (update writes result success))
prepareOne (selection []) = ReadProtocol.done (noPublication (deleted 0))
prepareOne (selection ids@(_ ∷ _)) = ReadProtocol.done (publish (removeSelection ids))

readOne : (effect : Effect) → ∀ {A} (same : Reply effect ≡ (Text ⊎ A)) →
  Observation effect → (next : A → Script Result) →
  (∀ value → OnePublication (next value)) → OnePublication (read effect same next)
readOne effect {A} same witness next proofs = observing witness
  (λ reply → receiveProof (subst (λ X → X) same reply))
  where
  receiveProof : (response : Text ⊎ A) → OnePublication (receiveRead next response)
  receiveProof (inj₁ detail) = finished (failed detail)
  receiveProof (inj₂ value) = proofs value

finishHasOnePublication : ∀ causal outcome → OnePublication (finishPropagation causal outcome)
finishHasOnePublication causal outcome with P.Result.numericFailure outcome
... | true = finished invalidNumericWrite
... | false with causal
...   | true = finished (projected (N.project (P.Result.writes outcome)) false)
...   | false = posteriors (P.Result.writes outcome) (propagated (N.project (P.Result.writes outcome)) false) tt

calculationHasOnePublication : ∀ causal id value beliefs reviews ground incomingRows →
  OnePublication (calculate causal id value beliefs reviews ground incomingRows)
calculationHasOnePublication causal id value beliefs reviews ground incomingRows
  with prepare (concatMap Reviews.Review.feedbacks reviews) ground beliefs
... | nothing = finished invalidNumericInput
... | just nodes = readOne (computeBeta causal (just (id , value))
  (external (id ∷ map G.BeliefValues.identity beliefs) incomingRows) (calculationEdges causal id incomingRows) nodes)
  refl tt _ (finishHasOnePublication causal)

seedHasOnePublication : ∀ causal id value → OnePublication (afterSeed causal id value)
seedHasOnePublication causal id value = readOne (descendants id causal) refl tt _ λ beliefs →
  readOne activeReviews refl tt _ λ reviews → readOne groundingMasses refl tt _ λ ground →
  readOne (incomingEdges (map G.BeliefValues.identity beliefs Data.List.++ (id ∷ []))) refl tt _
    (calculationHasOnePublication causal id value beliefs reviews ground)

durationHasOnePublication : ∀ threshold edges beliefs now grace →
  OnePublication (afterDuration threshold edges beliefs now grace)
durationHasOnePublication threshold edges beliefs now nothing = finished durationOutOfRange
durationHasOnePublication threshold edges beliefs now (just grace) = observing {effect = hashIteration _} tt
  (λ { (order , sameMembers) → selection (N.expiredTargets now grace threshold beliefs edges order) })

startHasOnePublication : ∀ request → OnePublication (start request)
startHasOnePublication (propagate id) = readOne (getBelief id) refl tt _ λ where
  nothing → finished missingBelief
  (just belief) → seedHasOnePublication false id (G.BeliefValues.probability belief)
startHasOnePublication (intervention id value) with N.probability value
... | false = finished invalidProbability
... | true = readOne (getBelief id) refl tt _ λ where
  nothing → finished missingBelief
  (just belief) → seedHasOnePublication true id value
startHasOnePublication (decay project factor) = readOne (listBeliefs project) refl tt _ λ beliefs →
  readOne groundingMasses refl tt _ λ ground → observing {effect = clock} tt λ now → decide beliefs ground now
  where
  decide : ∀ beliefs ground now → OnePublication (decayDecision factor beliefs ground now)
  decide beliefs ground now with N.decay now factor ground beliefs
  ... | nothing = finished invalidDecay
  ... | just writes = posteriors writes (changed (length writes)) tt
startHasOnePublication (contradictions project) = readOne (contradictionPairs project) refl tt _ λ where
  [] → finished (pairs [])
  candidates@(_ ∷ _) → readOne (listBeliefs project) refl tt _
    (λ beliefs → finished (pairs (N.activeContradictions beliefs candidates)))
startHasOnePublication (sweep project threshold grace) = readOne (defeatTimes project) refl tt _ λ where
  [] → finished (deleted 0)
  edges@(_ ∷ _) → readOne (listBeliefs project) refl tt _ λ beliefs →
    observing {effect = clock} tt λ now → observing {effect = hashIteration _} tt
      (λ { (order , sameMembers) → selection (N.expiredTargets now grace threshold beliefs edges order) })
startHasOnePublication (sweepHours project threshold hours) = readOne (defeatTimes project) refl tt _ λ where
  [] → finished (deleted 0)
  edges@(_ ∷ _) → readOne (listBeliefs project) refl tt _ λ beliefs →
    observing {effect = clock} tt λ now → observing {effect = convertGraceHours hours} tt
      (durationHasOnePublication threshold edges beliefs now)

prepareRequest : Request → ReadProtocol.Script Preparation
prepareRequest request = prepareOne (startHasOnePublication request)
