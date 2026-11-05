{-# OPTIONS --safe #-}
-- Learning-specific posterior inputs and writes. All arithmetic uses standard
-- Float; application state, traversal and evidence selection are concrete.
module Mimir.LearningRecompute where

open import Data.Float.Base using (Float; _+_; _*_)
open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.List using (List; []; _∷_; _++_; map; length; concatMap)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Mimir.Text using (Text; member)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.CandidateGraph as Graph
import Mimir.LearningTargets as Targets
import Mimir.ReviewEdges as Edges
import Mimir.ReviewSchema as Review
import Mimir.ReviewLedger as Ledger
import Mimir.ReviewRecomputeTraversal as Traversal
import Mimir.ApplicationFloat as Numeric
import Mimir.PosteriorComputation as Posterior
import Mimir.EvidenceValidity as Evidence

beliefs : List Graph.Node → List Graph.BeliefValues
beliefs [] = []
beliefs (Graph.patternNode p ∷ ns) = beliefs ns
beliefs (Graph.beliefNode b ∷ ns) = b ∷ beliefs ns

target : Graph.BeliefValues → Targets.Belief
target b = Targets.belief (Graph.BeliefValues.identity b)
  (Graph.BeliefValues.project b) (Graph.BeliefValues.memory b)

-- A finite graph has no new reachable vertex beyond its vertex count of
-- frontier expansions. Include one extra expansion for retired initial roots.
closureScoped : Maybe Text → List Graph.BeliefValues → List Edges.Edge → List ℕ → List ℕ
closureScoped project nodes edges roots = Traversal.State.visited
  (expand (suc (length nodes)) (Traversal.state roots roots))
  where
  module T = Traversal.For project (map target nodes) edges
  expand : ℕ → Traversal.State → Traversal.State
  expand zero current = current
  expand (suc fuel) current with Traversal.State.frontier current
  ... | [] = current
  ... | _ ∷ _ = expand fuel (T.advance current)

closure : Text → List Graph.BeliefValues → List Edges.Edge → List ℕ → List ℕ
closure project = closureScoped (just project)

selected : List ℕ → List Graph.BeliefValues → List Graph.BeliefValues
selected ids [] = []
selected ids (b ∷ bs) with member (Graph.BeliefValues.identity b) ids
... | true = b ∷ selected ids bs
... | false = selected ids bs

owned : Text → List Graph.BeliefValues → Bool
owned project [] = true
owned project (b ∷ bs) with Graph.BeliefValues.project b
... | nothing = false
... | just actual = does (actual ≟Text project) ∧ owned project bs

activeReviews : Text → List ℕ → Ledger.World → List Review.Review
activeReviews project [] ledger = []
activeReviews project (id ∷ ids) ledger with
  does (Ledger.R.Cell.project (Ledger.World.cells ledger id) ≟Text project)
... | false = activeReviews project ids ledger
... | true with Ledger.activeApplied (Ledger.World.cells ledger id) (Ledger.World.histories ledger id)
...   | nothing = activeReviews project ids ledger
...   | just applied = applied ∷ activeReviews project ids ledger

feedbackMass : ℕ → List Review.Feedback → Posterior.Beta → Maybe Posterior.Beta
feedbackMass id [] total = just total
feedbackMass id (f ∷ fs) total with id ≟ Review.Feedback.beliefID f
... | no different = feedbackMass id fs total
... | yes same with Numeric.number (Review.Feedback.weight f)
...   | nothing = nothing
...   | just weight with Review.Feedback.verdict f
...     | Review.support = feedbackMass id fs
  (Posterior.beta (Posterior.Beta.alpha total + weight * 4.0) (Posterior.Beta.negative total))
...     | Review.defeat = feedbackMass id fs
  (Posterior.beta (Posterior.Beta.alpha total) (Posterior.Beta.negative total + weight * 4.0))

groundMass : ℕ → List (ℕ × Float) → Float → Float
groundMass id [] total = total
groundMass id ((key , weight) ∷ rest) total with id ≟ key
... | yes same = groundMass id rest (total + weight)
... | no different = groundMass id rest total

prepareNodes : List Review.Feedback → List (ℕ × Float) → List Graph.BeliefValues → Maybe (List Posterior.Node)
prepareNodes feedback ground [] = just []
prepareNodes feedback ground (b ∷ bs) with feedbackMass (Graph.BeliefValues.identity b) feedback (Posterior.beta 0.0 0.0)
  | prepareNodes feedback ground bs
... | nothing | _ = nothing
... | just mass | nothing = nothing
... | just mass | just rest with Evidence.validBelief b
...   | false = nothing
...   | true = just (Posterior.node (Graph.BeliefValues.identity b)
  (Posterior.beta
    (Graph.BeliefValues.alpha0 b + (Posterior.Beta.alpha mass + 1.0 * groundMass (Graph.BeliefValues.identity b) ground 0.0))
    (Graph.BeliefValues.beta0 b + Posterior.Beta.negative mass))
  (Posterior.beta (Graph.BeliefValues.alpha b) (Graph.BeliefValues.beta b)) ∷ rest)

prepareEdges : List ℕ → List Edges.Edge → Maybe (List Posterior.Edge)
prepareEdges targets [] = just []
prepareEdges targets (e ∷ es) with member (Edges.Edge.to e) targets
... | false = prepareEdges targets es
... | true with Numeric.number (Edges.Edge.weight e) | prepareEdges targets es
...   | just weight | just rest = just (Posterior.edge (Edges.Edge.from e) (Edges.Edge.to e)
  (Edges.Edge.relation e) weight ∷ rest)
...   | _ | _ = nothing

external : List ℕ → List Graph.BeliefValues → Posterior.External
external ids [] = []
external ids (b ∷ bs) with member (Graph.BeliefValues.identity b) ids
... | true = external ids bs
... | false = (Graph.BeliefValues.identity b , Graph.BeliefValues.probability b) ∷ external ids bs

validWrites : Posterior.State → Bool
validWrites = Posterior.validState

apply : Posterior.State → List Graph.Node → List Graph.Node
apply changes [] = []
apply changes (Graph.patternNode p ∷ ns) = Graph.patternNode p ∷ apply changes ns
apply changes (Graph.beliefNode b ∷ ns) with Posterior.lookup (Graph.BeliefValues.identity b) changes
... | nothing = Graph.beliefNode b ∷ apply changes ns
... | just value = Graph.beliefNode (Evidence.updated b value) ∷ apply changes ns

applyPreservesValidity : ∀ changes nodes → Posterior.ValidState changes →
  All Evidence.ValidNode nodes → All Evidence.ValidNode (apply changes nodes)
applyPreservesValidity changes [] writes [] = []
applyPreservesValidity changes (Graph.patternNode p ∷ ns) writes (valid ∷ tail) =
  valid ∷ applyPreservesValidity changes ns writes tail
applyPreservesValidity changes (Graph.beliefNode b ∷ ns) writes (valid ∷ tail)
  with Posterior.lookup (Graph.BeliefValues.identity b) changes in found
... | nothing = valid ∷ applyPreservesValidity changes ns writes tail
... | just value = Evidence.updatedValid b value valid
  (Evidence.lookupValid (Graph.BeliefValues.identity b) changes value writes found) ∷
  applyPreservesValidity changes ns writes tail

originals : List Graph.Node → List (ℕ × (Float × Float))
originals [] = []
originals (Graph.patternNode p ∷ rest) = originals rest
originals (Graph.beliefNode b ∷ rest) =
  (Graph.BeliefValues.identity b , Graph.BeliefValues.alpha0 b , Graph.BeliefValues.beta0 b) ∷ originals rest

applyPreservesOriginals : ∀ changes nodes → originals (apply changes nodes) ≡ originals nodes
applyPreservesOriginals changes [] = refl
applyPreservesOriginals changes (Graph.patternNode p ∷ rest) = applyPreservesOriginals changes rest
applyPreservesOriginals changes (Graph.beliefNode b ∷ rest)
  with Posterior.lookup (Graph.BeliefValues.identity b) changes
... | nothing = cong ((Graph.BeliefValues.identity b , Graph.BeliefValues.alpha0 b , Graph.BeliefValues.beta0 b) ∷_)
  (applyPreservesOriginals changes rest)
... | just value = cong ((Graph.BeliefValues.identity b , Graph.BeliefValues.alpha0 b , Graph.BeliefValues.beta0 b) ∷_)
  (applyPreservesOriginals changes rest)

data Result : Set where
  foreignTarget invalidNumericInput invalidNumericWrite : Result
  recomputed : List Graph.Node → Bool → Result

finish : List Graph.Node → Posterior.Result → Result
finish nodes r with not (Posterior.Result.numericFailure r) ∧ validWrites (Posterior.Result.writes r)
... | false = invalidNumericWrite
... | true = recomputed (apply (Posterior.Result.writes r) nodes)
  (Posterior.Result.iterationLimitReached r)

finishPreservesValidity : ∀ nodes r after limit → All Evidence.ValidNode nodes →
  finish nodes r ≡ recomputed after limit → All Evidence.ValidNode after
finishPreservesValidity nodes r after limit valid observed
  with not (Posterior.Result.numericFailure r) ∧ validWrites (Posterior.Result.writes r) in admitted
... | false with observed
...   | ()
finishPreservesValidity nodes r after limit valid refl | true =
  applyPreservesValidity (Posterior.Result.writes r) nodes
    (Posterior.validStateSound (Posterior.Result.writes r)
      (Posterior.andRight (not (Posterior.Result.numericFailure r)) (validWrites (Posterior.Result.writes r)) admitted)) valid

failedCalculationCannotSucceed : ∀ nodes r → Posterior.Result.numericFailure r ≡ true →
  finish nodes r ≡ invalidNumericWrite
failedCalculationCannotSucceed nodes r failed rewrite failed = refl

run : Text → List ℕ → List Graph.Node → List Edges.Edge →
  List Review.Review → List (ℕ × Float) → Result
run project roots nodes edges reviews ground with owned project chosen
  where chosen = selected (closure project (beliefs nodes) edges roots) (beliefs nodes)
... | false = foreignTarget
... | true with prepareNodes (concatMap Review.Review.feedbacks reviews) ground chosen
  | prepareEdges (map Graph.BeliefValues.identity chosen) edges
  where chosen = selected (closure project (beliefs nodes) edges roots) (beliefs nodes)
...   | nothing | _ = invalidNumericInput
...   | just prepared | nothing = invalidNumericInput
...   | just prepared | just incoming = finish nodes
  (Posterior.run nothing (external (map Posterior.Node.identity prepared) (beliefs nodes)) incoming prepared)

runPreservesValidity : ∀ project roots nodes edges reviews ground after limit →
  All Evidence.ValidNode nodes → run project roots nodes edges reviews ground ≡ recomputed after limit →
  All Evidence.ValidNode after
runPreservesValidity project roots nodes edges reviews ground after limit valid observed
  with owned project (selected (closure project (beliefs nodes) edges roots) (beliefs nodes))
... | false with observed
...   | ()
runPreservesValidity project roots nodes edges reviews ground after limit valid observed | true
  with prepareNodes (concatMap Review.Review.feedbacks reviews) ground chosen
  | prepareEdges (map Graph.BeliefValues.identity chosen) edges
  where chosen = selected (closure project (beliefs nodes) edges roots) (beliefs nodes)
... | nothing | _ with observed
...   | ()
runPreservesValidity project roots nodes edges reviews ground after limit valid observed | true | just prepared | nothing with observed
... | ()
runPreservesValidity project roots nodes edges reviews ground after limit valid observed | true | just prepared | just incoming =
  finishPreservesValidity nodes
    (Posterior.run nothing (external (map Posterior.Node.identity prepared) (beliefs nodes)) incoming prepared)
    after limit valid observed

identitiesPreserved : ∀ changes nodes → map Graph.nodeID (apply changes nodes) ≡ map Graph.nodeID nodes
identitiesPreserved changes [] = refl
identitiesPreserved changes (Graph.patternNode p ∷ ns) = cong (Graph.PatternValues.identity p ∷_) (identitiesPreserved changes ns)
identitiesPreserved changes (Graph.beliefNode b ∷ ns) with Posterior.lookup (Graph.BeliefValues.identity b) changes
... | nothing = cong (Graph.BeliefValues.identity b ∷_)
  (identitiesPreserved changes ns)
... | just value = cong (Graph.BeliefValues.identity b ∷_)
  (identitiesPreserved changes ns)

finishPreservesIdentities : ∀ nodes r after limit → finish nodes r ≡ recomputed after limit →
  map Graph.nodeID after ≡ map Graph.nodeID nodes
finishPreservesIdentities nodes r after limit proof with not (Posterior.Result.numericFailure r) ∧ validWrites (Posterior.Result.writes r)
... | false with proof
...   | ()
finishPreservesIdentities nodes r after limit refl | true = identitiesPreserved (Posterior.Result.writes r) nodes

runPreservesIdentities : ∀ project roots nodes edges reviews ground after limit →
  run project roots nodes edges reviews ground ≡ recomputed after limit →
  map Graph.nodeID after ≡ map Graph.nodeID nodes
runPreservesIdentities project roots nodes edges reviews ground after limit proof
  with owned project (selected (closure project (beliefs nodes) edges roots) (beliefs nodes))
... | false with proof
...   | ()
runPreservesIdentities project roots nodes edges reviews ground after limit proof | true
  with prepareNodes (concatMap Review.Review.feedbacks reviews) ground chosen
  | prepareEdges (map Graph.BeliefValues.identity chosen) edges
  where chosen = selected (closure project (beliefs nodes) edges roots) (beliefs nodes)
... | nothing | _ with proof
...   | ()
runPreservesIdentities project roots nodes edges reviews ground after limit proof | true | just prepared | nothing with proof
... | ()
runPreservesIdentities project roots nodes edges reviews ground after limit proof | true | just prepared | just incoming = finishPreservesIdentities nodes
  (Posterior.run nothing
   (external (map Posterior.Node.identity prepared) (beliefs nodes))
   incoming prepared)
  after limit proof

-- Identity deletion has no project restriction. It uses the same numerical
-- update but includes current reviews and descendants from every project.
activeReviewsScoped : Maybe Text → List ℕ → Ledger.World → List Review.Review
activeReviewsScoped (just project) ids ledger = activeReviews project ids ledger
activeReviewsScoped nothing [] ledger = []
activeReviewsScoped nothing (id ∷ ids) ledger with Ledger.activeApplied
  (Ledger.World.cells ledger id) (Ledger.World.histories ledger id)
... | nothing = activeReviewsScoped nothing ids ledger
... | just applied = applied ∷ activeReviewsScoped nothing ids ledger

runGlobal : List ℕ → List Graph.Node → List Edges.Edge →
  List Review.Review → List (ℕ × Float) → Result
runGlobal roots nodes edges reviews ground with prepareNodes (concatMap Review.Review.feedbacks reviews) ground chosen
  | prepareEdges (map Graph.BeliefValues.identity chosen) edges
  where chosen = selected (closureScoped nothing (beliefs nodes) edges roots) (beliefs nodes)
... | nothing | _ = invalidNumericInput
... | just prepared | nothing = invalidNumericInput
... | just prepared | just incoming = finish nodes
  (Posterior.run nothing (external (map Posterior.Node.identity prepared) (beliefs nodes)) incoming prepared)
