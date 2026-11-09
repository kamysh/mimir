{-# OPTIONS --safe #-}
-- The graph-sized traversal bound is sufficient, including cycles and
-- duplicate rows. Its measure counts carrier entries not yet visited.
module Mimir.TraversalCompleteness where

import Data.Bool
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_; map; filter; length)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Membership.Propositional.Properties as Membership
import Data.List.Properties as Lists
open import Data.List.Relation.Unary.Any using (Any; here; there)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All.Properties as AllProperties
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _≟_)
import Data.Nat.Properties as Nat
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst; trans)
open import Mimir.Text using (Text)
import Mimir.LearningTargets as Targets
import Mimir.ReviewEdges as Edges
import Mimir.ReviewRecomputeTraversal as Traversal
import Mimir.ApplicationStore as Store
import Mimir.CandidateGraph as Graph
import Mimir.RetrievalRanking as Ranking
import Mimir.StorageReadBinding as Database
import Mimir.PreparedRetrieval as Prepared
import Mimir.LearningRecompute as Recompute
import Mimir.LearningStore as Learning
import Mimir.ReviewPreparationPublication as Publication

module Filters (P Q : ℕ → Set) (p? : ∀ x → Dec (P x)) (q? : ∀ x → Dec (Q x))
  (implies : ∀ {x} → Q x → P x) where
  nested : ∀ rows → filter q? rows ≡ filter q? (filter p? rows)
  nested [] = refl
  nested (x ∷ xs) with p? x | q? x
  ... | yes earlier | yes later = trans (cong (x ∷_) (nested xs))
    (sym (Lists.filter-accept q? later))
  ... | yes earlier | no later = trans (nested xs) (sym (Lists.filter-reject q? later))
  ... | no earlier | yes later = ⊥-elim (earlier (implies later))
  ... | no earlier | no later = nested xs

module For (project : Maybe Text) (beliefs : List Targets.Belief) (edges : List Edges.Edge) where
  module T = Traversal.For project beliefs edges
  open Traversal using (State; state)

  carrier = map Targets.Belief.identity beliefs

  lookupPresent : ∀ identity rows →
    Traversal.InScope project (Targets.lookup identity rows) →
    identity ∈ map Targets.Belief.identity rows
  lookupPresent identity [] ()
  lookupPresent identity (b ∷ rest) owned with identity ≟ Targets.Belief.identity b
  ... | yes same = here same
  ... | no _ = there (lookupPresent identity rest owned)

  remaining : State → List ℕ
  remaining before = filter (T.fresh? (State.visited before)) carrier

  nested : ∀ old new rows →
    filter (T.fresh? (new ++ old)) rows ≡
    filter (T.fresh? (new ++ old)) (filter (T.fresh? old) rows)
  nested old new = Filters.nested _ _ (T.fresh? old) (T.fresh? (new ++ old))
    (λ later member → later (Membership.∈-++⁺ʳ new member))

  witness : ∀ {P : ℕ → Set} {x xs} → x ∈ xs → P x → Any P xs
  witness (here refl) proof = here proof
  witness (there member) proof = there (witness member proof)

  decreases : ∀ before x → x ∈ T.next before →
    length (remaining (T.advance before)) < length (remaining before)
  decreases before x member = subst
    (λ rows → length rows < length (remaining before))
    (sym (nested (State.visited before) (T.next before) carrier))
    (Lists.filter-notAll (T.fresh? (State.visited (T.advance before))) (remaining before)
      (witness (Membership.∈-filter⁺ (T.fresh? (State.visited before))
        (lookupPresent x beliefs (All.lookup (T.nextOwned before) member))
        (All.lookup (T.nextFresh before) member))
        (λ fresh → fresh (T.discoveredRetained before x member))))

  emptyStaysEmpty : ∀ fuel visited → State.frontier (T.expand fuel (state visited [])) ≡ []
  emptyStaysEmpty zero visited = refl
  emptyStaysEmpty (suc fuel) visited = refl

  exhausts : ∀ budget before → length (remaining before) ≤ budget →
    State.frontier (T.expand (suc budget) before) ≡ []
  exhausts budget (state visited []) bound = refl
  exhausts zero before@(state visited (_ ∷ _)) bound with T.next before | decreases before
  ... | [] | progress = refl
  ... | x ∷ xs | progress = ⊥-elim (Nat.n≮0 (Nat.≤-trans (progress x (here refl)) bound))
  exhausts (suc budget) before@(state visited (_ ∷ _)) bound with T.next before | decreases before
  ... | [] | progress = emptyStaysEmpty (suc budget) visited
  ... | x ∷ xs | progress = exhausts budget (state ((x ∷ xs) ++ visited) (x ∷ xs))
    (Nat.≤-pred (Nat.≤-trans (progress x (here refl)) bound))

  graphSizedExhausts : ∀ seeds →
    State.frontier (T.expand (suc (length beliefs)) (T.start seeds)) ≡ []
  graphSizedExhausts seeds = exhausts (length beliefs) (T.start seeds)
    (subst (λ n → length (remaining (T.start seeds)) ≤ n)
      (Lists.length-map Targets.Belief.identity beliefs)
      (Lists.length-filter (T.fresh? seeds) carrier))

  retained : ∀ fuel before identity → identity ∈ State.visited before →
    identity ∈ State.visited (T.expand fuel before)
  retained zero before identity member = member
  retained (suc fuel) (state visited []) identity member = member
  retained (suc fuel) before@(state visited (_ ∷ _)) identity member =
    retained fuel (T.advance before) identity (T.visitedRetained before identity member)

  accounted : ∀ fuel before → T.Accounted before → T.Accounted (T.expand fuel before)
  accounted zero before proof = proof
  accounted (suc fuel) (state visited []) proof = proof
  accounted (suc fuel) before@(state visited (_ ∷ _)) proof =
    accounted fuel (T.advance before) (T.advanceAccounted before proof)

  owned : ∀ fuel before → All T.Owned (State.visited before) →
    All T.Owned (State.visited (T.expand fuel before))
  owned zero before proof = proof
  owned (suc fuel) (state visited []) proof = proof
  owned (suc fuel) before@(state visited (_ ∷ _)) proof =
    owned fuel (T.advance before) (T.scopedVisitedPreserved before proof)

  reached : ∀ seeds fuel before → All (T.Reached seeds) (State.visited before) →
    All (T.Reached seeds) (State.frontier before) →
    All (T.Reached seeds) (State.visited (T.expand fuel before))
  reached seeds zero before visited frontier = visited
  reached seeds (suc fuel) (state visited []) proof frontier = proof
  reached seeds (suc fuel) before@(state visited (_ ∷ _)) proof frontier =
    reached seeds fuel (T.advance before)
      (AllProperties.++⁺ (T.nextReached seeds before frontier) proof)
      (T.nextReached seeds before frontier)

  closure : List ℕ → List ℕ
  closure seeds = State.visited (T.expand (suc (length beliefs)) (T.start seeds))

  complete : ∀ seeds identity → T.Reached seeds identity → identity ∈ closure seeds
  complete seeds = T.allReachableIncluded seeds (closure seeds)
    (All.tabulate (retained (suc (length beliefs)) (T.start seeds) _))
    (T.exhaustedClosed (closure seeds)
      (subst (λ frontier → T.Accounted (state (closure seeds) frontier))
        (graphSizedExhausts seeds)
        (accounted (suc (length beliefs)) (T.start seeds) (T.initiallyAccounted seeds))))

  sound : ∀ seeds → All (T.Reached seeds) (closure seeds)
  sound seeds = reached seeds (suc (length beliefs)) (T.start seeds)
    (All.tabulate T.root) (All.tabulate T.root)

  noForeignIdentity : ∀ seeds → All T.Owned seeds → All T.Owned (closure seeds)
  noForeignIdentity seeds = owned (suc (length beliefs)) (T.start seeds)

-- Bind the finite-carrier result to the actual world-derived selector.
module PreparedSearch (arithmetic : Ranking.F32) (unicode : Ranking.Unicode)
  (database : Database.VectorOperations) (request : Prepared.Input)
  (world : Store.World) (query : Prepared.PreparedVector) where
  module P = Prepared.Intent arithmetic unicode database
  nodes = P.carrier request world
  edges = Publication.World.edges (Learning.World.publication (Store.World.learning world))
  seeds = P.seeds request world query
  module C = For nothing (map Recompute.target nodes) edges

  private
    justEqual : ∀ {A : Set} {a b : A} → just a ≡ just b → a ≡ b
    justEqual refl = refl

    lookupStored : ∀ identity rows b → Ranking.lookup identity rows ≡ just b → b ∈ rows
    lookupStored identity [] b ()
    lookupStored identity (first ∷ rest) b same with identity ≟ Graph.BeliefValues.identity first
    ... | yes _ = subst (_∈ (first ∷ rest)) (justEqual same) (here refl)
    ... | no _ = there (lookupStored identity rest b same)

    materializedStored : ∀ identities rows →
      All (λ b → b ∈ rows) (Ranking.materialize identities rows)
    materializedStored [] rows = All.[]
    materializedStored (identity ∷ rest) rows with Ranking.lookup identity rows in found
    ... | nothing = materializedStored rest rows
    ... | just b = lookupStored identity rows b found All.∷ materializedStored rest rows

    filteredStored : ∀ {A : Set} predicate (rows : List A) →
      All (λ b → b ∈ rows) (Data.List.filterᵇ predicate rows)
    filteredStored predicate [] = All.[]
    filteredStored predicate (b ∷ rows) with predicate b
    ... | Data.Bool.false = All.map there (filteredStored predicate rows)
    ... | Data.Bool.true = here refl All.∷ All.map there (filteredStored predicate rows)

    candidateInCarrier : ∀ b → b ∈ P.candidates request world → b ∈ nodes
    candidateInCarrier b member with Prepared.Input.project request |
      All.lookup (filteredStored (P.eligible request world) (Store.beliefs world)) member
    ... | nothing | stored = stored
    ... | just _ | stored = member

    inCarrierOwned : ∀ identity rows → identity ∈ map Graph.BeliefValues.identity rows →
      Traversal.InScope nothing (Targets.lookup identity (map Recompute.target rows))
    inCarrierOwned identity [] ()
    inCarrierOwned identity (b ∷ rows) member with identity ≟ Graph.BeliefValues.identity b
    ... | yes _ = tt
    ... | no different with member
    ...   | here same = ⊥-elim (different same)
    ...   | there later = inCarrierOwned identity rows later

  seedsFromCarrier : All C.T.Owned seeds
  seedsFromCarrier = AllProperties.map⁺ (All.map
    (λ {b} member → inCarrierOwned (Graph.BeliefValues.identity b) nodes
      (Membership.∈-map⁺ Graph.BeliefValues.identity (candidateInCarrier b member)))
    (materializedStored (Ranking.unique (P.lexical request world ++ P.vectors request world query))
      (P.candidates request world)))

  selectedClosure = Recompute.closureScoped nothing nodes edges seeds

  sameClosure : C.closure seeds ≡ selectedClosure
  sameClosure = cong (λ count → Traversal.State.visited
    (C.T.expand (suc count) (C.T.start seeds))) (Lists.length-map Recompute.target nodes)

  everyAllowedReachableIdentityIncluded : ∀ identity → C.T.Reached seeds identity → identity ∈ selectedClosure
  everyAllowedReachableIdentityIncluded identity reached =
    subst (identity ∈_) sameClosure (C.complete seeds identity reached)

  noForeignCarrierIdentityReturned : All (λ identity → identity ∈ map Graph.BeliefValues.identity nodes) selectedClosure
  noForeignCarrierIdentityReturned = subst
    (All (λ identity → identity ∈ map Graph.BeliefValues.identity nodes)) sameClosure
    (All.map (λ {identity} owned → subst (identity ∈_)
      (sym (Lists.map-∘ {g = Targets.Belief.identity} {f = Recompute.target} nodes))
      (C.lookupPresent identity (map Recompute.target nodes) owned))
      (C.noForeignIdentity seeds seedsFromCarrier))

  everyReturnedIdentityReachable : All (C.T.Reached seeds) selectedClosure
  everyReturnedIdentityReachable = subst (All (C.T.Reached seeds)) sameClosure (C.sound seeds)
