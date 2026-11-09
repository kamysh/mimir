{-# OPTIONS --safe #-}
-- One database-backed frontier expansion in recompute_learning. The adapter
-- must provide the actual graph snapshot. Initial roots may include retired
-- targets; only live target beliefs are discovered by following edges.
-- TraversalCompleteness proves the finite expansion reaches every allowed
-- connection. The posterior write plan is a separate obligation.
module Mimir.ReviewRecomputeTraversal where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_; map; filter; deduplicate)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Membership.Propositional.Properties as Membership
import Data.List.Properties as Lists
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.All.Properties as AllProperties
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (_×-dec_; ¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Mimir.Text using (Text)
open import Mimir.ReviewSchema using (Relation; supports; defeats; causes; contradicts)
open import Mimir.Validation using (accepted; rejected)
import Mimir.CandidateRegistry as Registry
import Mimir.LearningTargets as Targets
import Mimir.ReviewEdges as Edges

Carries : Relation → Set
Carries supports = ⊤
Carries defeats = ⊤
Carries causes = ⊤
Carries contradicts = ⊥

carries? : ∀ relation → Dec (Carries relation)
carries? supports = yes tt
carries? defeats = yes tt
carries? causes = yes tt
carries? contradicts = no (λ ())

InScope : Maybe Text → Maybe Targets.Belief → Set
InScope project nothing = ⊥
InScope nothing (just found) = ⊤
InScope (just project) (just found) = Targets.ExactProject project (Targets.Belief.project found)

inScope? : ∀ project found → Dec (InScope project found)
inScope? project nothing = no (λ ())
inScope? nothing (just found) = yes tt
inScope? (just project) (just found) with Targets.checkProject project (Targets.Belief.project found)
... | accepted owned = yes owned
... | rejected failure foreign = no foreign

record State : Set where
  constructor state
  field visited frontier : List ℕ

module For (project : Maybe Text) (beliefs : List Targets.Belief) (edges : List Edges.Edge) where

  Owned : ℕ → Set
  Owned identity = InScope project (Targets.lookup identity beliefs)

  Eligible : List ℕ → Edges.Edge → Set
  Eligible frontier e = Edges.Edge.from e ∈ frontier ×
    (Carries (Edges.Edge.relation e) × Owned (Edges.Edge.to e))

  eligible? : ∀ frontier e → Dec (Eligible frontier e)
  eligible? frontier e = Registry.IDs.present? (Edges.Edge.from e) frontier ×-dec
    (carries? (Edges.Edge.relation e) ×-dec inScope? project (Targets.lookup (Edges.Edge.to e) beliefs))

  destinations : List ℕ → List ℕ
  destinations frontier = map Edges.Edge.to (filter (eligible? frontier) edges)

  fresh? : ∀ visited identity → Dec (identity ∈ visited → ⊥)
  fresh? visited identity = ¬? (Registry.IDs.present? identity visited)

  next : State → List ℕ
  next before = filter (fresh? (State.visited before)) (deduplicate _≟_ (destinations (State.frontier before)))

  advance : State → State
  advance before = state (next before ++ State.visited before) (next before)

  -- The same finite expansion used by closureScoped, exposed so its
  -- exhaustion can be established rather than assumed at the call site.
  expand : ℕ → State → State
  expand zero current = current
  expand (suc fuel) current with State.frontier current
  ... | [] = current
  ... | _ ∷ _ = expand fuel (advance current)

  destinationsOwned : ∀ frontier → All Owned (destinations frontier)
  destinationsOwned frontier = AllProperties.map⁺
    (All.map (λ eligible → proj₂ (proj₂ eligible))
     (AllProperties.all-filter (eligible? frontier) edges))

  nextOwned : ∀ before → All Owned (next before)
  nextOwned before = AllProperties.filter⁺ (fresh? (State.visited before))
    (AllProperties.deduplicate⁺ _≟_
     (destinationsOwned (State.frontier before)))

  nextFresh : ∀ before → All (λ identity → identity ∈ State.visited before → ⊥) (next before)
  nextFresh before = AllProperties.all-filter (fresh? (State.visited before))
    (deduplicate _≟_ (destinations (State.frontier before)))

  visitedRetained : ∀ before identity → identity ∈ State.visited before → identity ∈ State.visited (advance before)
  visitedRetained before identity member = Membership.∈-++⁺ʳ (next before) member

  discoveredRetained : ∀ before identity → identity ∈ next before → identity ∈ State.visited (advance before)
  discoveredRetained before identity member = Membership.∈-++⁺ˡ member

  scopedVisitedPreserved : ∀ before → All Owned (State.visited before) → All Owned (State.visited (advance before))
  scopedVisitedPreserved before owned = AllProperties.++⁺ (nextOwned before) owned

  nextSound : ∀ before identity → identity ∈ next before →
    Σ Edges.Edge (λ e → e ∈ edges × (identity ≡ Edges.Edge.to e × Eligible (State.frontier before) e))
  nextSound before identity member = Membership.∈-map∘filter⁻ Edges.Edge.to
    (eligible? (State.frontier before))
    (Membership.∈-deduplicate⁻ _≟_
     (destinations (State.frontier before))
     (proj₁
      (Membership.∈-filter⁻ (fresh? (State.visited before)) member)))

  edgeFollowed : ∀ before e → e ∈ edges → Eligible (State.frontier before) e →
    Edges.Edge.to e ∈ State.visited (advance before)
  edgeFollowed before e member eligible with Registry.IDs.present? (Edges.Edge.to e) (State.visited before)
  ... | yes old = visitedRetained before (Edges.Edge.to e) old
  ... | no fresh = discoveredRetained before (Edges.Edge.to e)
    (Membership.∈-filter⁺ (fresh? (State.visited before))
     (Membership.∈-deduplicate⁺ _≟_
      (Membership.∈-map∘filter⁺ Edges.Edge.to
       (eligible? (State.frontier before))
       (e , member , refl , eligible)))
     fresh)

  data Reached (seeds : List ℕ) : ℕ → Set where
    root : ∀ {identity} → identity ∈ seeds → Reached seeds identity
    follow : ∀ e → e ∈ edges → Carries (Edges.Edge.relation e) → Owned (Edges.Edge.to e) →
      Reached seeds (Edges.Edge.from e) → Reached seeds (Edges.Edge.to e)

  nextReached : ∀ seeds before → All (Reached seeds) (State.frontier before) → All (Reached seeds) (next before)
  nextReached seeds before frontier = All.tabulate
    (λ {identity} member →
       let e , edgeMember , same , source , carries , owned
             = nextSound before identity member
       in subst (Reached seeds) (sym same)
          (follow e edgeMember carries owned (All.lookup frontier source)))

  -- Every edge from an already visited source is accounted for: its target
  -- has been visited, or its source is still waiting in the current frontier.
  Accounted : State → Set
  Accounted before = ∀ e → e ∈ edges → Carries (Edges.Edge.relation e) → Owned (Edges.Edge.to e) →
    Edges.Edge.from e ∈ State.visited before →
    Edges.Edge.to e ∈ State.visited before ⊎ Edges.Edge.from e ∈ State.frontier before

  start : List ℕ → State
  start seeds = state seeds seeds

  initiallyAccounted : ∀ seeds → Accounted (start seeds)
  initiallyAccounted seeds e member carries owned source = inj₂ source

  advanceAccounted : ∀ before → Accounted before → Accounted (advance before)
  advanceAccounted before accounted e member carries owned source
    with Membership.∈-++⁻ (next before) source
  ... | inj₁ pending = inj₂ pending
  ... | inj₂ earlier with accounted e member carries owned earlier
  ...   | inj₁ target = inj₁ (visitedRetained before (Edges.Edge.to e) target)
  ...   | inj₂ pending = inj₁ (edgeFollowed before e member (pending , carries , owned))

  Closed : List ℕ → Set
  Closed visited = ∀ e → e ∈ edges → Carries (Edges.Edge.relation e) → Owned (Edges.Edge.to e) →
    Edges.Edge.from e ∈ visited → Edges.Edge.to e ∈ visited

  exhaustedClosed : ∀ visited → Accounted (state visited []) → Closed visited
  exhaustedClosed visited accounted e member carries owned source with accounted e member carries owned source
  ... | inj₁ target = target
  ... | inj₂ ()

  allReachableIncluded : ∀ seeds visited → All (λ identity → identity ∈ visited) seeds → Closed visited →
    ∀ identity → Reached seeds identity → identity ∈ visited
  allReachableIncluded seeds visited roots closed identity (root member) = All.lookup roots member
  allReachableIncluded seeds visited roots closed .(Edges.Edge.to e) (follow e member carries owned previous) = closed e member carries owned
    (allReachableIncluded seeds visited roots closed
     (Edges.Edge.from e) previous)
