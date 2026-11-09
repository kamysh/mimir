{-# OPTIONS --safe #-}
-- Preserve the existing per-source, per-seed discovery order used by memory
-- preference. All identities and edges come from the selected stored carrier.
module Mimir.OrderedRetrieval where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; map; filter; deduplicate; length)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Membership.Propositional.Properties as Member
import Data.List.Properties as Lists
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.All.Properties as Every
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _≟_; _≤?_; _≤_; _<_)
import Data.Nat.Properties as Nat
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)
import Mimir.CandidateRegistry
import Mimir.LearningTargets as Targets
import Mimir.ReviewEdges as Edges
import Mimir.ReviewRecomputeTraversal as Traversal
import Mimir.TraversalCompleteness as Complete
import Mimir.RetrievalRanking as Ranking
import Mimir.ApplicationStore as Store
import Mimir.CandidateGraph as Graph
import Mimir.PreparedRetrieval as Prepared
import Mimir.LearningRecompute as Recompute
import Mimir.LearningStore as Learning
import Mimir.ReviewPreparationPublication as Publication
import Mimir.RetrievalProtocol as Protocol
import Mimir.RetrievalReadContract as Reads
import Mimir.StorageReadBinding as Database
import Mimir.LearningCandidates as Candidates
open import Mimir.Text using (Text)
open import Data.Maybe using (Maybe; just)

private
  before : ℕ → ℕ → Bool
  before x y = does (x ≤? y)

  insertKeeps : ∀ {A : Set} {P : A → Set} (order : A → A → Bool) x xs →
    P x → All P xs → All P (Ranking.insert order x xs)
  insertKeeps order x [] first All.[] = first All.∷ All.[]
  insertKeeps order x (y ∷ ys) first (second All.∷ rest) with order x y
  ... | true = first All.∷ second All.∷ rest
  ... | false = second All.∷ insertKeeps order x ys first rest

  sortKeeps : ∀ {A : Set} {P : A → Set} (order : A → A → Bool) xs → All P xs → All P (Ranking.sort order xs)
  sortKeeps order [] All.[] = All.[]
  sortKeeps order (x ∷ xs) (first All.∷ rest) =
    insertKeeps order x (Ranking.sort order xs) first (sortKeeps order xs rest)

  insertOld : ∀ x xs identity → identity ∈ xs → identity ∈ Ranking.insert before x xs
  insertOld x [] identity ()
  insertOld x (y ∷ ys) identity member with before x y
  ... | true = there member
  ... | false with member
  ...   | here same = here same
  ...   | there later = there (insertOld x ys identity later)

  insertNew : ∀ x xs → x ∈ Ranking.insert before x xs
  insertNew x [] = here refl
  insertNew x (y ∷ ys) with before x y
  ... | true = here refl
  ... | false = there (insertNew x ys)

  sortRetains : ∀ xs identity → identity ∈ xs → identity ∈ Ranking.sort before xs
  sortRetains (x ∷ xs) identity (here refl) = insertNew x (Ranking.sort before xs)
  sortRetains (x ∷ xs) identity (there member) = insertOld x (Ranking.sort before xs) identity (sortRetains xs identity member)

module For (beliefs : List Targets.Belief) (edges : List Edges.Edge) where
  module T = Traversal.For nothing beliefs edges
  module C = Complete.For nothing beliefs edges
  open Traversal using (State; state)

  fresh : List ℕ → ℕ → List ℕ
  fresh visited identity = filter (T.fresh? visited)
    (deduplicate _≟_ (Ranking.sort before (T.destinations (identity ∷ []))))

  freshAbsent : ∀ visited identity → All (λ x → x ∈ visited → ⊥) (fresh visited identity)
  freshAbsent visited identity = Every.all-filter (T.fresh? visited)
    (deduplicate _≟_ (Ranking.sort before (T.destinations (identity ∷ []))))

  freshOwned : ∀ visited identity → All T.Owned (fresh visited identity)
  freshOwned visited identity = Every.filter⁺ (T.fresh? visited)
    (Every.deduplicate⁺ _≟_ (sortKeeps before _ (T.destinationsOwned (identity ∷ []))))

  destinationsReached : ∀ seeds identity → T.Reached seeds identity →
    All (T.Reached seeds) (T.destinations (identity ∷ []))
  destinationsReached seeds identity reached = All.tabulate (λ {target} member →
    let e , present , same , source , carries , owned =
          Member.∈-map∘filter⁻ Edges.Edge.to (T.eligible? (identity ∷ [])) member
    in subst (T.Reached seeds) (sym same) (stepSource e present source carries owned))
    where
    stepSource : ∀ e → e ∈ edges → Edges.Edge.from e ∈ (identity ∷ []) →
      Traversal.Carries (Edges.Edge.relation e) → T.Owned (Edges.Edge.to e) → T.Reached seeds (Edges.Edge.to e)
    stepSource e present (here refl) carries owned = T.follow e present carries owned reached
    stepSource e present (there ()) carries owned

  freshReached : ∀ seeds visited identity → T.Reached seeds identity →
    All (T.Reached seeds) (fresh visited identity)
  freshReached seeds visited identity reached = Every.filter⁺ (T.fresh? visited)
    (Every.deduplicate⁺ _≟_ (sortKeeps before _ (destinationsReached seeds identity reached)))

  edgeFollowed : ∀ visited identity e → e ∈ edges → T.Eligible (identity ∷ []) e →
    Edges.Edge.to e ∈ visited ++ fresh visited identity
  edgeFollowed visited identity e present eligible with
    Mimir.CandidateRegistry.IDs.present? (Edges.Edge.to e) visited
  ... | Relation.Nullary.yes old = Member.∈-++⁺ˡ old
  ... | Relation.Nullary.no absent = Member.∈-++⁺ʳ visited
    (Member.∈-filter⁺ (T.fresh? visited)
      (Member.∈-deduplicate⁺ _≟_ (sortRetains _ _
        (Member.∈-map∘filter⁺ Edges.Edge.to (T.eligible? (identity ∷ []))
          (e , present , refl , eligible)))) absent)

  record Round (visited frontier : List ℕ) : Set where
    field
      result : State
      retained : ∀ identity → identity ∈ visited → identity ∈ State.visited result
      absent : All (λ identity → identity ∈ visited → ⊥) (State.frontier result)
      owned : All T.Owned (State.frontier result)
      pendingPresent : ∀ identity → identity ∈ State.frontier result → identity ∈ State.visited result
      origin : ∀ identity → identity ∈ State.visited result → identity ∈ visited ⊎ identity ∈ State.frontier result
      followed : ∀ e → e ∈ edges → T.Eligible frontier e → Edges.Edge.to e ∈ State.visited result
      reached : ∀ seeds → All (T.Reached seeds) visited → All (T.Reached seeds) frontier →
        All (T.Reached seeds) (State.visited result)

  round : ∀ visited frontier → Round visited frontier
  round visited [] = record
    { result = state visited []
    ; retained = λ identity member → member
    ; absent = All.[]
    ; owned = All.[]
    ; pendingPresent = λ identity ()
    ; origin = λ identity member → inj₁ member
    ; followed = λ { e member (() , carries , owned) }
    ; reached = λ seeds proof frontier → proof
    }
  round visited (identity ∷ rest) = record
    { result = state (State.visited (Round.result later)) (new ++ State.frontier (Round.result later))
    ; retained = λ x member → Round.retained later x (Member.∈-++⁺ˡ member)
    ; absent = Every.++⁺ (freshAbsent visited identity)
        (All.map (λ absent member → absent (Member.∈-++⁺ˡ member)) (Round.absent later))
    ; owned = Every.++⁺ (freshOwned visited identity) (Round.owned later)
    ; pendingPresent = pending
    ; origin = original
    ; followed = followed
    ; reached = λ seeds initial roots → Round.reached later seeds
        (Every.++⁺ initial (freshReached seeds visited identity (All.lookup roots (here refl))))
        (All.tail roots)
    }
    where
    new = fresh visited identity
    later = round (visited ++ new) rest

    pending : ∀ x → x ∈ new ++ State.frontier (Round.result later) → x ∈ State.visited (Round.result later)
    pending x member with Member.∈-++⁻ new member
    ... | inj₁ first = Round.retained later x (Member.∈-++⁺ʳ visited first)
    ... | inj₂ next = Round.pendingPresent later x next

    original : ∀ x → x ∈ State.visited (Round.result later) →
      x ∈ visited ⊎ x ∈ new ++ State.frontier (Round.result later)
    original x member with Round.origin later x member
    ... | inj₂ pending = inj₂ (Member.∈-++⁺ʳ new pending)
    ... | inj₁ earlier with Member.∈-++⁻ visited earlier
    ...   | inj₁ old = inj₁ old
    ...   | inj₂ found = inj₂ (Member.∈-++⁺ˡ found)

    followed : ∀ e → e ∈ edges → T.Eligible (identity ∷ rest) e →
      Edges.Edge.to e ∈ State.visited (Round.result later)
    followed e member (here same , carries , owned) =
      Round.retained later (Edges.Edge.to e) (edgeFollowed visited identity e member (here same , carries , owned))
    followed e member (there next , carries , owned) = Round.followed later e member (next , carries , owned)

  advance : State → State
  advance before = Round.result (round (State.visited before) (State.frontier before))

  remaining : State → List ℕ
  remaining before = filter (T.fresh? (State.visited before)) C.carrier

  decreases : ∀ before identity → identity ∈ State.frontier (advance before) →
    length (remaining (advance before)) < length (remaining before)
  decreases before identity member = subst
    (λ rows → length rows < length (remaining before)) (sym nested)
    (Lists.filter-notAll (T.fresh? (State.visited (advance before))) (remaining before)
      (C.witness (Member.∈-filter⁺ (T.fresh? (State.visited before))
        (C.lookupPresent identity beliefs (All.lookup (Round.owned step) member))
        (All.lookup (Round.absent step) member))
        (λ absent → absent (Round.pendingPresent step identity member))))
    where
    step = round (State.visited before) (State.frontier before)
    nested = Complete.Filters.nested _ _ (T.fresh? (State.visited before))
      (T.fresh? (State.visited (advance before)))
      (λ absent old → absent (Round.retained step _ old)) C.carrier

  private
    iterate : (State → State) → ℕ → State → State
    iterate step zero current = current
    iterate step (suc fuel) current with State.frontier current
    ... | [] = current
    ... | _ ∷ _ = iterate step fuel (step current)

    emptyStaysEmpty : ∀ step fuel visited → State.frontier (iterate step fuel (state visited [])) ≡ []
    emptyStaysEmpty step zero visited = refl
    emptyStaysEmpty step (suc fuel) visited = refl

    decreasingExhausts : ∀ step (measure : State → ℕ) →
      (∀ before identity → identity ∈ State.frontier (step before) → measure (step before) < measure before) →
      ∀ budget before → measure before ≤ budget → State.frontier (iterate step (suc budget) before) ≡ []
    decreasingExhausts step measure progress budget (state visited []) bound = refl
    decreasingExhausts step measure progress zero before@(state visited (_ ∷ _)) bound with step before | progress before
    ... | state later [] | decrease = refl
    ... | state later (x ∷ xs) | decrease = ⊥-elim (Nat.n≮0 (Nat.≤-trans (decrease x (here refl)) bound))
    decreasingExhausts step measure progress (suc budget) before@(state visited (_ ∷ _)) bound with step before | progress before
    ... | state later [] | decrease = emptyStaysEmpty step (suc budget) later
    ... | state later (x ∷ xs) | decrease = decreasingExhausts step measure progress budget (state later (x ∷ xs))
      (Nat.≤-pred (Nat.≤-trans (decrease x (here refl)) bound))

  expand : ℕ → State → State
  expand = iterate advance

  exhausts : ∀ budget before → length (remaining before) ≤ budget →
    State.frontier (expand (suc budget) before) ≡ []
  exhausts = decreasingExhausts advance (λ before → length (remaining before)) decreases

  graphSizedExhausts : ∀ visited frontier →
    State.frontier (expand (suc (length beliefs)) (state visited frontier)) ≡ []
  graphSizedExhausts visited frontier = exhausts (length beliefs) (state visited frontier)
    (subst (λ count → length (remaining (state visited frontier)) ≤ count)
      (Lists.length-map Targets.Belief.identity beliefs) (Lists.length-filter (T.fresh? visited) C.carrier))

  retained : ∀ fuel before identity → identity ∈ State.visited before → identity ∈ State.visited (expand fuel before)
  retained zero before identity member = member
  retained (suc fuel) (state visited []) identity member = member
  retained (suc fuel) before@(state visited (_ ∷ _)) identity member =
    retained fuel (advance before) identity (Round.retained (round (State.visited before) (State.frontier before)) identity member)

  reached : ∀ seeds fuel before → All (T.Reached seeds) (State.visited before) →
    All (T.Reached seeds) (State.frontier before) → All (T.Reached seeds) (State.visited (expand fuel before))
  reached seeds zero before proof frontier = proof
  reached seeds (suc fuel) (state visited []) proof frontier = proof
  reached seeds (suc fuel) before@(state visited (_ ∷ _)) proof frontier =
    reached seeds fuel (advance before)
      (Round.reached step seeds proof frontier)
      (All.tabulate (λ member → All.lookup (Round.reached step seeds proof frontier) (Round.pendingPresent step _ member)))
    where step = round (State.visited before) (State.frontier before)

  -- Initial seeds are already matched. While one seed's BFS runs, the other
  -- seeds still owe their outgoing edges; they remain in this invariant.
  advancePending : ∀ pending before →
    T.Accounted (state (State.visited before) (pending ++ State.frontier before)) →
    T.Accounted (state (State.visited (advance before)) (pending ++ State.frontier (advance before)))
  advancePending pending before previous e present carries owned source
    with Round.origin (round (State.visited before) (State.frontier before)) (Edges.Edge.from e) source
  ... | inj₂ discovered = inj₂ (Member.∈-++⁺ʳ pending discovered)
  ... | inj₁ old with previous e present carries owned old
  ...   | inj₁ target = inj₁ (Round.retained (round (State.visited before) (State.frontier before)) _ target)
  ...   | inj₂ waiting with Member.∈-++⁻ pending waiting
  ...     | inj₁ outer = inj₂ (Member.∈-++⁺ˡ outer)
  ...     | inj₂ active = inj₁ (Round.followed (round (State.visited before) (State.frontier before))
        e present (active , carries , owned))

  expandPending : ∀ pending fuel before →
    T.Accounted (state (State.visited before) (pending ++ State.frontier before)) →
    T.Accounted (state (State.visited (expand fuel before)) (pending ++ State.frontier (expand fuel before)))
  expandPending pending zero before proof = proof
  expandPending pending (suc fuel) (state visited []) proof = proof
  expandPending pending (suc fuel) before@(state visited (_ ∷ _)) proof =
    expandPending pending fuel (advance before) (advancePending pending before proof)

  walkSeeds : List ℕ → List ℕ → List ℕ
  walkSeeds [] visited = visited
  walkSeeds (identity ∷ rest) visited = walkSeeds rest
    (State.visited (expand (suc (length beliefs)) (state visited (identity ∷ []))))

  walkRetains : ∀ pending visited identity → identity ∈ visited → identity ∈ walkSeeds pending visited
  walkRetains [] visited identity member = member
  walkRetains (first ∷ rest) visited identity member = walkRetains rest _ identity
    (retained (suc (length beliefs)) (state visited (first ∷ [])) identity member)

  private
    moveSeed : ∀ visited identity pending → T.Accounted (state visited (identity ∷ pending)) →
      T.Accounted (state visited (pending ++ (identity ∷ [])))
    moveSeed visited identity pending previous e present carries owned source with previous e present carries owned source
    ... | inj₁ target = inj₁ target
    ... | inj₂ (here same) = inj₂ (Member.∈-++⁺ʳ pending (here same))
    ... | inj₂ (there later) = inj₂ (Member.∈-++⁺ˡ later)

    removeEmptyFrontier : ∀ visited pending frontier → frontier ≡ [] →
      T.Accounted (state visited (pending ++ frontier)) → T.Accounted (state visited pending)
    removeEmptyFrontier visited pending .[] refl proof rewrite Lists.++-identityʳ pending = proof

  walkAccounted : ∀ pending visited → T.Accounted (state visited pending) →
    T.Accounted (state (walkSeeds pending visited) [])
  walkAccounted [] visited proof = proof
  walkAccounted (identity ∷ rest) visited proof = walkAccounted rest _
    (removeEmptyFrontier _ rest _ (graphSizedExhausts visited (identity ∷ []))
      (expandPending rest (suc (length beliefs)) (state visited (identity ∷ []))
        (moveSeed visited identity rest proof)))

  walkComplete : ∀ seeds identity → T.Reached seeds identity → identity ∈ walkSeeds seeds seeds
  walkComplete seeds = T.allReachableIncluded seeds (walkSeeds seeds seeds)
    (All.tabulate (walkRetains seeds seeds _))
    (T.exhaustedClosed _ (walkAccounted seeds seeds (T.initiallyAccounted seeds)))

  walkReached : ∀ seeds pending visited → All (T.Reached seeds) visited → All (T.Reached seeds) pending →
    All (T.Reached seeds) (walkSeeds pending visited)
  walkReached seeds [] visited proof roots = proof
  walkReached seeds (identity ∷ rest) visited proof (first All.∷ later) = walkReached seeds rest _
    (reached seeds (suc (length beliefs)) (state visited (identity ∷ [])) proof (first All.∷ All.[])) later

  walkSound : ∀ seeds → All (T.Reached seeds) (walkSeeds seeds seeds)
  walkSound seeds = walkReached seeds seeds seeds (All.tabulate T.root) (All.tabulate T.root)

  advanceOwned : ∀ before → All T.Owned (State.visited before) → All T.Owned (State.visited (advance before))
  advanceOwned before proof = All.tabulate (λ member → choose
    (Round.origin step _ member))
    where
    step = round (State.visited before) (State.frontier before)
    choose : ∀ {identity} → identity ∈ State.visited before ⊎ identity ∈ State.frontier (advance before) → T.Owned identity
    choose (inj₁ old) = All.lookup proof old
    choose (inj₂ new) = All.lookup (Round.owned step) new

  expandOwned : ∀ fuel before → All T.Owned (State.visited before) → All T.Owned (State.visited (expand fuel before))
  expandOwned zero before proof = proof
  expandOwned (suc fuel) (state visited []) proof = proof
  expandOwned (suc fuel) before@(state visited (_ ∷ _)) proof = expandOwned fuel (advance before) (advanceOwned before proof)

  walkOwned : ∀ pending visited → All T.Owned visited → All T.Owned (walkSeeds pending visited)
  walkOwned [] visited proof = proof
  walkOwned (identity ∷ rest) visited proof = walkOwned rest _
    (expandOwned (suc (length beliefs)) (state visited (identity ∷ [])) proof)

record Request : Set where
  constructor searchRequest
  field context : Text; project : Maybe Text; selection : Ranking.Selection
        preference : Maybe Candidates.Memory

module Intent (arithmetic : Ranking.F32) (unicode : Ranking.Unicode)
  (database : Database.VectorOperations) where
  module P = Prepared.Intent arithmetic unicode database
  module Fusion = Ranking.Fusion arithmetic

  input : Request → Prepared.Preparation → Prepared.Input
  input request preparation = Prepared.input (Request.context request) (Request.project request)
    (Request.selection request) preparation

  edges : Store.World → List Edges.Edge
  edges snapshotState = Publication.World.edges (Learning.World.publication (Store.World.learning snapshotState))

  -- Unscoped SQL returns each seed's complete closure in ascending identity
  -- order. Only its returned endpoints are filtered; traversable intermediate
  -- nodes retain the existing whole-live-graph policy.
  unscoped : Request → Prepared.Preparation → Store.World → List ℕ →
    List Graph.BeliefValues → List Graph.BeliefValues
  unscoped request preparation snapshotState [] matched = matched
  unscoped request preparation snapshotState (identity ∷ rest) matched = unscoped request preparation snapshotState rest
    (proj₁ (Protocol.appendNew matched rows))
    where
    nodes = Store.beliefs snapshotState
    rows = Ranking.byIdentity (Data.List.filterᵇ (P.eligible (input request preparation) snapshotState)
      (Ranking.materialize (Recompute.closureScoped nothing nodes (edges snapshotState) (identity ∷ [])) nodes))

  matched : Request → Prepared.Preparation → Store.World → Prepared.PreparedVector → List Graph.BeliefValues
  matched request preparation snapshotState prepared with Request.project request
  ... | nothing = unscoped request preparation snapshotState seeds initial
    where
    selected = input request preparation
    seeds = P.seeds selected snapshotState prepared
    initial = Ranking.materialize
      (Ranking.unique (P.lexical selected snapshotState ++ P.vectors selected snapshotState prepared))
      (P.candidates selected snapshotState)
  ... | just _ = Ranking.materialize (O.walkSeeds seeds seeds) nodes
    where
    selected = input request preparation
    nodes = P.candidates selected snapshotState
    seeds = P.seeds selected snapshotState prepared
    module O = For (map Recompute.target nodes) (edges snapshotState)

  result : Request → Prepared.Preparation → Store.World → Prepared.PreparedVector → Protocol.Report
  result request preparation snapshotState prepared = Protocol.report
    (Fusion.rank (P.vectors selected snapshotState prepared) (P.lexical selected snapshotState)
      (Request.preference request) (Request.selection request) (matched request preparation snapshotState prepared))
    (Protocol.coverage (Request.context request) (Prepared.PreparedVector.semantic prepared))
    where selected = input request preparation

  hasCandidates : Request → Store.World → Prepared.Preparation → Bool
  hasCandidates request snapshotState preparation with P.candidates (input request preparation) snapshotState
  ... | [] = false
  ... | _ ∷ _ = true

  answer : Request → Store.World → Prepared.Preparation → Protocol.Report
  answer request snapshotState preparation with hasCandidates request snapshotState preparation
  ... | false = Protocol.report [] (Protocol.coverage (Request.context request) Protocol.noEligibleBeliefs)
  ... | true = result request preparation snapshotState (P.prepare preparation)

  private
    lookupKeeps : ∀ {Property : Graph.BeliefValues → Set} identity rows belief →
      All Property rows → Ranking.lookup identity rows ≡ just belief → Property belief
    lookupKeeps identity [] belief All.[] ()
    lookupKeeps identity (first ∷ rest) belief (property All.∷ properties) same
      with identity ≟ Graph.BeliefValues.identity first
    ... | Relation.Nullary.yes _ with same
    ...   | refl = property
    lookupKeeps identity (first ∷ rest) belief (property All.∷ properties) same
      | Relation.Nullary.no _ = lookupKeeps identity rest belief properties same

    materializeKeeps : ∀ {Property : Graph.BeliefValues → Set} identities rows →
      All Property rows → All Property (Ranking.materialize identities rows)
    materializeKeeps [] rows properties = All.[]
    materializeKeeps (identity ∷ rest) rows properties with Ranking.lookup identity rows in observed
    ... | nothing = materializeKeeps rest rows properties
    ... | just belief = lookupKeeps identity rows belief properties observed All.∷ materializeKeeps rest rows properties

    filterMember : ∀ (predicate : Graph.BeliefValues → Bool) rows belief → belief ∈ rows →
      predicate belief ≡ true → belief ∈ Data.List.filterᵇ predicate rows
    filterMember predicate (first ∷ rest) belief (here same) allowed
      with predicate first | subst (λ b → predicate b ≡ true) same allowed
    ... | true | valid = here same
    ... | false | ()
    filterMember predicate (first ∷ rest) belief (there member) allowed with predicate first
    ... | true = there (filterMember predicate rest belief member allowed)
    ... | false = filterMember predicate rest belief member allowed

    filteredMaterialized : ∀ predicate identities original →
      All (λ belief → belief ∈ Data.List.filterᵇ predicate original)
        (Data.List.filterᵇ predicate (Ranking.materialize identities original))
    filteredMaterialized predicate identities original = filterRows
      (Ranking.materialize identities original) (materializeKeeps identities original (All.tabulate (λ member → member)))
      where
      filterRows : ∀ rows → All (λ belief → belief ∈ original) rows →
        All (λ belief → belief ∈ Data.List.filterᵇ predicate original) (Data.List.filterᵇ predicate rows)
      filterRows [] All.[] = All.[]
      filterRows (belief ∷ rest) (stored All.∷ stores) with predicate belief in allowed
      ... | false = filterRows rest stores
      ... | true = filterMember predicate original belief stored allowed All.∷ filterRows rest stores

    appendKeeps : ∀ {Property : Graph.BeliefValues → Set} matched rows → All Property matched → All Property rows →
      All Property (proj₁ (Protocol.appendNew matched rows))
    appendKeeps matched [] properties All.[] = properties
    appendKeeps matched (belief ∷ rest) properties (first All.∷ remaining)
      with Ranking.member (Graph.BeliefValues.identity belief) (map Graph.BeliefValues.identity matched)
    ... | true = appendKeeps matched rest properties remaining
    ... | false = appendKeeps (matched ++ (belief ∷ [])) rest (Every.++⁺ properties (first All.∷ All.[])) remaining

    unscopedKeeps : ∀ request preparation snapshotState seeds matched →
      All (λ belief → belief ∈ P.candidates (input request preparation) snapshotState) matched →
      All (λ belief → belief ∈ P.candidates (input request preparation) snapshotState)
        (unscoped request preparation snapshotState seeds matched)
    unscopedKeeps request preparation snapshotState [] matched proof = proof
    unscopedKeeps request preparation snapshotState (identity ∷ rest) matched proof =
      unscopedKeeps request preparation snapshotState rest _ (appendKeeps matched _ proof
        (sortKeeps Ranking.identityBefore _ (filteredMaterialized (P.eligible (input request preparation) snapshotState)
          (Recompute.closureScoped nothing (Store.beliefs snapshotState) (edges snapshotState) (identity ∷ [])) (Store.beliefs snapshotState))))

    matchedKeeps : ∀ request preparation snapshotState prepared →
      All (λ belief → belief ∈ P.candidates (input request preparation) snapshotState)
        (matched request preparation snapshotState prepared)
    matchedKeeps request@(searchRequest text nothing selection preference) preparation snapshotState prepared =
      unscopedKeeps request preparation snapshotState (P.seeds selected snapshotState prepared)
        (Ranking.materialize identities rows)
        (materializeKeeps identities rows (All.tabulate (λ member → member)))
      where
      selected = input request preparation
      rows = P.candidates selected snapshotState
      identities = Ranking.unique (P.lexical selected snapshotState ++ P.vectors selected snapshotState prepared)
    matchedKeeps request@(searchRequest text (just project) selection preference) preparation snapshotState prepared =
      materializeKeeps (O.walkSeeds seeds seeds) rows (All.tabulate (λ member → member))
      where
      selected = input request preparation
      rows = P.candidates selected snapshotState
      seeds = P.seeds selected snapshotState prepared
      module O = For (map Recompute.target rows) (edges snapshotState)

    takeKeeps : ∀ {Property : Graph.BeliefValues → Set} count rows → All Property rows → All Property (Data.List.take count rows)
    takeKeeps zero rows proof = All.[]
    takeKeeps (suc count) [] All.[] = All.[]
    takeKeeps (suc count) (belief ∷ rest) (first All.∷ remaining) = first All.∷ takeKeeps count rest remaining

    selectKeeps : ∀ {Property : Graph.BeliefValues → Set} selection rows → All Property rows → All Property (Ranking.cap selection rows)
    selectKeeps nothing rows proof = proof
    selectKeeps (just count) rows proof = takeKeeps (Ranking.PositiveCount.count count) rows proof

    resultKeeps : ∀ request preparation snapshotState prepared →
      All (λ belief → belief ∈ P.candidates (input request preparation) snapshotState)
        (Protocol.Report.beliefs (result request preparation snapshotState prepared))
    resultKeeps request preparation snapshotState prepared = selectKeeps (Request.selection request) _
      (sortKeeps (Fusion.before _) _ (matchedKeeps request preparation snapshotState prepared))

  everyReturnedBeliefIsAnEligibleStoredCandidate : ∀ request snapshotState preparation →
    All (λ belief → belief ∈ P.candidates (input request preparation) snapshotState)
      (Protocol.Report.beliefs (answer request snapshotState preparation))
  everyReturnedBeliefIsAnEligibleStoredCandidate request snapshotState preparation
    with hasCandidates request snapshotState preparation
  ... | false = All.[]
  ... | true = resultKeeps request preparation snapshotState (P.prepare preparation)

  module Scoped (text project : Text) (selection : Ranking.Selection)
    (preference : Maybe Candidates.Memory) (preparation : Prepared.Preparation)
    (snapshotState : Store.World) (prepared : Prepared.PreparedVector) where
    request = searchRequest text (just project) selection preference
    selected = input request preparation
    rows = P.candidates selected snapshotState
    seeds = P.seeds selected snapshotState prepared
    module O = For (map Recompute.target rows) (edges snapshotState)
    module S = Complete.PreparedSearch arithmetic unicode database selected snapshotState prepared

    identities = O.walkSeeds seeds seeds

    usesTheCertifiedTraversal : matched request preparation snapshotState prepared ≡ Ranking.materialize identities rows
    usesTheCertifiedTraversal = refl

    everyAllowedReachableIdentityIncluded : ∀ identity → O.T.Reached seeds identity → identity ∈ identities
    everyAllowedReachableIdentityIncluded = O.walkComplete seeds

    everyDiscoveredIdentityIsReachable : All (O.T.Reached seeds) identities
    everyDiscoveredIdentityIsReachable = O.walkSound seeds

    everyDiscoveredIdentityIsInScope : All O.T.Owned identities
    everyDiscoveredIdentityIsInScope = O.walkOwned seeds seeds S.seedsFromCarrier
