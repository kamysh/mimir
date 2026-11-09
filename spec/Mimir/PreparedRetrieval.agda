{-# OPTIONS --safe #-}
-- Intended results for the INTERNAL prepared, type-neutral search boundary.
-- The public dispatcher must still establish that preparation belongs to its
-- request. No caller-provided beliefs, ranks or expected answer enter here.
module Mimir.PreparedRetrieval where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map; filterᵇ)
open import Data.List.Membership.Propositional using (_∈_)
import Data.List.Relation.Unary.All as Every
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤?_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (toList)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.ApplicationStore as Store
import Mimir.CandidateGraph as Graph
import Mimir.RetrievalRanking as Ranking
import Mimir.RetrievalReadContract as Reads
import Mimir.RetrievalProtocol as Protocol
import Mimir.StorageReadBinding as Database
import Mimir.ReviewPreparationPublication as Publication
import Mimir.LearningStore as Learning
import Mimir.LearningRecompute as Recompute
import Mimir.Recovery as Recovery
import Mimir.LearningContextProtocol as Context

data Preparation : Set where
  unconfigured : Preparation
  observed : Text ⊎ List Store.Vector → Preparation

-- This internal request has no memory-type preference. The remaining public
-- preference case must retain its existing discovery-order ranking policy.
record Input : Set where
  constructor input
  field context : Text; project : Maybe Text; selection : Ranking.Selection
        preparation : Preparation

record PreparedVector : Set where
  constructor preparedVector
  field semantic : Protocol.Semantic; vector : Maybe Store.Vector

module Intent (arithmetic : Ranking.F32) (unicode : Ranking.Unicode)
  (database : Database.VectorOperations) where
  module Fusion = Ranking.Fusion arithmetic
  module Existing = Protocol.Run arithmetic unicode

  prepare : Preparation → PreparedVector
  prepare unconfigured = preparedVector Protocol.unconfigured nothing
  prepare (observed (inj₁ cause)) = preparedVector (Protocol.embeddingFailed cause) nothing
  prepare (observed (inj₂ [])) = preparedVector
    (Protocol.unusableQueryVector (toList "The backend returned no query embedding.")) nothing
  prepare (observed (inj₂ ([] ∷ []))) = preparedVector
    (Protocol.unusableQueryVector (toList "The query embedding is empty.")) nothing
  prepare (observed (inj₂ ((first ∷ rest) ∷ []))) with Existing.finiteVector (first ∷ rest)
  ... | false = preparedVector
    (Protocol.unusableQueryVector (toList "The query embedding contains a non-finite value.")) nothing
  ... | true with Existing.nonzeroVector (first ∷ rest)
  ...   | false = preparedVector
    (Protocol.unusableQueryVector (toList "The query embedding has zero norm, so cosine similarity is undefined.")) nothing
  ...   | true = preparedVector Protocol.evaluated (just (first ∷ rest))
  prepare (observed (inj₂ (_ ∷ _ ∷ _))) = preparedVector
    (Protocol.unusableQueryVector (toList "The backend returned multiple embeddings for one submitted context.")) nothing

  eligible : Input → Store.World → Graph.BeliefValues → Bool
  eligible request state = Ranking.eligible (Input.project request) (Reads.retired state)

  candidates : Input → Store.World → List Graph.BeliefValues
  candidates request state = filterᵇ (eligible request state) (Store.beliefs state)

  lexical : Input → Store.World → List ℕ
  lexical request state = Ranking.tokenRanking unicode (Input.context request) (candidates request state)

  -- Scope is applied before vector ranking, exactly where it constrains the
  -- database candidate table. Unscoped lookup retains all table rows, including
  -- orphan vector IDs which are removed later by graph materialization.
  vectorRows : Input → Store.World → List (ℕ × Store.Vector)
  vectorRows request state with Input.project request
  ... | nothing = Store.World.beliefVectors state
  ... | just _ = Database.eligibleVectors
    (just (map Graph.BeliefValues.identity (candidates request state))) (Store.World.beliefVectors state)

  vectorBefore : Store.Vector → (ℕ × Store.Vector) → (ℕ × Store.Vector) → Bool
  vectorBefore query first second with Database.VectorOperations.databaseLessEqual database
    (Database.VectorOperations.cosineDistance database query (proj₂ first))
    (Database.VectorOperations.cosineDistance database query (proj₂ second))
  ... | false = false
  ... | true with Database.VectorOperations.databaseLessEqual database
    (Database.VectorOperations.cosineDistance database query (proj₂ second))
    (Database.VectorOperations.cosineDistance database query (proj₂ first))
  ...   | false = true
  ...   | true = does (proj₁ first ≤? proj₁ second)

  vectors : Input → Store.World → PreparedVector → List ℕ
  vectors request state (preparedVector semantic nothing) = []
  vectors request state (preparedVector semantic (just query)) =
    map proj₁ (Ranking.sort (vectorBefore query) (vectorRows request state))

  seeds : Input → Store.World → PreparedVector → List ℕ
  seeds request state prepared = map Graph.BeliefValues.identity
    (Ranking.materialize (Ranking.unique (lexical request state ++ vectors request state prepared))
      (candidates request state))
    where open import Data.List using (_++_)

  -- A scoped search may traverse readable global beliefs, but may not use a
  -- foreign/working/superseded intermediate to bridge back into scope. An
  -- unscoped closure follows the complete live graph and filters its endpoints.
  carrier : Input → Store.World → List Graph.BeliefValues
  carrier request state with Input.project request
  ... | nothing = Store.beliefs state
  ... | just _ = candidates request state

  matched : Input → Store.World → PreparedVector → List Graph.BeliefValues
  matched request state prepared = Ranking.byIdentity
    (filterᵇ (λ belief → Ranking.member (Graph.BeliefValues.identity belief) reached) (candidates request state))
    where
    edges = Publication.World.edges (Learning.World.publication (Store.World.learning state))
    reached = Recompute.closureScoped nothing (carrier request state) edges (seeds request state prepared)

  result : Input → Store.World → PreparedVector → Protocol.Report
  result request state prepared = Protocol.report
    (Fusion.rank (vectors request state prepared) (lexical request state) nothing
      (Input.selection request) (matched request state prepared))
    (Protocol.coverage (Input.context request) (PreparedVector.semantic prepared))

  answer : Input → Store.World → Protocol.Report
  answer request state with candidates request state
  ... | [] = Protocol.report [] (Protocol.coverage (Input.context request) Protocol.noEligibleBeliefs)
  ... | _ ∷ _ = result request state (prepare (Input.preparation request))

  module Checked = Recovery.ReadOnly answer

  operation : Recovery.Recoverable Store.World Input
  operation = Checked.operation

  completeReplyAndUnchangedWorld : ∀ request initial interrupted final reply →
    Checked.Checked.X.Interrupted (Checked.Checked.script request) initial interrupted →
    Checked.Checked.X.Completed (Checked.Checked.script request) interrupted final reply →
    final ≡ initial × reply ≡ answer request initial
  completeReplyAndUnchangedWorld = Checked.completedRetryPreservesStateAndAnswer

  private
    filterKeeps : ∀ {A : Set} {P : A → Set} predicate xs →
      Every.All P xs → Every.All P (filterᵇ predicate xs)
    filterKeeps predicate [] Every.[] = Every.[]
    filterKeeps predicate (x ∷ xs) (first Every.∷ rest) with predicate x
    ... | false = filterKeeps predicate xs rest
    ... | true = first Every.∷ filterKeeps predicate xs rest

    filterTrue : ∀ {A : Set} (predicate : A → Bool) xs →
      Every.All (λ x → predicate x ≡ true) (filterᵇ predicate xs)
    filterTrue predicate [] = Every.[]
    filterTrue predicate (x ∷ xs) with predicate x in observedPredicate
    ... | false = filterTrue predicate xs
    ... | true = observedPredicate Every.∷ filterTrue predicate xs

    insertKeeps : ∀ {A : Set} {P : A → Set} before x xs →
      P x → Every.All P xs → Every.All P (Ranking.insert before x xs)
    insertKeeps before x [] proof Every.[] = proof Every.∷ Every.[]
    insertKeeps before x (y ∷ ys) proof (first Every.∷ rest) with before x y
    ... | true = proof Every.∷ first Every.∷ rest
    ... | false = first Every.∷ insertKeeps before x ys proof rest

    sortKeeps : ∀ {A : Set} {P : A → Set} before xs →
      Every.All P xs → Every.All P (Ranking.sort before xs)
    sortKeeps before [] Every.[] = Every.[]
    sortKeeps before (x ∷ xs) (first Every.∷ rest) =
      insertKeeps before x (Ranking.sort before xs) first (sortKeeps before xs rest)

    takeKeeps : ∀ {A : Set} {P : A → Set} count xs →
      Every.All P xs → Every.All P (Data.List.take count xs)
    takeKeeps Data.Nat.zero xs proof = Every.[]
    takeKeeps (Data.Nat.suc count) [] Every.[] = Every.[]
    takeKeeps (Data.Nat.suc count) (x ∷ xs) (first Every.∷ rest) = first Every.∷ takeKeeps count xs rest

    selectionKeeps : ∀ {A : Set} {P : A → Set} selection xs →
      Every.All P xs → Every.All P (Ranking.cap selection xs)
    selectionKeeps nothing xs proof = proof
    selectionKeeps (just count) xs proof = takeKeeps (Ranking.PositiveCount.count count) xs proof

    matchedKeeps : ∀ {P : Graph.BeliefValues → Set} request state prepared →
      Every.All P (candidates request state) → Every.All P (matched request state prepared)
    matchedKeeps request state prepared proof = sortKeeps Ranking.identityBefore _ (filterKeeps _ _ proof)

    resultKeeps : ∀ {P : Graph.BeliefValues → Set} request state prepared →
      Every.All P (candidates request state) → Every.All P (Protocol.Report.beliefs (result request state prepared))
    resultKeeps request state prepared proof = selectionKeeps (Input.selection request) _
      (sortKeeps (Fusion.before _) _ (matchedKeeps request state prepared proof))

  everyReturnedBeliefIsEligible : ∀ request state →
    Every.All (λ belief → eligible request state belief ≡ true) (Protocol.Report.beliefs (answer request state))
  everyReturnedBeliefIsEligible request state with candidates request state
  ... | [] = Every.[]
  ... | _ ∷ _ = resultKeeps request state (prepare (Input.preparation request))
    (filterTrue (eligible request state) (Store.beliefs state))

  everyReturnedBeliefIsStored : ∀ request state →
    Every.All (λ belief → belief ∈ Store.beliefs state) (Protocol.Report.beliefs (answer request state))
  everyReturnedBeliefIsStored request state with candidates request state
  ... | [] = Every.[]
  ... | _ ∷ _ = resultKeeps request state (prepare (Input.preparation request))
    (filterKeeps (eligible request state) (Store.beliefs state) (Every.tabulate (λ member → member)))

  unconfiguredNeverClaimsSemanticEvaluation : ∀ query project selection state →
    Protocol.Coverage.semantic (Protocol.Report.retrieval (answer (input query project selection unconfigured) state)) ≡
      Protocol.noEligibleBeliefs ⊎
    Protocol.Coverage.semantic (Protocol.Report.retrieval (answer (input query project selection unconfigured) state)) ≡
      Protocol.unconfigured
  unconfiguredNeverClaimsSemanticEvaluation query project selection state
    with candidates (input query project selection unconfigured) state
  ... | [] = inj₁ refl
  ... | _ ∷ _ = inj₂ refl

  equalVectorDistancesUseIdentity : ∀ query first second →
    Database.VectorOperations.databaseLessEqual database
      (Database.VectorOperations.cosineDistance database query (proj₂ first))
      (Database.VectorOperations.cosineDistance database query (proj₂ second)) ≡ true →
    Database.VectorOperations.databaseLessEqual database
      (Database.VectorOperations.cosineDistance database query (proj₂ second))
      (Database.VectorOperations.cosineDistance database query (proj₂ first)) ≡ true →
    vectorBefore query first second ≡ does (proj₁ first ≤? proj₁ second)
  equalVectorDistancesUseIdentity query first second forward reverse rewrite forward | reverse = refl

module LearningContext (arithmetic : Ranking.F32) (unicode : Ranking.Unicode)
  (database : Database.VectorOperations) (textBefore : Text → Text → Bool) where
  module Retrieval = Intent arithmetic unicode database
  module Assembly = Context.Assembly unicode textBefore

  record Request : Set where
    constructor contextSearch
    field context project : Text; selection : Ranking.Selection; preparation : Preparation

  embeddingsEnabled : Preparation → Bool
  embeddingsEnabled unconfigured = false
  embeddingsEnabled (observed _) = true

  query : Request → Input
  query request = input (Request.context request) (just (Request.project request))
    (Request.selection request) (Request.preparation request)

  assembled : Request → Store.World → Assembly.Input
  assembled request state = Assembly.selected
    (Context.contextRequest (Request.context request) (Request.project request) (Request.selection request)
      (embeddingsEnabled (Request.preparation request)))
    (map Graph.BeliefValues.identity (Protocol.Report.beliefs selected))
    (Protocol.Coverage.semantic (Protocol.Report.retrieval selected))
    where selected = Retrieval.answer (query request) state

  answer : Request → Store.World → Assembly.Result
  answer request state = Assembly.answer (assembled request state) state

  module Checked = Recovery.ReadOnly answer
  operation : Recovery.Recoverable Store.World Request
  operation = Checked.operation

  completeReplyAndUnchangedWorld : ∀ request initial interrupted final reply →
    Checked.Checked.X.Interrupted (Checked.Checked.script request) initial interrupted →
    Checked.Checked.X.Completed (Checked.Checked.script request) interrupted final reply →
    final ≡ initial × reply ≡ answer request initial
  completeReplyAndUnchangedWorld = Checked.completedRetryPreservesStateAndAnswer
