{-# OPTIONS --safe #-}
-- The complete project ownership closure is published in one transaction.
-- Its returned count is the observed belief count plus the observed chunk
-- count; patterns are removed but do not contribute to that count.
module Mimir.ProjectDeletion where

open import Data.Bool using (Bool; true; false; not; _∨_)
open import Data.List using (List; []; _∷_; filterᵇ; map; length; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _+_; z≤n)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Mimir.Text using (Text)
import Mimir.ApplicationStore as Store
import Mimir.GraphWrites as Writes
import Mimir.LearningStore as Learning
import Mimir.ReviewPreparationPublication as Publication
import Mimir.ReviewLedger as Ledger
import Mimir.ExperienceRead as Read
import Mimir.ExperienceSchema as Experience
import Mimir.ReviewObservation as Observation
import Mimir.CandidateRegistry as Candidates
import Mimir.AssessmentWrites as Assessments
import Mimir.ItemOwners as Owners
import Mimir.RetrievalRanking as Ranking
import Mimir.DocumentStore as Documents
import Mimir.LearningTransaction as Transaction
import Mimir.DatabaseTransaction as DB
import Mimir.Effects as Effects

open import Data.String using (toList)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
import Mimir.CandidateGraph as Graph
import Mimir.ReviewEdges as Edges
import Mimir.Recovery as Recovery
import Mimir.StructuredValue as Wire

-- These list laws state both halves of deletion: every owned row is removed,
-- and every retained row survives. They quantify over all predicates and rows.
module Retention {A : Set} (owned : A → Bool) where
  retain : List A → List A
  retain = filterᵇ (λ value → not (owned value))

  excludesOwned : ∀ values → All (λ value → owned value ≡ false) (retain values)
  excludesOwned [] = []
  excludesOwned (value ∷ rest) with owned value in equality
  ... | true = excludesOwned rest
  ... | false = equality ∷ excludesOwned rest

  preservesUnowned : ∀ value values → owned value ≡ false →
    Any (value ≡_) values → Any (value ≡_) (retain values)
  preservesUnowned value (.value ∷ rest) retained (here refl) rewrite retained = here refl
  preservesUnowned value (head ∷ rest) retained (there present) with owned head
  ... | true = preservesUnowned value rest retained present
  ... | false = there (preservesUnowned value rest retained present)

ownedExperiences : Text → Learning.World → List ℕ
ownedExperiences project w = map Read.identity (filterᵇ (Read.scopeMatches (just project)) (Learning.World.current w))

-- SQL foreign-key cascades remove relational history and ownership. Graph
-- nodes/edges are not FK targets; the preceding graph DELETE phases own them.
forgetLearning : Text → Store.World → Store.World
forgetLearning project w = record w { learning = record learn
  { current = filterᵇ (λ r → keep (Read.identity r)) (Learning.World.current learn)
  ; sources = filterᵇ (λ r → keep (Experience.Experience.identity (Learning.SourceVersion.payload r))) (Learning.World.sources learn)
  ; reviewTimes = filterᵇ (λ r → keep (Learning.ReviewTime.experience r)) (Learning.World.reviewTimes learn)
  ; itemKeys = keys
  ; publication = record pub
    { ledger = Ledger.world cells histories
    ; registry = filterᵇ (λ r → keep (Candidates.Entry.experienceID r)) (Publication.World.registry pub)
    ; assessments = filterᵇ (λ r → keep (Assessments.Row.experience r)) (Publication.World.assessments pub)
    ; owners = owners } } }
  where
  learn = Store.World.learning w
  pub = Learning.World.publication learn
  ledger = Publication.World.ledger pub
  ids = ownedExperiences project learn
  keep : ℕ → Bool
  keep id = not (Ranking.member id ids)
  keys : ℕ → Text → Maybe ℕ
  keys experience name with Ranking.member experience ids
  ... | true = nothing
  ... | false = Learning.World.itemKeys learn experience name
  cells : ℕ → Ledger.R.Cell
  cells id with Ranking.member id ids
  ... | true = Ledger.R.cell [] 0 0 0 nothing z≤n
  ... | false = Ledger.World.cells ledger id
  histories : ℕ → List Ledger.Version
  histories id with Ranking.member id ids
  ... | true = []
  ... | false = Ledger.World.histories ledger id
  owners : Owners.Registry
  owners id with Publication.World.owners pub id
  ... | nothing = nothing
  ... | just (owner , provenance) with Ranking.member owner ids
  ...   | true = nothing
  ...   | false = just (owner , provenance)

forgottenExperienceKeysRemoved : ∀ project before experience name →
  Ranking.member experience (ownedExperiences project (Store.World.learning before)) ≡ true →
  Learning.World.itemKeys (Store.World.learning (forgetLearning project before)) experience name ≡ nothing
forgottenExperienceKeysRemoved project before experience name removed rewrite removed = refl

otherExperienceKeysPreserved : ∀ project before experience name →
  Ranking.member experience (ownedExperiences project (Store.World.learning before)) ≡ false →
  Learning.World.itemKeys (Store.World.learning (forgetLearning project before)) experience name ≡
    Learning.World.itemKeys (Store.World.learning before) experience name
otherExperienceKeysPreserved project before experience name retained rewrite retained = refl

projectChunks : Text → Store.World → List ℕ
projectChunks project w = map Documents.Chunk.identity
  (filterᵇ (λ c → Writes.tagged project (Documents.Chunk.project c)) (Store.World.chunks w))

-- Ownership is captured from the ORIGINAL world. Vector selection must not
-- depend on roots still being discoverable in the resulting world.
record Closure : Set where
  constructor closure
  field beliefs patterns chunks : List ℕ

ownership : Text → Store.World → Closure
ownership project before = closure (Writes.projectBeliefs project before)
  (Writes.projectPatterns project before) (projectChunks project before)

ownedNode : Text → Graph.Node → Bool
ownedNode project node = Writes.tagged project (Graph.nodeProject node)

ownedEdge : Closure → Edges.Edge → Bool
ownedEdge selected link = Ranking.member (Edges.Edge.from link) roots ∨ Ranking.member (Edges.Edge.to link) roots
  where roots = Closure.beliefs selected ++ Closure.patterns selected

ownedGround : Closure → Store.Ground → Bool
ownedGround selected edge = Ranking.member (Store.Ground.belief edge) (Closure.beliefs selected) ∨
  Ranking.member (Store.Ground.chunk edge) (Closure.chunks selected)

-- One resulting state, defined field by field from ownership. This function
-- contains no SQL statements, commit order, receipt or execution cursor.
eraseProject : Text → Store.World → Store.World
eraseProject project before = record before
  { learning = record learn
      { publication = record publication
          { nodes = Retention.retain (ownedNode project) (Store.nodes before)
          ; edges = Retention.retain (ownedEdge selected) (Publication.World.edges publication) }
      ; independentOrigins = Retention.retain (λ row → Ranking.member (proj₁ row) roots)
          (Learning.World.independentOrigins learn) }
  ; chunks = Retention.retain (λ chunk → Writes.tagged project (Documents.Chunk.project chunk)) (Store.World.chunks before)
  ; beliefVectors = Retention.retain (λ row → Ranking.member (proj₁ row) (Closure.beliefs selected)) (Store.World.beliefVectors before)
  ; chunkVectors = Retention.retain (λ row → Ranking.member (proj₁ row) (Closure.chunks selected)) (Store.World.chunkVectors before)
  ; grounds = Retention.retain (ownedGround selected) (Store.World.grounds before) }
  where
  selected = ownership project before
  roots = Closure.beliefs selected ++ Closure.patterns selected
  learn = Store.World.learning (forgetLearning project before)
  publication = Learning.World.publication learn

noOriginalBeliefVectors : ∀ project before →
  All (λ row → Ranking.member (proj₁ row) (Closure.beliefs (ownership project before)) ≡ false)
    (Store.World.beliefVectors (eraseProject project before))
noOriginalBeliefVectors project before = Retention.excludesOwned _ (Store.World.beliefVectors before)

noOriginalChunkVectors : ∀ project before →
  All (λ row → Ranking.member (proj₁ row) (Closure.chunks (ownership project before)) ≡ false)
    (Store.World.chunkVectors (eraseProject project before))
noOriginalChunkVectors project before = Retention.excludesOwned _ (Store.World.chunkVectors before)

noProjectNodes : ∀ project before → All (λ node → ownedNode project node ≡ false) (Store.nodes (eraseProject project before))
noProjectNodes project before = Retention.excludesOwned (ownedNode project) (Store.nodes before)

noProjectChunks : ∀ project before → All (λ chunk → Writes.tagged project (Documents.Chunk.project chunk) ≡ false)
  (Store.World.chunks (eraseProject project before))
noProjectChunks project before = Retention.excludesOwned _ (Store.World.chunks before)

noOwnedGrounds : ∀ project before → All (λ edge → ownedGround (ownership project before) edge ≡ false)
  (Store.World.grounds (eraseProject project before))
noOwnedGrounds project before = Retention.excludesOwned _ (Store.World.grounds before)

noOwnedEdges : ∀ project before → All (λ link → ownedEdge (ownership project before) link ≡ false)
  (Publication.World.edges (Learning.World.publication (Store.World.learning (eraseProject project before))))
noOwnedEdges project before = Retention.excludesOwned _
  (Publication.World.edges (Learning.World.publication (Store.World.learning before)))

noOriginalExperiences : ∀ project before →
  All (λ row → Ranking.member (Read.identity row) (ownedExperiences project (Store.World.learning before)) ≡ false)
    (Learning.World.current (Store.World.learning (eraseProject project before)))
noOriginalExperiences project before = Retention.excludesOwned _ (Learning.World.current (Store.World.learning before))

otherBeliefVectorPreserved : ∀ project before row →
  Ranking.member (proj₁ row) (Closure.beliefs (ownership project before)) ≡ false →
  Any (row ≡_) (Store.World.beliefVectors before) →
  Any (row ≡_) (Store.World.beliefVectors (eraseProject project before))
otherBeliefVectorPreserved project before row = Retention.preservesUnowned _ row (Store.World.beliefVectors before)

otherChunkVectorPreserved : ∀ project before row →
  Ranking.member (proj₁ row) (Closure.chunks (ownership project before)) ≡ false →
  Any (row ≡_) (Store.World.chunkVectors before) →
  Any (row ≡_) (Store.World.chunkVectors (eraseProject project before))
otherChunkVectorPreserved project before row = Retention.preservesUnowned _ row (Store.World.chunkVectors before)

otherNodePreserved : ∀ project before node → ownedNode project node ≡ false →
  Any (node ≡_) (Store.nodes before) → Any (node ≡_) (Store.nodes (eraseProject project before))
otherNodePreserved project before node = Retention.preservesUnowned _ node (Store.nodes before)

otherChunkPreserved : ∀ project before chunk → Writes.tagged project (Documents.Chunk.project chunk) ≡ false →
  Any (chunk ≡_) (Store.World.chunks before) → Any (chunk ≡_) (Store.World.chunks (eraseProject project before))
otherChunkPreserved project before chunk = Retention.preservesUnowned _ chunk (Store.World.chunks before)

otherEdgePreserved : ∀ project before link → ownedEdge (ownership project before) link ≡ false →
  Any (link ≡_) (Publication.World.edges (Learning.World.publication (Store.World.learning before))) →
  Any (link ≡_) (Publication.World.edges (Learning.World.publication (Store.World.learning (eraseProject project before))))
otherEdgePreserved project before link = Retention.preservesUnowned _ link
  (Publication.World.edges (Learning.World.publication (Store.World.learning before)))

deletedCount : Text → Store.World → ℕ
deletedCount project before = length (Writes.projectBeliefs project before) + length (projectChunks project before)

intent : Recovery.Business.Intent Text
intent = record
  { intended = eraseProject
  ; expectedReply = λ project before → Wire.object ((toList "deleted" , Wire.unsigned (deletedCount project before)) ∷ []) }

module Operation (database : ℕ) where
  module T = Transaction.Over Store.World ℕ Text database 671942183

  plan : Text → Store.World → T.Decision
  plan project before = T.replace (eraseProject project before) (deletedCount project before)

  Effect = T.Effect
  Reply = T.Reply
  module E = T.E

  data Result : Set where
    transactionResult : T.Outcome → Result
    deleted : ℕ → Result

  finish : T.Outcome → E.Script Result
  finish (T.applied count) = E.done (deleted count)
  finish result = E.done (transactionResult result)

  start : Text → E.Script Result
  start project = E._>>=_ Tx.start finish
    where module Tx = T.Plan (plan project)

  Publication : Text → Store.World → DB.Receipt → Store.World → Set
  Publication project before receipt after = DB.Atomic before (eraseProject project before) receipt after

  noPartiallyDeletedPublication : ∀ project before receipt after →
    Publication project before receipt after →
    after ≡ before ⊎ after ≡ eraseProject project before
  noPartiallyDeletedPublication project before .DB.committed .(eraseProject project before) DB.committedAll = inj₂ refl
  noPartiallyDeletedPublication project before .DB.aborted .before DB.abortedNone = inj₁ refl
  noPartiallyDeletedPublication project before .DB.acknowledgementLost .before DB.unknownBefore = inj₁ refl
  noPartiallyDeletedPublication project before .DB.acknowledgementLost .(eraseProject project before) DB.unknownAfter = inj₂ refl
