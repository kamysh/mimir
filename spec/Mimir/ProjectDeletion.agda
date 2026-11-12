{-# OPTIONS --safe #-}
-- Project deletion removes all owned data in one transaction. Its returned
-- count is the belief count plus the chunk count from the transaction's view;
-- patterns are removed but do not contribute to that count.
module Mimir.ProjectDeletion where

open import Data.Bool using (Bool; true; false; not)
open import Data.List using (List; []; _∷_; _++_; filterᵇ; map; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _+_; z≤n)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.String using (toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Mimir.Text using (Text)
open import Mimir.UUIDGroups using (UUID; _≟UUID_)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.ApplicationStore as Store
import Mimir.GraphWrites as Writes
import Mimir.CandidateGraph as Graph
import Mimir.IndependentProvenance as Origin
import Mimir.StructuredValue as JSON
import Mimir.ReviewEdges as Edges
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
import Mimir.Recovery as Recovery

ownedExperiences : Text → Learning.World → List UUID
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
  keep : UUID → Bool
  keep id = not (Ranking.member id ids)
  keys : UUID → Text → Maybe UUID
  keys experience name with Ranking.member experience ids
  ... | true = nothing
  ... | false = Learning.World.itemKeys learn experience name
  cells : UUID → Ledger.R.Cell
  cells id with Ranking.member id ids
  ... | true = Ledger.R.cell [] 0 0 0 nothing z≤n
  ... | false = Ledger.World.cells ledger id
  histories : UUID → List Ledger.Version
  histories id with Ranking.member id ids
  ... | true = []
  ... | false = Ledger.World.histories ledger id
  owners : Owners.Registry
  owners id with Publication.World.owners pub id
  ... | nothing = nothing
  ... | just (owner , provenance) with Ranking.member owner ids
  ...   | true = nothing
  ...   | false = just (owner , provenance)

projectChunks : Text → Store.World → List UUID
projectChunks project w = map Documents.Chunk.identity
  (filterᵇ (λ c → Writes.tagged project (Documents.Chunk.project c)) (Store.World.chunks w))

-- Capture both sets of ownership keys from the same transaction view, before
-- removing anything that would make those keys undiscoverable.
intended : Text → Store.World → Store.World
intended project w = forgetLearning project
  (Store.removeNodes patternIDs false
    (Writes.deleteProjectBeliefs project
      (Store.removeChunks chunkIDs
        (Store.removeChunkVectors chunkIDs
          (Store.removeBeliefVectors beliefIDs w)))))
  where
  beliefIDs = Writes.projectBeliefs project w
  patternIDs = Writes.projectPatterns project w
  chunkIDs = projectChunks project w

deletedCount : Text → Store.World → ℕ
deletedCount project w = length (Writes.projectBeliefs project w) + length (projectChunks project w)

-- Records owned by the project must be absent after deletion.
data NoRows {A : Set} (key : A → UUID) (ids : List UUID) : List A → Set where
  noRows : NoRows key ids []
  keptRow : ∀ {row rest} → Ranking.member (key row) ids ≡ false →
    NoRows key ids rest → NoRows key ids (row ∷ rest)

rowsCleared : ∀ {A : Set} (key : A → UUID) ids rows →
  NoRows key ids (filterᵇ (λ row → not (Ranking.member (key row) ids)) rows)
rowsCleared key ids [] = noRows
rowsCleared key ids (row ∷ rest) with Ranking.member (key row) ids in selected
... | true = rowsCleared key ids rest
... | false = keptRow selected (rowsCleared key ids rest)

rowsStayCleared : ∀ {A : Set} (key : A → UUID) original removed rows → NoRows key original rows →
  NoRows key original (filterᵇ (λ row → not (Ranking.member (key row) removed)) rows)
rowsStayCleared key original removed [] noRows = noRows
rowsStayCleared key original removed (row ∷ rest) (keptRow absent tail)
  with Ranking.member (key row) removed
... | true = rowsStayCleared key original removed rest tail
... | false = keptRow absent (rowsStayCleared key original removed rest tail)

rowsSurviveFilter : ∀ {A : Set} (key : A → UUID) ids (keep : A → Bool) rows →
  NoRows key ids rows → NoRows key ids (filterᵇ keep rows)
rowsSurviveFilter key ids keep [] noRows = noRows
rowsSurviveFilter key ids keep (row ∷ rest) (keptRow absent tail) with keep row
... | true = keptRow absent (rowsSurviveFilter key ids keep rest tail)
... | false = rowsSurviveFilter key ids keep rest tail

edgesFromCleared : ∀ ids edges → NoRows Edges.Edge.from ids (Store.detach ids edges)
edgesFromCleared ids [] = noRows
edgesFromCleared ids (relation ∷ rest) with Ranking.member (Edges.Edge.from relation) ids in selected
... | true = edgesFromCleared ids rest
... | false with Ranking.member (Edges.Edge.to relation) ids
...   | true = edgesFromCleared ids rest
...   | false = keptRow selected (edgesFromCleared ids rest)

edgesToCleared : ∀ ids edges → NoRows Edges.Edge.to ids (Store.detach ids edges)
edgesToCleared ids [] = noRows
edgesToCleared ids (relation ∷ rest) with Ranking.member (Edges.Edge.from relation) ids
... | true = edgesToCleared ids rest
... | false with Ranking.member (Edges.Edge.to relation) ids in selected
...   | true = edgesToCleared ids rest
...   | false = keptRow selected (edgesToCleared ids rest)

edgesStayCleared : ∀ key ids removed edges → NoRows key ids edges → NoRows key ids (Store.detach removed edges)
edgesStayCleared key ids removed edges = rowsSurviveFilter key ids
  (λ relation → not (Ranking.member (Edges.Edge.from relation) removed Data.Bool.∨
                           Ranking.member (Edges.Edge.to relation) removed)) edges

NoVectors : ∀ {A : Set} → List UUID → List (UUID × A) → Set
NoVectors = NoRows proj₁

vectorsCleared : ∀ {A : Set} (ids : List UUID) (rows : List (UUID × A)) →
  NoVectors ids (filterᵇ (λ row → not (Ranking.member (proj₁ row) ids)) rows)
vectorsCleared = rowsCleared proj₁

vectorsRemainCleared : ∀ {A : Set} (original removed : List UUID) (rows : List (UUID × A)) →
  NoVectors original rows →
  NoVectors original (filterᵇ (λ row → not (Ranking.member (proj₁ row) removed)) rows)
vectorsRemainCleared = rowsStayCleared proj₁

beliefVectorsCleared : ∀ project before →
  NoVectors (Writes.projectBeliefs project before) (Store.World.beliefVectors (intended project before))
beliefVectorsCleared project before = vectorsCleared (Writes.projectBeliefs project before) (Store.World.beliefVectors before)

beliefVectorsRemainCleared : ∀ project before ids →
  NoVectors ids (Store.World.beliefVectors before) →
  NoVectors ids (Store.World.beliefVectors (intended project before))
beliefVectorsRemainCleared project before ids cleared =
  vectorsRemainCleared ids (Writes.projectBeliefs project before) (Store.World.beliefVectors before) cleared

chunkVectorsCleared : ∀ project before →
  NoVectors (projectChunks project before) (Store.World.chunkVectors (intended project before))
chunkVectorsCleared project before = vectorsCleared (projectChunks project before) (Store.World.chunkVectors before)

chunkVectorsRemainCleared : ∀ project before ids →
  NoVectors ids (Store.World.chunkVectors before) →
  NoVectors ids (Store.World.chunkVectors (intended project before))
chunkVectorsRemainCleared project before ids cleared =
  vectorsRemainCleared ids (projectChunks project before) (Store.World.chunkVectors before) cleared

NoNodes : List UUID → List Graph.Node → Set
NoNodes = NoRows Graph.nodeID

nodesCleared : ∀ ids nodes →
  NoNodes ids (filterᵇ (λ node → not (Ranking.member (Graph.nodeID node) ids)) nodes)
nodesCleared = rowsCleared Graph.nodeID

nodesRemainCleared : ∀ original removed nodes → NoNodes original nodes →
  NoNodes original (filterᵇ (λ node → not (Ranking.member (Graph.nodeID node) removed)) nodes)
nodesRemainCleared = rowsStayCleared Graph.nodeID

beliefNodesCleared : ∀ project before →
  NoNodes (Writes.projectBeliefs project before) (Store.nodes (intended project before))
beliefNodesCleared project before =
  nodesRemainCleared (Writes.projectBeliefs project before)
    (Writes.projectPatterns project before)
    (Store.nodes afterBeliefs)
    (nodesCleared (Writes.projectBeliefs project before) (Store.nodes before))
  where
  afterBeliefs = Writes.deleteProjectBeliefs project
    (Store.removeChunks (projectChunks project before)
      (Store.removeChunkVectors (projectChunks project before)
        (Store.removeBeliefVectors (Writes.projectBeliefs project before) before)))

patternNodesCleared : ∀ project before →
  NoNodes (Writes.projectPatterns project before) (Store.nodes (intended project before))
patternNodesCleared project before = nodesCleared (Writes.projectPatterns project before)
  (Store.nodes (Writes.deleteProjectBeliefs project before))

nodesStayCleared : ∀ project before ids → NoNodes ids (Store.nodes before) →
  NoNodes ids (Store.nodes (intended project before))
nodesStayCleared project before ids cleared =
  nodesRemainCleared ids (Writes.projectPatterns project before)
    (Store.nodes (Writes.deleteProjectBeliefs project before))
    (nodesRemainCleared ids (Writes.projectBeliefs project before) (Store.nodes before) cleared)

edgesOf : Store.World → List Edges.Edge
edgesOf state = Publication.World.edges (Learning.World.publication (Store.World.learning state))

beliefEdgesCleared : ∀ key →
  (∀ ids edges → NoRows key ids (Store.detach ids edges)) →
  ∀ project before → NoRows key (Writes.projectBeliefs project before) (edgesOf (intended project before))
beliefEdgesCleared key clears project before = edgesStayCleared key (Writes.projectBeliefs project before)
  (Writes.projectPatterns project before) (Store.detach (Writes.projectBeliefs project before) (edgesOf before))
  (clears (Writes.projectBeliefs project before) (edgesOf before))

patternEdgesCleared : ∀ key →
  (∀ ids edges → NoRows key ids (Store.detach ids edges)) →
  ∀ project before → NoRows key (Writes.projectPatterns project before) (edgesOf (intended project before))
patternEdgesCleared key clears project before = clears (Writes.projectPatterns project before)
  (Store.detach (Writes.projectBeliefs project before) (edgesOf before))

edgesOfStayCleared : ∀ key project before ids → NoRows key ids (edgesOf before) →
  NoRows key ids (edgesOf (intended project before))
edgesOfStayCleared key project before ids cleared = edgesStayCleared key ids (Writes.projectPatterns project before)
  (Store.detach (Writes.projectBeliefs project before) (edgesOf before))
  (edgesStayCleared key ids (Writes.projectBeliefs project before) (edgesOf before) cleared)

keepGroundBelief : List UUID → Store.Ground → Bool
keepGroundBelief ids row = not (Ranking.member (Store.Ground.belief row) ids)

keepGroundChunk : List UUID → Store.Ground → Bool
keepGroundChunk ids row = not (Ranking.member (Store.Ground.chunk row) ids)

beliefGroundsCleared : ∀ project before →
  NoRows Store.Ground.belief (Writes.projectBeliefs project before) (Store.World.grounds (intended project before))
beliefGroundsCleared project before = rowsSurviveFilter Store.Ground.belief beliefIDs
  (keepGroundBelief (Writes.projectPatterns project before))
  (filterᵇ (keepGroundBelief beliefIDs) withoutChunks)
  (rowsCleared Store.Ground.belief beliefIDs withoutChunks)
  where
  beliefIDs = Writes.projectBeliefs project before
  withoutChunks = filterᵇ (keepGroundChunk (projectChunks project before)) (Store.World.grounds before)

patternGroundsCleared : ∀ project before →
  NoRows Store.Ground.belief (Writes.projectPatterns project before) (Store.World.grounds (intended project before))
patternGroundsCleared project before = rowsCleared Store.Ground.belief (Writes.projectPatterns project before)
  (filterᵇ (keepGroundBelief (Writes.projectBeliefs project before))
    (filterᵇ (keepGroundChunk (projectChunks project before)) (Store.World.grounds before)))

chunkGroundsCleared : ∀ project before →
  NoRows Store.Ground.chunk (projectChunks project before) (Store.World.grounds (intended project before))
chunkGroundsCleared project before = rowsSurviveFilter Store.Ground.chunk chunkIDs
  (keepGroundBelief (Writes.projectPatterns project before)) afterBeliefs
  (rowsSurviveFilter Store.Ground.chunk chunkIDs (keepGroundBelief (Writes.projectBeliefs project before)) withoutChunks
    (rowsCleared Store.Ground.chunk chunkIDs (Store.World.grounds before)))
  where
  chunkIDs = projectChunks project before
  withoutChunks = filterᵇ (keepGroundChunk chunkIDs) (Store.World.grounds before)
  afterBeliefs = filterᵇ (keepGroundBelief (Writes.projectBeliefs project before)) withoutChunks

groundsStayCleared : ∀ key project before ids → NoRows key ids (Store.World.grounds before) →
  NoRows key ids (Store.World.grounds (intended project before))
groundsStayCleared key project before ids cleared = rowsSurviveFilter key ids
  (keepGroundBelief (Writes.projectPatterns project before)) afterBeliefs
  (rowsSurviveFilter key ids (keepGroundBelief (Writes.projectBeliefs project before)) withoutChunks
    (rowsSurviveFilter key ids (keepGroundChunk (projectChunks project before)) (Store.World.grounds before) cleared))
  where
  withoutChunks = filterᵇ (keepGroundChunk (projectChunks project before)) (Store.World.grounds before)
  afterBeliefs = filterᵇ (keepGroundBelief (Writes.projectBeliefs project before)) withoutChunks

originsOf : Store.World → List (UUID × Origin.Stored)
originsOf state = Learning.World.independentOrigins (Store.World.learning state)

beliefOriginsCleared : ∀ project before →
  NoRows proj₁ (Writes.projectBeliefs project before) (originsOf (intended project before))
beliefOriginsCleared project before = rowsStayCleared proj₁ beliefIDs patternIDs
  (filterᵇ (λ row → not (Ranking.member (proj₁ row) beliefIDs)) (originsOf before))
  (rowsCleared proj₁ beliefIDs (originsOf before))
  where
  beliefIDs = Writes.projectBeliefs project before
  patternIDs = Writes.projectPatterns project before

patternOriginsCleared : ∀ project before →
  NoRows proj₁ (Writes.projectPatterns project before) (originsOf (intended project before))
patternOriginsCleared project before = rowsCleared proj₁ (Writes.projectPatterns project before)
  (filterᵇ (λ row → not (Ranking.member (proj₁ row) (Writes.projectBeliefs project before))) (originsOf before))

originsStayCleared : ∀ project before ids → NoRows proj₁ ids (originsOf before) →
  NoRows proj₁ ids (originsOf (intended project before))
originsStayCleared project before ids cleared = rowsStayCleared proj₁ ids (Writes.projectPatterns project before)
  (filterᵇ (λ row → not (Ranking.member (proj₁ row) (Writes.projectBeliefs project before))) (originsOf before))
  (rowsStayCleared proj₁ ids (Writes.projectBeliefs project before) (originsOf before) cleared)

NoChunks : List UUID → List Documents.Chunk → Set
NoChunks = NoRows Documents.Chunk.identity

chunksCleared : ∀ ids chunks →
  NoChunks ids (filterᵇ (λ chunk → not (Ranking.member (Documents.Chunk.identity chunk) ids)) chunks)
chunksCleared = rowsCleared Documents.Chunk.identity

chunksRemainCleared : ∀ original removed chunks → NoChunks original chunks →
  NoChunks original (filterᵇ (λ chunk → not (Ranking.member (Documents.Chunk.identity chunk) removed)) chunks)
chunksRemainCleared = rowsStayCleared Documents.Chunk.identity

projectChunksCleared : ∀ project before →
  NoChunks (projectChunks project before) (Store.World.chunks (intended project before))
projectChunksCleared project before = chunksCleared (projectChunks project before) (Store.World.chunks before)

chunksStayCleared : ∀ project before ids → NoChunks ids (Store.World.chunks before) →
  NoChunks ids (Store.World.chunks (intended project before))
chunksStayCleared project before ids cleared =
  chunksRemainCleared ids (projectChunks project before) (Store.World.chunks before) cleared

currentCleared : ∀ project before →
  NoRows Read.identity (ownedExperiences project (Store.World.learning before))
    (Learning.World.current (Store.World.learning (intended project before)))
currentCleared project before = rowsCleared Read.identity
  (ownedExperiences project (Store.World.learning before)) (Learning.World.current (Store.World.learning before))

currentStayCleared : ∀ project before ids → NoRows Read.identity ids (Learning.World.current (Store.World.learning before)) →
  NoRows Read.identity ids (Learning.World.current (Store.World.learning (intended project before)))
currentStayCleared project before ids cleared = rowsStayCleared Read.identity ids
  (ownedExperiences project (Store.World.learning before)) (Learning.World.current (Store.World.learning before)) cleared

sourceKey : Learning.SourceVersion → UUID
sourceKey row = Experience.Experience.identity (Learning.SourceVersion.payload row)

sourcesCleared : ∀ project before →
  NoRows sourceKey (ownedExperiences project (Store.World.learning before))
    (Learning.World.sources (Store.World.learning (intended project before)))
sourcesCleared project before = rowsCleared sourceKey
  (ownedExperiences project (Store.World.learning before)) (Learning.World.sources (Store.World.learning before))

sourcesStayCleared : ∀ project before ids → NoRows sourceKey ids (Learning.World.sources (Store.World.learning before)) →
  NoRows sourceKey ids (Learning.World.sources (Store.World.learning (intended project before)))
sourcesStayCleared project before ids cleared = rowsStayCleared sourceKey ids
  (ownedExperiences project (Store.World.learning before)) (Learning.World.sources (Store.World.learning before)) cleared

reviewTimesCleared : ∀ project before →
  NoRows Learning.ReviewTime.experience (ownedExperiences project (Store.World.learning before))
    (Learning.World.reviewTimes (Store.World.learning (intended project before)))
reviewTimesCleared project before = rowsCleared Learning.ReviewTime.experience
  (ownedExperiences project (Store.World.learning before)) (Learning.World.reviewTimes (Store.World.learning before))

reviewTimesStayCleared : ∀ project before ids →
  NoRows Learning.ReviewTime.experience ids (Learning.World.reviewTimes (Store.World.learning before)) →
  NoRows Learning.ReviewTime.experience ids (Learning.World.reviewTimes (Store.World.learning (intended project before)))
reviewTimesStayCleared project before ids cleared = rowsStayCleared Learning.ReviewTime.experience ids
  (ownedExperiences project (Store.World.learning before)) (Learning.World.reviewTimes (Store.World.learning before)) cleared

registryCleared : ∀ project before →
  NoRows Candidates.Entry.experienceID (ownedExperiences project (Store.World.learning before))
    (Publication.World.registry (Learning.World.publication (Store.World.learning (intended project before))))
registryCleared project before = rowsCleared Candidates.Entry.experienceID
  (ownedExperiences project (Store.World.learning before))
  (Publication.World.registry (Learning.World.publication (Store.World.learning before)))

registryStayCleared : ∀ project before ids →
  NoRows Candidates.Entry.experienceID ids (Publication.World.registry (Learning.World.publication (Store.World.learning before))) →
  NoRows Candidates.Entry.experienceID ids (Publication.World.registry (Learning.World.publication (Store.World.learning (intended project before))))
registryStayCleared project before ids cleared = rowsStayCleared Candidates.Entry.experienceID ids
  (ownedExperiences project (Store.World.learning before))
  (Publication.World.registry (Learning.World.publication (Store.World.learning before))) cleared

assessmentsCleared : ∀ project before →
  NoRows Assessments.Row.experience (ownedExperiences project (Store.World.learning before))
    (Publication.World.assessments (Learning.World.publication (Store.World.learning (intended project before))))
assessmentsCleared project before = rowsCleared Assessments.Row.experience
  (ownedExperiences project (Store.World.learning before))
  (Publication.World.assessments (Learning.World.publication (Store.World.learning before)))

assessmentsStayCleared : ∀ project before ids →
  NoRows Assessments.Row.experience ids (Publication.World.assessments (Learning.World.publication (Store.World.learning before))) →
  NoRows Assessments.Row.experience ids (Publication.World.assessments (Learning.World.publication (Store.World.learning (intended project before))))
assessmentsStayCleared project before ids cleared = rowsStayCleared Assessments.Row.experience ids
  (ownedExperiences project (Store.World.learning before))
  (Publication.World.assessments (Learning.World.publication (Store.World.learning before))) cleared

itemKeyCleared : ∀ project before experience name →
  Ranking.member experience (ownedExperiences project (Store.World.learning before)) ≡ true →
  Learning.World.itemKeys (Store.World.learning (intended project before)) experience name ≡ nothing
itemKeyCleared project before experience name selected rewrite selected = refl

itemKeyStaysCleared : ∀ project before experience name →
  Learning.World.itemKeys (Store.World.learning before) experience name ≡ nothing →
  Learning.World.itemKeys (Store.World.learning (intended project before)) experience name ≡ nothing
itemKeyStaysCleared project before experience name cleared
  with Ranking.member experience (ownedExperiences project (Store.World.learning before))
... | true = refl
... | false = cleared

historyCleared : ∀ project before experience →
  Ranking.member experience (ownedExperiences project (Store.World.learning before)) ≡ true →
  Ledger.World.histories (Publication.World.ledger (Learning.World.publication (Store.World.learning (intended project before)))) experience ≡ []
historyCleared project before experience selected rewrite selected = refl

historyStaysCleared : ∀ project before experience →
  Ledger.World.histories (Publication.World.ledger (Learning.World.publication (Store.World.learning before))) experience ≡ [] →
  Ledger.World.histories (Publication.World.ledger (Learning.World.publication (Store.World.learning (intended project before)))) experience ≡ []
historyStaysCleared project before experience cleared
  with Ranking.member experience (ownedExperiences project (Store.World.learning before))
... | true = refl
... | false = cleared

emptyReviewCell : Ledger.R.Cell
emptyReviewCell = Ledger.R.cell [] 0 0 0 nothing z≤n

reviewCellCleared : ∀ project before experience →
  Ranking.member experience (ownedExperiences project (Store.World.learning before)) ≡ true →
  Ledger.World.cells (Publication.World.ledger (Learning.World.publication (Store.World.learning (intended project before)))) experience ≡ emptyReviewCell
reviewCellCleared project before experience selected rewrite selected = refl

reviewCellStaysCleared : ∀ project before experience →
  Ledger.World.cells (Publication.World.ledger (Learning.World.publication (Store.World.learning before))) experience ≡ emptyReviewCell →
  Ledger.World.cells (Publication.World.ledger (Learning.World.publication (Store.World.learning (intended project before)))) experience ≡ emptyReviewCell
reviewCellStaysCleared project before experience cleared
  with Ranking.member experience (ownedExperiences project (Store.World.learning before))
... | true = refl
... | false = cleared

ownerOf : Store.World → UUID → Maybe Owners.Owner
ownerOf state = Publication.World.owners (Learning.World.publication (Store.World.learning state))

ownerCleared : ∀ project before item experience provenance →
  ownerOf before item ≡ just (experience , provenance) →
  Ranking.member experience (ownedExperiences project (Store.World.learning before)) ≡ true →
  ownerOf (intended project before) item ≡ nothing
ownerCleared project before item experience provenance original selected rewrite original | selected = refl

ownerStaysCleared : ∀ project before item → ownerOf before item ≡ nothing →
  ownerOf (intended project before) item ≡ nothing
ownerStaysCleared project before item cleared rewrite cleared = refl

-- The observable goal is stated against ownership in the original world,
-- not against whatever keys a retry can still discover.
record Deleted (project : Text) (before after : Store.World) : Set where
  private
    beliefIDs = Writes.projectBeliefs project before
    patternIDs = Writes.projectPatterns project before
    chunkIDs = projectChunks project before
    experienceIDs = ownedExperiences project (Store.World.learning before)
    learned = Store.World.learning after
    publication = Learning.World.publication learned
    ledger = Publication.World.ledger publication
  field
    beliefs : NoNodes beliefIDs (Store.nodes after)
    patterns : NoNodes patternIDs (Store.nodes after)
    beliefVectors : NoVectors beliefIDs (Store.World.beliefVectors after)
    chunks : NoChunks chunkIDs (Store.World.chunks after)
    chunkVectors : NoVectors chunkIDs (Store.World.chunkVectors after)
    beliefEdgesFrom : NoRows Edges.Edge.from beliefIDs (edgesOf after)
    beliefEdgesTo : NoRows Edges.Edge.to beliefIDs (edgesOf after)
    patternEdgesFrom : NoRows Edges.Edge.from patternIDs (edgesOf after)
    patternEdgesTo : NoRows Edges.Edge.to patternIDs (edgesOf after)
    beliefGrounds : NoRows Store.Ground.belief beliefIDs (Store.World.grounds after)
    patternGrounds : NoRows Store.Ground.belief patternIDs (Store.World.grounds after)
    chunkGrounds : NoRows Store.Ground.chunk chunkIDs (Store.World.grounds after)
    beliefOrigins : NoRows proj₁ beliefIDs (originsOf after)
    patternOrigins : NoRows proj₁ patternIDs (originsOf after)
    experiences : NoRows Read.identity experienceIDs (Learning.World.current learned)
    sources : NoRows sourceKey experienceIDs (Learning.World.sources learned)
    reviewTimes : NoRows Learning.ReviewTime.experience experienceIDs (Learning.World.reviewTimes learned)
    registry : NoRows Candidates.Entry.experienceID experienceIDs (Publication.World.registry publication)
    assessments : NoRows Assessments.Row.experience experienceIDs (Publication.World.assessments publication)
    itemKeys : ∀ experience name → Ranking.member experience experienceIDs ≡ true →
      Learning.World.itemKeys learned experience name ≡ nothing
    histories : ∀ experience → Ranking.member experience experienceIDs ≡ true →
      Ledger.World.histories ledger experience ≡ []
    cells : ∀ experience → Ranking.member experience experienceIDs ≡ true →
      Ledger.World.cells ledger experience ≡ emptyReviewCell
    owners : ∀ item experience provenance → ownerOf before item ≡ just (experience , provenance) →
      Ranking.member experience experienceIDs ≡ true → ownerOf after item ≡ nothing

published : Text → Store.World → Store.World
published = intended

module Operation (database : ℕ) where
  module T = Transaction.Over Store.World ℕ Text database 671942183

  plan : Text → Store.World → T.Decision
  plan project w = T.replace (published project w) (deletedCount project w)

  data Effect : Set where
    learning : T.Effect → Effect

  Reply : Effect → Set
  Reply (learning effect) = T.Reply effect

  module E = Effects.Protocol Effect Reply
  open E

  data Result : Set where
    transactionResult : T.Outcome → Result
    deleted : ℕ → Result

  liftLearning : T.E.Script T.Outcome → Script T.Outcome
  liftLearning (T.E.done result) = done result
  liftLearning (T.E.ask effect next) = ask (learning effect) (λ reply → liftLearning (next reply))

  start : Text → Script Result
  start project = liftLearning Tx.start >>= finish
    where
    module Tx = T.Plan (plan project)
    finish : T.Outcome → Script Result
    finish (T.applied count) = done (deleted count)
    finish result = done (transactionResult result)

  -- A reported success must come from one transaction that read its world,
  -- wrote this operation's intended result, and received a commit receipt.
  successfulTrace : ∀ project events count → Runs (start project) events (deleted count) →
    Σ ℕ (λ tx → Σ Store.World (λ before →
      events ≡
        (learning (T.begin database) , inj₂ tx) ∷
        (learning (T.acquire tx 671942183) , inj₂ tt) ∷
        (learning (T.read tx) , inj₂ before) ∷
        (learning (T.write tx (published project before)) , inj₂ tt) ∷
        (learning (T.commit tx) , T.committed) ∷ [] ×
      count ≡ deletedCount project before))
  successfulTrace project events count (replied _ _ (inj₁ failure) ())
  successfulTrace project events count
    (replied _ _ (inj₂ tx) (replied _ _ (inj₁ failure) (replied _ _ cleanup ())))
  successfulTrace project events count
    (replied _ _ (inj₂ tx) (replied _ _ (inj₂ tt) (replied _ _ (inj₁ failure)
      (replied _ _ cleanup ()))))
  successfulTrace project events count
    (replied _ _ (inj₂ tx) (replied _ _ (inj₂ tt) (replied _ _ (inj₂ before)
      (replied _ _ (inj₁ failure) (replied _ _ cleanup ())))))
  successfulTrace project events count
    (replied _ _ (inj₂ tx) (replied _ _ (inj₂ tt) (replied _ _ (inj₂ before)
      (replied _ _ (inj₂ tt) (replied _ _ (T.aborted failure) ())))))
  successfulTrace project events count
    (replied _ _ (inj₂ tx) (replied _ _ (inj₂ tt) (replied _ _ (inj₂ before)
      (replied _ _ (inj₂ tt) (replied _ _ T.committed (returned .(deleted count))))))) =
    tx , before , refl , refl

  possibleSuccess : ∀ project tx before →
    Runs (start project)
      ((learning (T.begin database) , inj₂ tx) ∷
       (learning (T.acquire tx 671942183) , inj₂ tt) ∷
       (learning (T.read tx) , inj₂ before) ∷
       (learning (T.write tx (published project before)) , inj₂ tt) ∷
       (learning (T.commit tx) , T.committed) ∷ [])
      (deleted (deletedCount project before))
  possibleSuccess project tx before =
    replied _ _ (inj₂ tx) (replied _ _ (inj₂ tt) (replied _ _ (inj₂ before)
      (replied _ _ (inj₂ tt) (replied _ _ T.committed (returned _)))))

  TransactionPublication : Text → Store.World → DB.Receipt → Store.World → Set
  TransactionPublication project before receipt after = DB.Atomic before (published project before) receipt after

  -- Each interrupted attempt can have published or the entire
  -- transaction. There is no intermediate publication to strand a vector.
  data Interruptions (project : Text) : Store.World → Store.World → Set where
    none : ∀ {world} → Interruptions project world world
    oneInterruption : ∀ {before middle after receipt events residual} →
      Prefix (start project) events residual →
      TransactionPublication project before receipt middle →
      Interruptions project middle after → Interruptions project before after

  -- The committed retry is an actual run of this operation, with the stated
  -- transaction snapshot and write. PostgreSQL supplies the atomic receipt.
  data Completed (project : Text) (before after : Store.World) : Set where
    completed : ∀ tx →
      Runs (start project)
        ((learning (T.begin database) , inj₂ tx) ∷
         (learning (T.acquire tx 671942183) , inj₂ tt) ∷
         (learning (T.read tx) , inj₂ before) ∷
         (learning (T.write tx (published project before)) , inj₂ tt) ∷
         (learning (T.commit tx) , T.committed) ∷ [])
        (deleted (deletedCount project before)) →
      TransactionPublication project before DB.committed after → Completed project before after

  retryAfterInterruptions : ∀ {Property : Store.World → Set} project before intermediate final →
    Property (published project before) →
    (∀ world → Property world → Property (published project world)) →
    Interruptions project before intermediate →
    TransactionPublication project intermediate DB.committed final → Property final
  retryAfterInterruptions {Property} project before intermediate final cleared preserves interruptions DB.committedAll
    with reached (inj₁ refl) interruptions
    where
    advance : ∀ {world next receipt} → world ≡ before ⊎ Property world →
      TransactionPublication project world receipt next → next ≡ before ⊎ Property next
    advance (inj₁ refl) DB.committedAll = inj₂ cleared
    advance (inj₂ property) DB.committedAll = inj₂ (preserves _ property)
    advance reached DB.abortedNone = reached

    reached : ∀ {world next} → world ≡ before ⊎ Property world →
      Interruptions project world next → next ≡ before ⊎ Property next
    reached known none = known
    reached known (oneInterruption prefix publication rest) = reached (advance known publication) rest
  ... | inj₁ refl = cleared
  ... | inj₂ property = preserves _ property

  retriesClearBeliefEdges : ∀ key →
    (∀ ids edges → NoRows key ids (Store.detach ids edges)) →
    ∀ project before intermediate final → Interruptions project before intermediate →
    TransactionPublication project intermediate DB.committed final →
    NoRows key (Writes.projectBeliefs project before) (edgesOf final)
  retriesClearBeliefEdges key clears project before intermediate final attempts retry =
    retryAfterInterruptions project before intermediate final (beliefEdgesCleared key clears project before)
      (λ world → edgesOfStayCleared key project world (Writes.projectBeliefs project before)) attempts retry

  retriesClearPatternEdges : ∀ key →
    (∀ ids edges → NoRows key ids (Store.detach ids edges)) →
    ∀ project before intermediate final → Interruptions project before intermediate →
    TransactionPublication project intermediate DB.committed final →
    NoRows key (Writes.projectPatterns project before) (edgesOf final)
  retriesClearPatternEdges key clears project before intermediate final attempts retry =
    retryAfterInterruptions project before intermediate final (patternEdgesCleared key clears project before)
      (λ world → edgesOfStayCleared key project world (Writes.projectPatterns project before)) attempts retry

  retriesClearBeliefGrounds : ∀ project before intermediate final → Interruptions project before intermediate →
    TransactionPublication project intermediate DB.committed final →
    NoRows Store.Ground.belief (Writes.projectBeliefs project before) (Store.World.grounds final)
  retriesClearBeliefGrounds project before intermediate final attempts retry =
    retryAfterInterruptions project before intermediate final (beliefGroundsCleared project before)
      (λ world → groundsStayCleared Store.Ground.belief project world (Writes.projectBeliefs project before)) attempts retry

  retriesClearPatternGrounds : ∀ project before intermediate final → Interruptions project before intermediate →
    TransactionPublication project intermediate DB.committed final →
    NoRows Store.Ground.belief (Writes.projectPatterns project before) (Store.World.grounds final)
  retriesClearPatternGrounds project before intermediate final attempts retry =
    retryAfterInterruptions project before intermediate final (patternGroundsCleared project before)
      (λ world → groundsStayCleared Store.Ground.belief project world (Writes.projectPatterns project before)) attempts retry

  retriesClearChunkGrounds : ∀ project before intermediate final → Interruptions project before intermediate →
    TransactionPublication project intermediate DB.committed final →
    NoRows Store.Ground.chunk (projectChunks project before) (Store.World.grounds final)
  retriesClearChunkGrounds project before intermediate final attempts retry =
    retryAfterInterruptions project before intermediate final (chunkGroundsCleared project before)
      (λ world → groundsStayCleared Store.Ground.chunk project world (projectChunks project before)) attempts retry

  retriesClearBeliefOrigins : ∀ project before intermediate final → Interruptions project before intermediate →
    TransactionPublication project intermediate DB.committed final →
    NoRows proj₁ (Writes.projectBeliefs project before) (originsOf final)
  retriesClearBeliefOrigins project before intermediate final attempts retry =
    retryAfterInterruptions project before intermediate final (beliefOriginsCleared project before)
      (λ world → originsStayCleared project world (Writes.projectBeliefs project before)) attempts retry

  retriesClearPatternOrigins : ∀ project before intermediate final → Interruptions project before intermediate →
    TransactionPublication project intermediate DB.committed final →
    NoRows proj₁ (Writes.projectPatterns project before) (originsOf final)
  retriesClearPatternOrigins project before intermediate final attempts retry =
    retryAfterInterruptions project before intermediate final (patternOriginsCleared project before)
      (λ world → originsStayCleared project world (Writes.projectPatterns project before)) attempts retry

  retriesClearItemKey : ∀ project before intermediate final experience name →
    Ranking.member experience (ownedExperiences project (Store.World.learning before)) ≡ true →
    Interruptions project before intermediate → TransactionPublication project intermediate DB.committed final →
    Learning.World.itemKeys (Store.World.learning final) experience name ≡ nothing
  retriesClearItemKey project before intermediate final experience name selected attempts retry =
    retryAfterInterruptions project before intermediate final (itemKeyCleared project before experience name selected)
      (λ world → itemKeyStaysCleared project world experience name) attempts retry

  retriesClearHistory : ∀ project before intermediate final experience →
    Ranking.member experience (ownedExperiences project (Store.World.learning before)) ≡ true →
    Interruptions project before intermediate → TransactionPublication project intermediate DB.committed final →
    Ledger.World.histories (Publication.World.ledger (Learning.World.publication (Store.World.learning final))) experience ≡ []
  retriesClearHistory project before intermediate final experience selected attempts retry =
    retryAfterInterruptions project before intermediate final (historyCleared project before experience selected)
      (λ world → historyStaysCleared project world experience) attempts retry

  retriesClearReviewCell : ∀ project before intermediate final experience →
    Ranking.member experience (ownedExperiences project (Store.World.learning before)) ≡ true →
    Interruptions project before intermediate → TransactionPublication project intermediate DB.committed final →
    Ledger.World.cells (Publication.World.ledger (Learning.World.publication (Store.World.learning final))) experience ≡ emptyReviewCell
  retriesClearReviewCell project before intermediate final experience selected attempts retry =
    retryAfterInterruptions project before intermediate final (reviewCellCleared project before experience selected)
      (λ world → reviewCellStaysCleared project world experience) attempts retry

  retriesClearOwner : ∀ project before intermediate final item experience provenance →
    ownerOf before item ≡ just (experience , provenance) →
    Ranking.member experience (ownedExperiences project (Store.World.learning before)) ≡ true →
    Interruptions project before intermediate → TransactionPublication project intermediate DB.committed final →
    ownerOf final item ≡ nothing
  retriesClearOwner project before intermediate final item experience provenance original selected attempts retry =
    retryAfterInterruptions project before intermediate final (ownerCleared project before item experience provenance original selected)
      (λ world → ownerStaysCleared project world item) attempts retry

  deletionConverges : ∀ project before intermediate final →
    Interruptions project before intermediate →
    Completed project intermediate final → Deleted project before final
  deletionConverges project before intermediate final attempts (completed tx run retry) = record
    { beliefs = prove (beliefNodesCleared project before)
        (λ world → nodesStayCleared project world (Writes.projectBeliefs project before))
    ; patterns = prove (patternNodesCleared project before)
        (λ world → nodesStayCleared project world (Writes.projectPatterns project before))
    ; beliefVectors = prove (beliefVectorsCleared project before)
        (λ world → beliefVectorsRemainCleared project world (Writes.projectBeliefs project before))
    ; chunks = prove (projectChunksCleared project before)
        (λ world → chunksStayCleared project world (projectChunks project before))
    ; chunkVectors = prove (chunkVectorsCleared project before)
        (λ world → chunkVectorsRemainCleared project world (projectChunks project before))
    ; beliefEdgesFrom = retriesClearBeliefEdges Edges.Edge.from edgesFromCleared project before intermediate final attempts retry
    ; beliefEdgesTo = retriesClearBeliefEdges Edges.Edge.to edgesToCleared project before intermediate final attempts retry
    ; patternEdgesFrom = retriesClearPatternEdges Edges.Edge.from edgesFromCleared project before intermediate final attempts retry
    ; patternEdgesTo = retriesClearPatternEdges Edges.Edge.to edgesToCleared project before intermediate final attempts retry
    ; beliefGrounds = retriesClearBeliefGrounds project before intermediate final attempts retry
    ; patternGrounds = retriesClearPatternGrounds project before intermediate final attempts retry
    ; chunkGrounds = retriesClearChunkGrounds project before intermediate final attempts retry
    ; beliefOrigins = retriesClearBeliefOrigins project before intermediate final attempts retry
    ; patternOrigins = retriesClearPatternOrigins project before intermediate final attempts retry
    ; experiences = prove (currentCleared project before)
        (λ world → currentStayCleared project world (ownedExperiences project (Store.World.learning before)))
    ; sources = prove (sourcesCleared project before)
        (λ world → sourcesStayCleared project world (ownedExperiences project (Store.World.learning before)))
    ; reviewTimes = prove (reviewTimesCleared project before)
        (λ world → reviewTimesStayCleared project world (ownedExperiences project (Store.World.learning before)))
    ; registry = prove (registryCleared project before)
        (λ world → registryStayCleared project world (ownedExperiences project (Store.World.learning before)))
    ; assessments = prove (assessmentsCleared project before)
        (λ world → assessmentsStayCleared project world (ownedExperiences project (Store.World.learning before)))
    ; itemKeys = λ experience name selected → retriesClearItemKey project before intermediate final experience name selected attempts retry
    ; histories = λ experience selected → retriesClearHistory project before intermediate final experience selected attempts retry
    ; cells = λ experience selected → retriesClearReviewCell project before intermediate final experience selected attempts retry
    ; owners = λ item experience provenance original selected →
        retriesClearOwner project before intermediate final item experience provenance original selected attempts retry
    }
    where
    prove : ∀ {Property : Store.World → Set} → Property (published project before) →
      (∀ world → Property world → Property (published project world)) → Property final
    prove cleared preserves = retryAfterInterruptions project before intermediate final cleared preserves attempts retry

-- The operation's outcome is stated against the initial project ownership.
module Standalone (database : ℕ) (project : Text) where
  module P = Operation database

  data Category : Set where
    beliefNode patternNode beliefVector chunk chunkVector : Category
    beliefEdgeFrom beliefEdgeTo patternEdgeFrom patternEdgeTo : Category
    beliefGround patternGround chunkGround beliefOrigin patternOrigin : Category
    experienceRow sourceRow reviewTime registry assessment : Category

  ownedIDs : Category → Store.World → List UUID
  ownedIDs beliefNode before = Writes.projectBeliefs project before
  ownedIDs beliefVector before = Writes.projectBeliefs project before
  ownedIDs beliefEdgeFrom before = Writes.projectBeliefs project before
  ownedIDs beliefEdgeTo before = Writes.projectBeliefs project before
  ownedIDs beliefGround before = Writes.projectBeliefs project before
  ownedIDs beliefOrigin before = Writes.projectBeliefs project before
  ownedIDs patternNode before = Writes.projectPatterns project before
  ownedIDs patternEdgeFrom before = Writes.projectPatterns project before
  ownedIDs patternEdgeTo before = Writes.projectPatterns project before
  ownedIDs patternGround before = Writes.projectPatterns project before
  ownedIDs patternOrigin before = Writes.projectPatterns project before
  ownedIDs chunk before = projectChunks project before
  ownedIDs chunkVector before = projectChunks project before
  ownedIDs chunkGround before = projectChunks project before
  ownedIDs experienceRow before = ownedExperiences project (Store.World.learning before)
  ownedIDs sourceRow before = ownedExperiences project (Store.World.learning before)
  ownedIDs reviewTime before = ownedExperiences project (Store.World.learning before)
  ownedIDs registry before = ownedExperiences project (Store.World.learning before)
  ownedIDs assessment before = ownedExperiences project (Store.World.learning before)

  rowIDs : Category → Store.World → List UUID
  rowIDs beliefNode after = map Graph.nodeID (Store.nodes after)
  rowIDs patternNode after = map Graph.nodeID (Store.nodes after)
  rowIDs beliefVector after = map proj₁ (Store.World.beliefVectors after)
  rowIDs chunk after = map Documents.Chunk.identity (Store.World.chunks after)
  rowIDs chunkVector after = map proj₁ (Store.World.chunkVectors after)
  rowIDs beliefEdgeFrom after = map Edges.Edge.from (edgesOf after)
  rowIDs beliefEdgeTo after = map Edges.Edge.to (edgesOf after)
  rowIDs patternEdgeFrom after = map Edges.Edge.from (edgesOf after)
  rowIDs patternEdgeTo after = map Edges.Edge.to (edgesOf after)
  rowIDs beliefGround after = map Store.Ground.belief (Store.World.grounds after)
  rowIDs patternGround after = map Store.Ground.belief (Store.World.grounds after)
  rowIDs chunkGround after = map Store.Ground.chunk (Store.World.grounds after)
  rowIDs beliefOrigin after = map proj₁ (originsOf after)
  rowIDs patternOrigin after = map proj₁ (originsOf after)
  rowIDs experienceRow after = map Read.identity (Learning.World.current (Store.World.learning after))
  rowIDs sourceRow after = map sourceKey (Learning.World.sources (Store.World.learning after))
  rowIDs reviewTime after = map Learning.ReviewTime.experience (Learning.World.reviewTimes (Store.World.learning after))
  rowIDs registry after = map Candidates.Entry.experienceID
    (Publication.World.registry (Learning.World.publication (Store.World.learning after)))
  rowIDs assessment after = map Assessments.Row.experience
    (Publication.World.assessments (Learning.World.publication (Store.World.learning after)))

  data Index (before : Store.World) : Set where
    ownedRow : (category : Category) → (id : UUID) → Ranking.member id (ownedIDs category before) ≡ true → Index before
    itemKey : (experience : UUID) → (name : Text) →
      Ranking.member experience (ownedExperiences project (Store.World.learning before)) ≡ true → Index before
    history cell : (experience : UUID) →
      Ranking.member experience (ownedExperiences project (Store.World.learning before)) ≡ true → Index before
    itemOwner : (item experience : UUID) → (provenance : Text × Text) →
      ownerOf before item ≡ just (experience , provenance) →
      Ranking.member experience (ownedExperiences project (Store.World.learning before)) ≡ true → Index before

  Observation : (before : Store.World) → Index before → Set
  Observation before (ownedRow category id selected) = Bool
  Observation before (itemKey experience name selected) = Maybe UUID
  Observation before (history experience selected) = List Ledger.Version
  Observation before (cell experience selected) = Ledger.R.Cell
  Observation before (itemOwner item experience provenance original selected) = Maybe Owners.Owner

  observe : (before : Store.World) → (index : Index before) → Store.World → Observation before index
  observe before (ownedRow category id selected) after = Ranking.member id (rowIDs category after)
  observe before (itemKey experience name selected) after = Learning.World.itemKeys (Store.World.learning after) experience name
  observe before (history experience selected) after =
    Ledger.World.histories (Publication.World.ledger (Learning.World.publication (Store.World.learning after))) experience
  observe before (cell experience selected) after =
    Ledger.World.cells (Publication.World.ledger (Learning.World.publication (Store.World.learning after))) experience
  observe before (itemOwner item experience provenance original selected) after = ownerOf after item

  emptyObservation : ∀ before (index : Index before) → Observation before index
  emptyObservation before (ownedRow category id selected) = false
  emptyObservation before (itemKey experience name selected) = nothing
  emptyObservation before (history experience selected) = []
  emptyObservation before (cell experience selected) = emptyReviewCell
  emptyObservation before (itemOwner item experience provenance original selected) = nothing

  Atomic : Store.World → (effect : P.Effect) → P.Reply effect → Store.World → Set
  Atomic before (P.learning (P.T.begin db)) reply after = after ≡ before
  Atomic before (P.learning (P.T.acquire tx key)) reply after = after ≡ before
  Atomic before (P.learning (P.T.read tx)) (inj₁ failure) after = after ≡ before
  Atomic before (P.learning (P.T.read tx)) (inj₂ observed) after = (after ≡ before) × (observed ≡ before)
  Atomic before (P.learning (P.T.write tx proposed)) (inj₁ failure) after = after ≡ before
  Atomic before (P.learning (P.T.write tx proposed)) (inj₂ tt) after =
    (after ≡ before) × (proposed ≡ published project before)
  Atomic before (P.learning (P.T.allocateItem tx owner key source actor)) reply after = after ≡ before
  Atomic before (P.learning (P.T.commit tx)) reply after =
    DB.Atomic before (published project before) (P.T.receipt reply) after
  Atomic before (P.learning (P.T.rollback tx)) reply after = after ≡ before

  Successful : P.Result → Set
  Successful (P.deleted count) = ⊤
  Successful _ = ⊥

  module R = Recovery Store.World P.Effect P.Result Index P.Reply Atomic
    (λ before after → after ≡ before) Observation observe
    (λ _ world → world) Successful (λ _ → ⊤)

  trueNotFalse : true ≡ false → ⊥
  trueNotFalse ()

  absentFromRows : ∀ {A : Set} (key : A → UUID) id ids rows →
    Ranking.member id ids ≡ true → NoRows key ids rows →
    Ranking.member id (map key rows) ≡ false
  absentFromRows key id ids [] selected noRows = refl
  absentFromRows key id ids (row ∷ rest) selected (keptRow absent tail) with id ≟UUID key row
  ... | yes refl = ⊥-elim (trueNotFalse (trans (sym selected) absent))
  ... | no different = absentFromRows key id ids rest selected tail

  Change : Store.World → Store.World → Set
  Change before after = (after ≡ before) ⊎
    Σ DB.Receipt (λ receipt → P.TransactionPublication project before receipt after)

  classify : ∀ before effect reply after → Atomic before effect reply after → Change before after
  classify before (P.learning (P.T.begin db)) reply after same = inj₁ same
  classify before (P.learning (P.T.acquire tx key)) reply after same = inj₁ same
  classify before (P.learning (P.T.read tx)) (inj₁ failure) after same = inj₁ same
  classify before (P.learning (P.T.read tx)) (inj₂ observed) after (same , snapshot) = inj₁ same
  classify before (P.learning (P.T.write tx proposed)) (inj₁ failure) after same = inj₁ same
  classify before (P.learning (P.T.write tx proposed)) (inj₂ tt) after (same , staged) = inj₁ same
  classify before (P.learning (P.T.allocateItem tx owner key source actor)) reply after same = inj₁ same
  classify before (P.learning (P.T.commit tx)) reply after commit = inj₂ (P.T.receipt reply , commit)
  classify before (P.learning (P.T.rollback tx)) reply after same = inj₁ same

  afterChange : ∀ {before middle after} → Change before middle →
    P.Interruptions project middle after → P.Interruptions project before after
  afterChange (inj₁ refl) later = later
  afterChange (inj₂ (receipt , commit)) later =
    P.oneInterruption (P.E.stopped (P.start project)) commit later

  interruption : ∀ {program before after} → R.Interrupted program before after →
    P.Interruptions project before after
  interruption (R.stopped refl) = P.none
  interruption (R.replied {effect = effect} {reply = reply} {before = before} {middle = middle} atomic rest) =
    afterChange (classify before effect reply middle atomic) (interruption rest)

  failedAttempt : ∀ {program before after} → R.Failed program before after →
    P.Interruptions project before after
  failedAttempt (R.failedReturn failed) = P.none
  failedAttempt (R.failedReply {effect = effect} {reply = reply} {before = before} {middle = middle} atomic rest) =
    afterChange (classify before effect reply middle atomic) (failedAttempt rest)

  appendInterruptions : ∀ {before middle after} → P.Interruptions project before middle →
    P.Interruptions project middle after → P.Interruptions project before after
  appendInterruptions P.none later = later
  appendInterruptions (P.oneInterruption prefix publication rest) later =
    P.oneInterruption prefix publication (appendInterruptions rest later)

  interruptions : ∀ {program before after} → R.Attempts* program before after →
    P.Interruptions project before after
  interruptions R.noAttempts = P.none
  interruptions (R.afterInterruption first rest) =
    appendInterruptions (interruption first) (interruptions rest)
  interruptions (R.afterFailure first rest) =
    appendInterruptions (failedAttempt first) (interruptions rest)

  committedEvents : ∀ before after tx snapshot →
    R.Applied
      ((P.learning (P.T.begin database) , inj₂ tx) ∷
       (P.learning (P.T.acquire tx 671942183) , inj₂ tt) ∷
       (P.learning (P.T.read tx) , inj₂ snapshot) ∷
       (P.learning (P.T.write tx (published project snapshot)) , inj₂ tt) ∷
       (P.learning (P.T.commit tx) , P.T.committed) ∷ []) before after →
    P.TransactionPublication project before DB.committed after
  committedEvents before after tx snapshot
    (R.appliedEffect begin (R.appliedEffect lock (R.appliedEffect (read , observed)
      (R.appliedEffect (write , staged) (R.appliedEffect commit R.noEffects)))))
    rewrite begin | lock | read | write = commit

  committedSnapshot : ∀ before after tx snapshot →
    R.Applied
      ((P.learning (P.T.begin database) , inj₂ tx) ∷
       (P.learning (P.T.acquire tx 671942183) , inj₂ tt) ∷
       (P.learning (P.T.read tx) , inj₂ snapshot) ∷
       (P.learning (P.T.write tx (published project snapshot)) , inj₂ tt) ∷
       (P.learning (P.T.commit tx) , P.T.committed) ∷ []) before after →
    snapshot ≡ before
  committedSnapshot before after tx snapshot
    (R.appliedEffect begin (R.appliedEffect lock (R.appliedEffect (read , observed) rest)))
    rewrite begin | lock = observed

  actualCompletion : ∀ before after tx snapshot count →
    count ≡ deletedCount project snapshot →
    P.E.Runs (P.start project)
      ((P.learning (P.T.begin database) , inj₂ tx) ∷
       (P.learning (P.T.acquire tx 671942183) , inj₂ tt) ∷
       (P.learning (P.T.read tx) , inj₂ snapshot) ∷
       (P.learning (P.T.write tx (published project snapshot)) , inj₂ tt) ∷
       (P.learning (P.T.commit tx) , P.T.committed) ∷ []) (P.deleted count) →
    R.Applied
      ((P.learning (P.T.begin database) , inj₂ tx) ∷
       (P.learning (P.T.acquire tx 671942183) , inj₂ tt) ∷
       (P.learning (P.T.read tx) , inj₂ snapshot) ∷
       (P.learning (P.T.write tx (published project snapshot)) , inj₂ tt) ∷
       (P.learning (P.T.commit tx) , P.T.committed) ∷ []) before after →
    P.Completed project before after
  actualCompletion before after tx snapshot count countMatches execution effects
    with committedSnapshot before after tx snapshot effects
  ... | refl rewrite countMatches =
    P.completed tx execution (committedEvents before after tx before effects)

  originalCompletion : ∀ before after → R.Completed (P.start project) before after →
    P.Completed project before after
  originalCompletion before after completed with R.completedTrace completed
  ... | events , P.transactionResult result , middle , execution , () , effects , finalized
  ... | events , P.deleted count , middle , execution , tt , effects , finalized
    with P.successfulTrace project events count execution
  ... | tx , snapshot , trace , countMatches rewrite trace | finalized =
    actualCompletion before middle tx snapshot count countMatches execution effects

  deletionConverges : ∀ before middle after →
    R.Attempts* (P.start project) before middle → R.Completed (P.start project) middle after →
    Deleted project before after
  deletionConverges before middle after attempts completed =
    P.deletionConverges project before middle after (interruptions attempts) (originalCompletion middle after completed)

  intendedDeleted : ∀ before {middle after} → P.Completed project middle after →
    Deleted project before (published project before)
  intendedDeleted before (P.completed tx execution publication) =
    P.deletionConverges project before before (published project before) P.none
      (P.completed tx (P.possibleSuccess project tx before) DB.committedAll)

  cleared : ∀ before after → Deleted project before after →
    (index : Index before) → observe before index after ≡ emptyObservation before index
  cleared before after deletion (ownedRow beliefNode id selected) =
    absentFromRows Graph.nodeID id _ (Store.nodes after) selected (Deleted.beliefs deletion)
  cleared before after deletion (ownedRow patternNode id selected) =
    absentFromRows Graph.nodeID id _ (Store.nodes after) selected (Deleted.patterns deletion)
  cleared before after deletion (ownedRow beliefVector id selected) =
    absentFromRows proj₁ id _ (Store.World.beliefVectors after) selected (Deleted.beliefVectors deletion)
  cleared before after deletion (ownedRow chunk id selected) =
    absentFromRows Documents.Chunk.identity id _ (Store.World.chunks after) selected (Deleted.chunks deletion)
  cleared before after deletion (ownedRow chunkVector id selected) =
    absentFromRows proj₁ id _ (Store.World.chunkVectors after) selected (Deleted.chunkVectors deletion)
  cleared before after deletion (ownedRow beliefEdgeFrom id selected) =
    absentFromRows Edges.Edge.from id _ (edgesOf after) selected (Deleted.beliefEdgesFrom deletion)
  cleared before after deletion (ownedRow beliefEdgeTo id selected) =
    absentFromRows Edges.Edge.to id _ (edgesOf after) selected (Deleted.beliefEdgesTo deletion)
  cleared before after deletion (ownedRow patternEdgeFrom id selected) =
    absentFromRows Edges.Edge.from id _ (edgesOf after) selected (Deleted.patternEdgesFrom deletion)
  cleared before after deletion (ownedRow patternEdgeTo id selected) =
    absentFromRows Edges.Edge.to id _ (edgesOf after) selected (Deleted.patternEdgesTo deletion)
  cleared before after deletion (ownedRow beliefGround id selected) =
    absentFromRows Store.Ground.belief id _ (Store.World.grounds after) selected (Deleted.beliefGrounds deletion)
  cleared before after deletion (ownedRow patternGround id selected) =
    absentFromRows Store.Ground.belief id _ (Store.World.grounds after) selected (Deleted.patternGrounds deletion)
  cleared before after deletion (ownedRow chunkGround id selected) =
    absentFromRows Store.Ground.chunk id _ (Store.World.grounds after) selected (Deleted.chunkGrounds deletion)
  cleared before after deletion (ownedRow beliefOrigin id selected) =
    absentFromRows proj₁ id _ (originsOf after) selected (Deleted.beliefOrigins deletion)
  cleared before after deletion (ownedRow patternOrigin id selected) =
    absentFromRows proj₁ id _ (originsOf after) selected (Deleted.patternOrigins deletion)
  cleared before after deletion (ownedRow experienceRow id selected) =
    absentFromRows Read.identity id _ (Learning.World.current (Store.World.learning after)) selected (Deleted.experiences deletion)
  cleared before after deletion (ownedRow sourceRow id selected) =
    absentFromRows sourceKey id _ (Learning.World.sources (Store.World.learning after)) selected (Deleted.sources deletion)
  cleared before after deletion (ownedRow reviewTime id selected) =
    absentFromRows Learning.ReviewTime.experience id _ (Learning.World.reviewTimes (Store.World.learning after)) selected (Deleted.reviewTimes deletion)
  cleared before after deletion (ownedRow registry id selected) =
    absentFromRows Candidates.Entry.experienceID id _
      (Publication.World.registry (Learning.World.publication (Store.World.learning after))) selected (Deleted.registry deletion)
  cleared before after deletion (ownedRow assessment id selected) =
    absentFromRows Assessments.Row.experience id _
      (Publication.World.assessments (Learning.World.publication (Store.World.learning after))) selected (Deleted.assessments deletion)
  cleared before after deletion (itemKey experience name selected) = Deleted.itemKeys deletion experience name selected
  cleared before after deletion (history experience selected) = Deleted.histories deletion experience selected
  cleared before after deletion (cell experience selected) = Deleted.cells deletion experience selected
  cleared before after deletion (itemOwner item experience provenance original selected) =
    Deleted.owners deletion item experience provenance original selected

  converges : ∀ (input : ⊤) before middle after →
    R.Attempts* (P.start project) before middle → R.Completed (P.start project) middle after →
    ∀ index → observe before index after ≡ observe before index (published project before)
  converges input before middle after attempts completed index =
    trans (cleared before after (deletionConverges before middle after attempts completed) index)
      (sym (cleared before (published project before)
        (intendedDeleted before (originalCompletion middle after completed)) index))

  interruptedUnchanged : ∀ {before after} → R.Interrupted (P.start project) before after → after ≡ before
  interruptedUnchanged (R.stopped refl) = refl
  interruptedUnchanged (R.replied {reply = inj₁ error} refl ())
  interruptedUnchanged (R.replied {reply = inj₂ tx} refl (R.stopped refl)) = refl
  interruptedUnchanged (R.replied {reply = inj₂ tx} refl
    (R.replied {reply = inj₁ error} refl (R.stopped refl))) = refl
  interruptedUnchanged (R.replied {reply = inj₂ tx} refl
    (R.replied {reply = inj₁ error} refl (R.replied refl ())))
  interruptedUnchanged (R.replied {reply = inj₂ tx} refl
    (R.replied {reply = inj₂ tt} refl (R.stopped refl))) = refl
  interruptedUnchanged (R.replied {reply = inj₂ tx} refl
    (R.replied {reply = inj₂ tt} refl
    (R.replied {reply = inj₁ error} refl (R.stopped refl)))) = refl
  interruptedUnchanged (R.replied {reply = inj₂ tx} refl
    (R.replied {reply = inj₂ tt} refl
    (R.replied {reply = inj₁ error} refl (R.replied refl ()))))
  interruptedUnchanged (R.replied {reply = inj₂ tx} refl
    (R.replied {reply = inj₂ tt} refl
    (R.replied {reply = inj₂ snapshot} (refl , refl) (R.stopped refl)))) = refl
  interruptedUnchanged (R.replied {reply = inj₂ tx} refl
    (R.replied {reply = inj₂ tt} refl
    (R.replied {reply = inj₂ snapshot} (refl , refl)
    (R.replied {reply = inj₁ error} refl (R.stopped refl))))) = refl
  interruptedUnchanged (R.replied {reply = inj₂ tx} refl
    (R.replied {reply = inj₂ tt} refl
    (R.replied {reply = inj₂ snapshot} (refl , refl)
    (R.replied {reply = inj₁ error} refl (R.replied refl ())))))
  interruptedUnchanged (R.replied {reply = inj₂ tx} refl
    (R.replied {reply = inj₂ tt} refl
    (R.replied {reply = inj₂ snapshot} (refl , refl)
    (R.replied {reply = inj₂ tt} (refl , staged) (R.stopped refl))))) = refl
  interruptedUnchanged (R.replied {reply = inj₂ tx} refl
    (R.replied {reply = inj₂ tt} refl
    (R.replied {reply = inj₂ snapshot} (refl , refl)
    (R.replied {reply = inj₂ tt} (refl , staged) (R.replied {reply = P.T.committed} commit ())))))
  interruptedUnchanged (R.replied {reply = inj₂ tx} refl
    (R.replied {reply = inj₂ tt} refl
    (R.replied {reply = inj₂ snapshot} (refl , refl)
    (R.replied {reply = inj₂ tt} (refl , staged) (R.replied {reply = P.T.aborted detail} commit ())))))

  failedUnchanged : ∀ {before after} → R.Failed (P.start project) before after → after ≡ before
  failedUnchanged (R.failedReply {reply = inj₁ error} refl (R.failedReturn failed)) = refl
  failedUnchanged (R.failedReply {reply = inj₂ tx} refl
    (R.failedReply {reply = inj₁ error} refl (R.failedReply refl (R.failedReturn failed)))) = refl
  failedUnchanged (R.failedReply {reply = inj₂ tx} refl
    (R.failedReply {reply = inj₂ tt} refl
    (R.failedReply {reply = inj₁ error} refl (R.failedReply refl (R.failedReturn failed))))) = refl
  failedUnchanged (R.failedReply {reply = inj₂ tx} refl
    (R.failedReply {reply = inj₂ tt} refl
    (R.failedReply {reply = inj₂ snapshot} (refl , refl)
    (R.failedReply {reply = inj₁ error} refl (R.failedReply refl (R.failedReturn failed)))))) = refl
  failedUnchanged (R.failedReply {reply = inj₂ tx} refl
    (R.failedReply {reply = inj₂ tt} refl
    (R.failedReply {reply = inj₂ snapshot} (refl , refl)
    (R.failedReply {reply = inj₂ tt} (refl , staged)
    (R.failedReply {reply = P.T.committed} commit (R.failedReturn failed)))))) = ⊥-elim (failed tt)
  failedUnchanged (R.failedReply {reply = inj₂ tx} refl
    (R.failedReply {reply = inj₂ tt} refl
    (R.failedReply {reply = inj₂ snapshot} (refl , refl)
    (R.failedReply {reply = inj₂ tt} (refl , staged)
    (R.failedReply {reply = P.T.aborted detail} DB.abortedNone (R.failedReturn failed)))))) = refl

  atomicDeletion : R.AllOrNothing ⊤
  atomicDeletion = record
    { expected = λ _ before index → observe before index (published project before)
    ; script = λ _ → P.start project
    ; interruptedUnchanged = λ _ _ _ attempt → interruptedUnchanged attempt
    ; failedUnchanged = λ _ _ _ attempt → failedUnchanged attempt
    ; achieves = λ input before after completed → converges input before before after R.noAttempts completed
    }
  module CertifiedDeletion = R.Transactional atomicDeletion
  recovery : R.Recoverable ⊤
  recovery = CertifiedDeletion.transactional
