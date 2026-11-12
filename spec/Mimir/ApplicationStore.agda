{-# OPTIONS --safe #-}
-- Shared physical application state. This can represent inconsistent legacy
-- stores; desired paired-document publication is separately constrained by
-- DocumentStore.Storage. Merely representing a bad state does not permit it
-- as the result of an operation governed by that stronger contract.
module Mimir.ApplicationStore where

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_)
open import Data.Float.Base using (Float; _+_)
open import Data.List using (List; []; _∷_; map; filterᵇ; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Mimir.UUIDGroups using (UUID; _≟UUID_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (does; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.LearningStore as Learning
import Mimir.ReviewPreparationPublication as Publication
import Mimir.CandidateGraph as Graph
import Mimir.CandidateRegistry as Registry
import Mimir.ReviewEdges as Edges
import Mimir.DocumentStore as Documents
import Mimir.RetrievalRanking as Ranking
import Mimir.LearningRecompute as Recompute
import Mimir.IndependentProvenance as Independent
import Mimir.Binary64 as Binary64

-- At an external embedding boundary each binary32 component may be widened
-- exactly to Float for transport/storage description. No binary64 dot product
-- or binary64 ranking is substituted for pgvector's operations here.
Vector = List Float

record Ground : Set where
  constructor ground
  field chunk belief : UUID; weight : Float

record World : Set where
  constructor world
  field
    learning : Learning.World
    chunks : List Documents.Chunk
    beliefVectors chunkVectors : List (UUID × Vector)
    grounds : List Ground

nodes : World → List Graph.Node
nodes w = Publication.World.nodes (Learning.World.publication (World.learning w))

edges : World → List Edges.Edge
edges w = Publication.World.edges (Learning.World.publication (World.learning w))

beliefs : World → List Graph.BeliefValues
beliefs w = Recompute.beliefs (nodes w)

patterns : List Graph.Node → List Graph.PatternValues
patterns [] = []
patterns (Graph.beliefNode b ∷ ns) = patterns ns
patterns (Graph.patternNode p ∷ ns) = p ∷ patterns ns

setNodes : List Graph.Node → World → World
setNodes ns w = record w { learning = record learn { publication = record pub { nodes = ns } } }
  where learn = World.learning w; pub = Learning.World.publication learn

insertNode : Graph.Node → World → World
insertNode node w = setNodes (nodes w ++ (node ∷ [])) w

retire : List UUID → Registry.Registry → Registry.Registry
retire ids = map (λ r → record r { retired = Registry.Entry.retired r ∨ Ranking.member (Registry.Entry.nodeID r) ids })

detach : List UUID → List Edges.Edge → List Edges.Edge
detach ids = filterᵇ (λ e → not (Ranking.member (Edges.Edge.from e) ids ∨ Ranking.member (Edges.Edge.to e) ids))

-- Historical experience/review rows and assessment contributions are retained
-- on identity deletion. Candidate reservations become retired, never reusable.
removeNodes : List UUID → Bool → World → World
removeNodes ids retireCandidates w = record w
  { learning = record learn
      { publication = record pub
          { nodes = filterᵇ (λ n → not (Ranking.member (Graph.nodeID n) ids)) (Publication.World.nodes pub)
          ; edges = detach ids (Publication.World.edges pub)
          ; registry = registry }
      ; independentOrigins = filterᵇ (λ row → not (Ranking.member (proj₁ row) ids)) (Learning.World.independentOrigins learn) }
  ; grounds = filterᵇ (λ e → not (Ranking.member (Ground.belief e) ids)) (World.grounds w) }
  where
  learn = World.learning w
  pub = Learning.World.publication learn
  registry = ifRetire retireCandidates
    where
    ifRetire : Bool → Registry.Registry
    ifRetire true = retire ids (Publication.World.registry pub)
    ifRetire false = Publication.World.registry pub

removeBeliefVectors : List UUID → World → World
removeBeliefVectors ids w = record w
  { beliefVectors = filterᵇ (λ row → not (Ranking.member (proj₁ row) ids)) (World.beliefVectors w) }

removeChunks : List UUID → World → World
removeChunks ids w = record w
  { chunks = filterᵇ (λ c → not (Ranking.member (Documents.Chunk.identity c) ids)) (World.chunks w)
  ; grounds = filterᵇ (λ e → not (Ranking.member (Ground.chunk e) ids)) (World.grounds w) }

removeChunkVectors : List UUID → World → World
removeChunkVectors ids w = record w
  { chunkVectors = filterᵇ (λ row → not (Ranking.member (proj₁ row) ids)) (World.chunkVectors w) }

putVector : UUID → Vector → List (UUID × Vector) → List (UUID × Vector)
putVector id vector [] = (id , vector) ∷ []
putVector id vector ((key , old) ∷ rest) with id ≟UUID key
... | yes _ = (key , vector) ∷ rest
... | no _ = (key , old) ∷ putVector id vector rest

groundingMasses : World → List (UUID × Float)
groundingMasses w = map (λ e → Ground.belief e , Ground.weight e)
  (filterᵇ (λ e → Ranking.member (Ground.belief e) (map Graph.BeliefValues.identity (beliefs w)) ∧
    Ranking.member (Ground.chunk e) (map Documents.Chunk.identity (World.chunks w))) (World.grounds w))

-- Learning transactions read GROUNDS from their same physical snapshot.
-- The learning-only model's grounding field is a projection, never a second
-- independently mutable store. Publication writes back only learning columns.
learningView : World → Learning.World
learningView w = record (World.learning w) { grounding = groundingMasses w }

installLearning : Learning.World → World → World
installLearning value w = record w
  { learning = record value { grounding = groundingMasses w } }

learningPublicationPreservesGrounds : ∀ value w →
  World.grounds (installLearning value w) ≡ World.grounds w
learningPublicationPreservesGrounds value w = refl

learningPublicationPreservesChunks : ∀ value w →
  World.chunks (installLearning value w) ≡ World.chunks w
learningPublicationPreservesChunks value w = refl

learningReadUsesPhysicalGrounds : ∀ w →
  Learning.World.grounding (learningView w) ≡ groundingMasses w
learningReadUsesPhysicalGrounds w = refl

chunk : UUID → List Documents.Chunk → Maybe Documents.Chunk
chunk id [] = nothing
chunk id (c ∷ cs) with id ≟UUID Documents.Chunk.identity c
... | yes _ = just c
... | no _ = chunk id cs

documentIDs : Text → World → List UUID
documentIDs path w = map Documents.Chunk.identity
  (filterᵇ (λ c → does (path ≟Text Documents.Chunk.document c)) (World.chunks w))

retirementKeepsIdentities : ∀ ids entries → map Registry.Entry.nodeID (retire ids entries) ≡ map Registry.Entry.nodeID entries
retirementKeepsIdentities ids [] = refl
retirementKeepsIdentities ids (e ∷ es) = cong (Registry.Entry.nodeID e ∷_) (retirementKeepsIdentities ids es)

deletionPreservesSourceHistory : ∀ ids retiring w →
  Learning.World.sources (World.learning (removeNodes ids retiring w)) ≡ Learning.World.sources (World.learning w)
deletionPreservesSourceHistory ids retiring w = refl
