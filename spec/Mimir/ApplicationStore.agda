{-# OPTIONS --safe #-}
-- Shared physical application state. This can represent inconsistent legacy
-- stores; desired paired-document publication is separately constrained by
-- DocumentStore.Storage. Merely representing a bad state does not permit it
-- as the result of an operation governed by that stronger contract.
module Mimir.ApplicationStore where

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_)
open import Data.Float.Base using (Float; _+_)
open import Data.Empty using (⊥-elim)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_; map; filterᵇ; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Nullary using (Dec; does; yes; no; ¬_; _×-dec_)
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
import Mimir.StructuredValue as Wire
import Mimir.LearningHistoryWire as RawHistory

-- At an external embedding boundary each binary32 component may be widened
-- exactly to Float for transport/storage description. No binary64 dot product
-- or binary64 ranking is substituted for pgvector's operations here.
Vector = List Float

record Ground : Set where
  constructor ground
  field chunk belief : ℕ; weight : Float

-- These are the five existing PostgreSQL operation tables, not an operation's
-- private execution world. UUIDs/times arrive from PostgreSQL; no allocator or
-- uniqueness axiom is introduced here. JSONB admission remains at its boundary.
record ReservationRow : Set where
  constructor reservationRow
  field token : ℕ; reservedAt : ℤ

record RequestKeyRow : Set where
  constructor requestKeyRow
  field requestKey : Text; token : ℕ

record BindingRow : Set where
  constructor bindingRow
  field token : ℕ; operation : Text; arguments settings : Wire.Value; boundAt : ℤ

record PlanRow : Set where
  constructor planRow
  field token : ℕ; plan : Wire.Value

record SavedReplyRow : Set where
  constructor savedReplyRow
  field token : ℕ; step : Text; reply : Wire.Value

record OperationTables : Set where
  constructor operationTables
  field
    reservations : List ReservationRow
    requestKeys : List RequestKeyRow
    bindings : List BindingRow
    plans : List PlanRow
    savedReplies : List SavedReplyRow

record World : Set where
  constructor world
  field
    learning : Learning.World
    chunks : List Documents.Chunk
    beliefVectors chunkVectors : List (ℕ × Vector)
    grounds : List Ground
    history : RawHistory.Database -- original JSONB, including older payload shapes
    operations : OperationTables

replyKey? : ∀ token step row → Dec (token ≡ SavedReplyRow.token row × step ≡ SavedReplyRow.step row)
replyKey? token step row = (token ≟ SavedReplyRow.token row) ×-dec (step ≟Text SavedReplyRow.step row)

lookupReply : ℕ → Text → List SavedReplyRow → Maybe Wire.Value
lookupReply token step [] = nothing
lookupReply token step (row ∷ rest) with replyKey? token step row
... | yes _ = just (SavedReplyRow.reply row)
... | no _ = lookupReply token step rest

lookupSaved : World → ℕ → Text → Maybe Wire.Value
lookupSaved before token step = lookupReply token step (OperationTables.savedReplies (World.operations before))

-- The executor returns an already saved answer rather than replacing it.
saveAnswer : World → ℕ → Text → Wire.Value → World
saveAnswer before token step answer with lookupSaved before token step
... | just _ = before
... | nothing = record before { operations = record tables
  { savedReplies = savedReplyRow token step answer ∷ OperationTables.savedReplies tables } }
  where tables = World.operations before

originalAnswer : World → ℕ → Text → Wire.Value → Wire.Value
originalAnswer before token step proposed with lookupSaved before token step
... | just saved = saved
... | nothing = proposed

headReplyReadable : ∀ token step answer rest →
  lookupReply token step (savedReplyRow token step answer ∷ rest) ≡ just answer
headReplyReadable token step answer rest with replyKey? token step (savedReplyRow token step answer)
... | yes _ = refl
... | no impossible = ⊥-elim (impossible (refl , refl))

savedAnswerReadable : ∀ before token step proposed →
  lookupSaved (saveAnswer before token step proposed) token step ≡
    just (originalAnswer before token step proposed)
savedAnswerReadable before token step proposed with lookupSaved before token step in observed
... | just answer = observed
... | nothing = headReplyReadable token step proposed _

savedAnswerUnchanged : ∀ before token step original proposed →
  lookupSaved before token step ≡ just original → saveAnswer before token step proposed ≡ before
savedAnswerUnchanged before token step original proposed observed rewrite observed = refl

retryKeepsSavedAnswer : ∀ before token step first second →
  saveAnswer (saveAnswer before token step first) token step second ≡ saveAnswer before token step first
retryKeepsSavedAnswer before token step first second =
  savedAnswerUnchanged (saveAnswer before token step first) token step
    (originalAnswer before token step first) second (savedAnswerReadable before token step first)

otherSavedAnswerPreserved : ∀ before token step proposed otherToken otherStep →
  ¬ (otherToken ≡ token × otherStep ≡ step) →
  lookupSaved (saveAnswer before token step proposed) otherToken otherStep ≡ lookupSaved before otherToken otherStep
otherSavedAnswerPreserved before token step proposed otherToken otherStep different with lookupSaved before token step
... | just _ = refl
... | nothing with replyKey? otherToken otherStep (savedReplyRow token step proposed)
... | yes same = ⊥-elim (different same)
... | no _ = refl

-- This projection is only a frame assertion. Recovery still observes the
-- complete World, including all operation tables, without a smaller-world API.
BusinessSnapshot = Learning.World × List Documents.Chunk ×
  List (ℕ × Vector) × List (ℕ × Vector) × List Ground × RawHistory.Database

businessSnapshot : World → BusinessSnapshot
businessSnapshot before = World.learning before , World.chunks before ,
  World.beliefVectors before , World.chunkVectors before , World.grounds before , World.history before

savingAnswerPreservesBusiness : ∀ before token step proposed →
  businessSnapshot (saveAnswer before token step proposed) ≡ businessSnapshot before
savingAnswerPreservesBusiness before token step proposed with lookupSaved before token step
... | just _ = refl
... | nothing = refl

savingAnswerPreservesOperationInputs : ∀ before token step proposed →
  let prior = World.operations before
      after = World.operations (saveAnswer before token step proposed)
  in (OperationTables.reservations after , OperationTables.requestKeys after ,
      OperationTables.bindings after , OperationTables.plans after) ≡
     (OperationTables.reservations prior , OperationTables.requestKeys prior ,
      OperationTables.bindings prior , OperationTables.plans prior)
savingAnswerPreservesOperationInputs before token step proposed with lookupSaved before token step
... | just _ = refl
... | nothing = refl

nodes : World → List Graph.Node
nodes w = Publication.World.nodes (Learning.World.publication (World.learning w))

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

retire : List ℕ → Registry.Registry → Registry.Registry
retire ids = map (λ r → record r { retired = Registry.Entry.retired r ∨ Ranking.member (Registry.Entry.nodeID r) ids })

detach : List ℕ → List Edges.Edge → List Edges.Edge
detach ids = filterᵇ (λ e → not (Ranking.member (Edges.Edge.from e) ids ∨ Ranking.member (Edges.Edge.to e) ids))

-- Historical experience/review rows and assessment contributions are retained
-- on identity deletion. Candidate reservations become retired, never reusable.
removeNodes : List ℕ → Bool → World → World
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

removeBeliefVectors : List ℕ → World → World
removeBeliefVectors ids w = record w
  { beliefVectors = filterᵇ (λ row → not (Ranking.member (proj₁ row) ids)) (World.beliefVectors w) }

removeChunks : List ℕ → World → World
removeChunks ids w = record w
  { chunks = filterᵇ (λ c → not (Ranking.member (Documents.Chunk.identity c) ids)) (World.chunks w)
  ; grounds = filterᵇ (λ e → not (Ranking.member (Ground.chunk e) ids)) (World.grounds w) }

removeChunkVectors : List ℕ → World → World
removeChunkVectors ids w = record w
  { chunkVectors = filterᵇ (λ row → not (Ranking.member (proj₁ row) ids)) (World.chunkVectors w) }

putVector : ℕ → Vector → List (ℕ × Vector) → List (ℕ × Vector)
putVector id vector [] = (id , vector) ∷ []
putVector id vector ((key , old) ∷ rest) with id ≟ key
... | yes _ = (key , vector) ∷ rest
... | no _ = (key , old) ∷ putVector id vector rest

groundingMasses : World → List (ℕ × Float)
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

chunk : ℕ → List Documents.Chunk → Maybe Documents.Chunk
chunk id [] = nothing
chunk id (c ∷ cs) with id ≟ Documents.Chunk.identity c
... | yes _ = just c
... | no _ = chunk id cs

documentIDs : Text → World → List ℕ
documentIDs path w = map Documents.Chunk.identity
  (filterᵇ (λ c → does (path ≟Text Documents.Chunk.document c)) (World.chunks w))

retirementKeepsIdentities : ∀ ids entries → map Registry.Entry.nodeID (retire ids entries) ≡ map Registry.Entry.nodeID entries
retirementKeepsIdentities ids [] = refl
retirementKeepsIdentities ids (e ∷ es) = cong (Registry.Entry.nodeID e ∷_) (retirementKeepsIdentities ids es)

deletionPreservesSourceHistory : ∀ ids retiring w →
  Learning.World.sources (World.learning (removeNodes ids retiring w)) ≡ Learning.World.sources (World.learning w)
deletionPreservesSourceHistory ids retiring w = refl
