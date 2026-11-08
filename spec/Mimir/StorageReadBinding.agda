{-# OPTIONS --safe #-}
-- Bind read effects to the selected table/graph view at each READ COMMITTED
-- statement. Pgvector cosine evaluation and PostgreSQL float ordering are
-- dependency operations; Mimir owns filtering, the selected table and LIMIT.
module Mimir.StorageReadBinding where

open import Data.Bool using (Bool; true; false)
open import Data.Float.Base using (Float)
open import Data.List using (List; []; _∷_; map; filterᵇ)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _≤?_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.ApplicationStore as Store
import Mimir.LearningStore as Learning
import Mimir.LearningContextProtocol as ContextProtocol
import Mimir.DocumentStore as Documents
import Mimir.RetrievalRanking as Ranking
import Mimir.RetrievalProtocol as Retrieval
import Mimir.RetrievalReadContract as RetrievalReads
import Mimir.DocumentQuery as Query
import Mimir.EvidenceRead as Evidence
import Mimir.StorageSemantics as Semantics
import Mimir.GraphReadProtocol as Graph
import Mimir.GraphRecords as Records
import Mimir.GraphNumerics as Numeric
import Mimir.InferenceProtocol as Inference
import Mimir.DatabaseReadCommitted as Committed
import Mimir.Recovery as Recovery
import Mimir.PublicEncoding as Encoding
import Mimir.StructuredValue as Wire
import Mimir.LearningCandidates as Candidates
import Mimir.LearningCapabilities as Capabilities

eligibleVectors : Maybe (List ℕ) → List (ℕ × Store.Vector) → List (ℕ × Store.Vector)
eligibleVectors nothing rows = rows
eligibleVectors (just ids) rows = filterᵇ (λ row → Ranking.member (proj₁ row) ids) rows

record VectorOperations : Set where
  field cosineDistance : Store.Vector → Store.Vector → Float
        databaseLessEqual : Float → Float → Bool

module Vectors (ops : VectorOperations) where
  data Ordered (query : Store.Vector) : List (ℕ × Store.Vector) → Set where
    empty : Ordered query []
    one : ∀ row → Ordered query (row ∷ [])
    more : ∀ first second rest →
      VectorOperations.databaseLessEqual ops
        (VectorOperations.cosineDistance ops query (proj₂ first))
        (VectorOperations.cosineDistance ops query (proj₂ second)) ≡ true →
      Ordered query (second ∷ rest) → Ordered query (first ∷ second ∷ rest)

  -- This base ordering allows equal distances in either order. Belief search
  -- additionally requires StableSelected below. IDs are SQL table keys;
  -- absent graph endpoints are not prefiltered by vector-only SQL statements.
  record Selected (query : Store.Vector) (limit : Ranking.Selection) (filter : Maybe (List ℕ))
    (rows : List (ℕ × Store.Vector)) (result : List ℕ) : Set where
    field sorted : List (ℕ × Store.Vector)
          complete : sorted ↭ eligibleVectors filter rows
          ordered : Ordered query sorted
          capped : result ≡ Ranking.cap limit (map proj₁ sorted)

  -- Ordered already requires the forward distance comparison. If the reverse
  -- comparison also holds, ascending identity decides that equal-distance tie.
  tieBefore : Store.Vector → (ℕ × Store.Vector) → (ℕ × Store.Vector) → Bool
  tieBefore query first second with VectorOperations.databaseLessEqual ops
    (VectorOperations.cosineDistance ops query (proj₂ second))
    (VectorOperations.cosineDistance ops query (proj₂ first))
  ... | false = true
  ... | true = does (proj₁ first ≤? proj₁ second)

  StableTies : Store.Vector → List (ℕ × Store.Vector) → Set
  StableTies query [] = ⊤
  StableTies query (row ∷ []) = ⊤
  StableTies query (first ∷ second ∷ rest) =
    tieBefore query first second ≡ true × StableTies query (second ∷ rest)

  record StableSelected (query : Store.Vector) (limit : Ranking.Selection) (filter : Maybe (List ℕ))
    (rows : List (ℕ × Store.Vector)) (result : List ℕ) : Set where
    field selected : Selected query limit filter rows result
          stableTies : StableTies query (Selected.sorted selected)

  equalDistancesUseIdentity : ∀ query first second →
    VectorOperations.databaseLessEqual ops
      (VectorOperations.cosineDistance ops query (proj₂ second))
      (VectorOperations.cosineDistance ops query (proj₂ first)) ≡ true →
    tieBefore query first second ≡ does (proj₁ first ≤? proj₁ second)
  equalDistancesUseIdentity query first second equal rewrite equal = refl

projectChunks : Text → Store.World → List ℕ
projectChunks project snapshot = map Documents.Chunk.identity
  (filterᵇ (λ chunk → same (Documents.Chunk.project chunk)) (Store.World.chunks snapshot))
  where
  same : Maybe Text → Bool
  same nothing = Data.Bool.false
  same (just actual) = does (actual ≟Text project)

evidenceGrounds : List ℕ → Store.World → List Store.Ground
evidenceGrounds ids snapshot = filterᵇ (λ ground → Ranking.member (Store.Ground.belief ground) ids)
  (Semantics.groundRows snapshot)

EvidenceMeaning : Store.World → (effect : Evidence.Effect) → Evidence.Reply effect → Set
EvidenceMeaning snapshot (Evidence.readGrounds ids) (inj₁ error) = ⊤
EvidenceMeaning snapshot (Evidence.readGrounds ids) (inj₂ rows) = rows ↭ evidenceGrounds ids snapshot
EvidenceMeaning snapshot (Evidence.readChunk id) (inj₁ error) = ⊤
EvidenceMeaning snapshot (Evidence.readChunk id) (inj₂ row) = row ≡ Store.chunk id (Store.World.chunks snapshot)
EvidenceMeaning snapshot (Evidence.openSnapshot belief) (inj₁ error) = ⊤
EvidenceMeaning snapshot (Evidence.openSnapshot belief) (inj₂ (tx , first , rows)) =
  first ≡ snapshot × rows ↭ evidenceGrounds (belief ∷ []) snapshot
EvidenceMeaning snapshot (Evidence.readSnapshotChunk tx first id) (inj₁ error) = ⊤
EvidenceMeaning snapshot (Evidence.readSnapshotChunk tx first id) (inj₂ row) =
  snapshot ≡ first × row ≡ Store.chunk id (Store.World.chunks snapshot)
EvidenceMeaning snapshot (Evidence.closeSnapshot tx) reply = ⊤

module Read (ops : VectorOperations) where
  module V = Vectors ops

  data DocumentMeaning (snapshot : Store.World) : (effect : Query.Effect) → Query.Reply effect → Set where
    opened : ∀ tx → DocumentMeaning snapshot Query.beginRead (inj₂ tx)
    openFailed : ∀ error → DocumentMeaning snapshot Query.beginRead (inj₁ error)
    closed : ∀ tx reply → DocumentMeaning snapshot (Query.closeRead tx) reply
    project : ∀ project rows → rows ↭ projectChunks project snapshot →
      DocumentMeaning snapshot (Query.projectChunkIDs project) (inj₂ rows)
    projectFailed : ∀ project error → DocumentMeaning snapshot (Query.projectChunkIDs project) (inj₁ error)
    vectors : ∀ query limit filter ids → V.Selected query limit filter (Store.World.chunkVectors snapshot) ids →
      DocumentMeaning snapshot (Query.queryVectors query limit filter) (inj₂ ids)
    vectorsFailed : ∀ query limit filter error → DocumentMeaning snapshot (Query.queryVectors query limit filter) (inj₁ error)
    chunk : ∀ id → DocumentMeaning snapshot (Query.getChunk id) (inj₂ (Store.chunk id (Store.World.chunks snapshot)))
    chunkFailed : ∀ id error → DocumentMeaning snapshot (Query.getChunk id) (inj₁ error)

  RetrievalMeaning : (state : Retrieval.State) → Store.World → Retrieval.Reply state → Set
  RetrievalMeaning state@(Retrieval.vectorQuery requestValue retired beliefs token vector) snapshot (inj₁ error) = ⊤
  RetrievalMeaning state@(Retrieval.vectorQuery requestValue retired beliefs token vector) snapshot (inj₂ ids)
    with Retrieval.command state
  ... | just (Retrieval.queryVector query limit filter) = V.StableSelected query limit filter (Store.World.beliefVectors snapshot) ids
  ... | _ = Data.Empty.⊥
    where import Data.Empty
  RetrievalMeaning state snapshot reply = RetrievalReads.ReadMeaning state snapshot reply

-- A distinct event is retained for each observed database effect. Ordinary
-- reads do not imply one session-wide snapshot. Page reads explicitly start a
-- read-only REPEATABLE READ transaction: the second SELECT sees the first
-- SELECT's snapshot, under PostgreSQL's external isolation contract.
module Observed (reads : Committed.Contract Store.World) where
  open Committed.Contract reads

  GraphReply : (effect : Graph.Effect) → Graph.Reply effect → Set
  GraphReply (Graph.select handle statement) (inj₁ error) = ⊤
  GraphReply (Graph.select handle statement) (inj₂ observedWorld) = Σ Read (λ read → observedWorld ≡ snapshot read)
  GraphReply (Graph.openExplanation id) (inj₁ error) = ⊤
  GraphReply (Graph.openExplanation id) (inj₂ (tx , original)) = Σ Read (λ read → original ≡ snapshot read)
  GraphReply (Graph.explanationSnapshot tx original statement) (inj₁ error) = ⊤
  GraphReply (Graph.explanationSnapshot tx original statement) (inj₂ observed) = observed ≡ original
  GraphReply (Graph.openPage project memory) (inj₁ error) = ⊤
  GraphReply (Graph.openPage project memory) (inj₂ (tx , first)) = Σ Read (λ read → first ≡ snapshot read)
  GraphReply (Graph.pageSnapshotRows tx first project memory limit offset) (inj₁ error) = ⊤
  GraphReply (Graph.pageSnapshotRows tx first project memory limit offset) (inj₂ second) = second ≡ first
  GraphReply (Graph.dropTransaction tx) reply = ⊤

  pageReplyUsesItsOriginalSnapshot : ∀ tx first second project memory limit offset →
    GraphReply (Graph.pageSnapshotRows tx first project memory limit offset) (inj₂ second) →
    Records.pageResult project memory limit offset
      (Data.List.length (Records.listBeliefs project memory (Store.beliefs first))) (Store.beliefs second) ≡
    Graph.pageAnswer project memory limit offset first
  pageReplyUsesItsOriginalSnapshot tx first second project memory limit offset stable =
    Graph.pageUsesCountSnapshot project memory limit offset first second stable

  EvidenceReply : (effect : Evidence.Effect) → Evidence.Reply effect → Set
  EvidenceReply (Evidence.readGrounds ids) (inj₁ error) = ⊤
  EvidenceReply (Evidence.readChunk id) (inj₁ error) = ⊤
  EvidenceReply (Evidence.openSnapshot belief) (inj₁ error) = ⊤
  EvidenceReply (Evidence.readSnapshotChunk tx first id) (inj₁ error) = ⊤
  EvidenceReply (Evidence.closeSnapshot tx) reply = ⊤
  EvidenceReply effect reply = Σ Read (λ read → EvidenceMeaning (snapshot read) effect reply)

  passageUsesSelectedSnapshot : ∀ tx first id row →
    EvidenceReply (Evidence.readSnapshotChunk tx first id) (inj₂ row) →
    row ≡ Store.chunk id (Store.World.chunks first)
  passageUsesSelectedSnapshot tx first id row (read , stable , selected) =
    trans selected (cong (λ world → Store.chunk id (Store.World.chunks world)) stable)

  SuccessfulInferenceReply : (databaseSum : List Float → Float) → (effect : Inference.Effect) → Inference.Reply effect → Set
  SuccessfulInferenceReply databaseSum effect reply = Σ Read (λ read → Semantics.InferenceRead databaseSum (snapshot read) effect reply)

  interventionUsesTargetSnapshot : ∀ sum tx first effect reply →
    SuccessfulInferenceReply sum (Inference.inSnapshot tx first effect) reply →
    Semantics.InferenceRead sum first effect reply
  interventionUsesTargetSnapshot sum tx first effect reply
    (read , Semantics.readInSnapshot .tx .first .effect .reply stable meaning) =
    subst (λ world → Semantics.InferenceRead sum world effect reply) stable meaning

  contradictionsUseSelectedSnapshot : ∀ sum tx first scope beliefs candidates →
    SuccessfulInferenceReply sum (Inference.snapshotBeliefs tx first scope) (inj₂ beliefs) →
    Numeric.activeContradictions beliefs candidates ≡ Numeric.activeContradictions
      (Records.listBeliefs scope nothing (Store.beliefs first)) candidates
  contradictionsUseSelectedSnapshot sum tx first scope beliefs candidates
    (read , Semantics.readSnapshotBeliefs .tx .first .scope stable) =
    cong (λ world → Numeric.activeContradictions
      (Records.listBeliefs scope nothing (Store.beliefs world)) candidates) stable

module RetrievalSnapshot (ops : VectorOperations) (reads : Committed.Contract Store.World)
  (first : Committed.Contract.Read reads) where
  module D = Committed.Contract reads
  module Meaning = Read ops

  world : Store.World
  world = D.snapshot first

  -- The first actual database read fixes the response view. Vector replies
  -- retain their complete selected-table, filter and ordering obligations.
  record QueryRead (phase : Retrieval.State) (reply : Retrieval.Reply phase) : Set where
    constructor observedQuery
    field
      event : D.Read
      sameView : D.snapshot event ≡ world
      meaning : Meaning.RetrievalMeaning phase (D.snapshot event) reply

  selectedWorldMeaning : ∀ phase reply → QueryRead phase reply → Meaning.RetrievalMeaning phase world reply
  selectedWorldMeaning phase reply evidence =
    subst (λ state → Meaning.RetrievalMeaning phase state reply)
      (QueryRead.sameView evidence) (QueryRead.meaning evidence)

  responseReadsAgree : ∀ firstPhase firstReply secondPhase secondReply →
    (one : QueryRead firstPhase firstReply) → (two : QueryRead secondPhase secondReply) →
    D.snapshot (QueryRead.event one) ≡ D.snapshot (QueryRead.event two)
  responseReadsAgree firstPhase firstReply secondPhase secondReply one two =
    trans (QueryRead.sameView one) (sym (QueryRead.sameView two))

  -- Enrichment is part of the same response, not another independently
  -- chosen snapshot after ranking. Its individual reads retain their meaning.
  record Passage (effect : Evidence.Effect) (reply : Evidence.Reply effect) : Set where
    constructor observedPassage
    field
      event : D.Read
      sameView : D.snapshot event ≡ world
      meaning : EvidenceMeaning (D.snapshot event) effect reply

  retrievalAndPassagesAgree : ∀ phase value effect reply →
    (queryRead : QueryRead phase value) → (passageRead : Passage effect reply) →
    D.snapshot (QueryRead.event queryRead) ≡ D.snapshot (Passage.event passageRead)
  retrievalAndPassagesAgree phase value effect reply queryRead passageRead =
    trans (QueryRead.sameView queryRead) (sym (Passage.sameView passageRead))

-- This view starts at the first database query, after embedding preparation.
-- Selected vector rows, chunk text and parent text use the same stored state.
module DocumentSnapshot (ops : VectorOperations) (reads : Committed.Contract Store.World)
  (first : Committed.Contract.Read reads) where
  module D = Committed.Contract reads
  module Meaning = Read ops

  world : Store.World
  world = D.snapshot first

  record QueryRead (effect : Query.Effect) (reply : Query.Reply effect) : Set where
    constructor observedQuery
    field
      event : D.Read
      sameView : D.snapshot event ≡ world
      meaning : Meaning.DocumentMeaning (D.snapshot event) effect reply

  selectedWorldMeaning : ∀ effect reply → QueryRead effect reply → Meaning.DocumentMeaning world effect reply
  selectedWorldMeaning effect reply evidence =
    subst (λ state → Meaning.DocumentMeaning state effect reply)
      (QueryRead.sameView evidence) (QueryRead.meaning evidence)

  responseReadsAgree : ∀ firstEffect firstReply secondEffect secondReply →
    (one : QueryRead firstEffect firstReply) → (two : QueryRead secondEffect secondReply) →
    D.snapshot (QueryRead.event one) ≡ D.snapshot (QueryRead.event two)
  responseReadsAgree firstEffect firstReply secondEffect secondReply one two =
    trans (QueryRead.sameView one) (sym (QueryRead.sameView two))

-- Procedure and assessment reads retain the full retrieval response view.
module LearningContextSnapshot (ops : VectorOperations) (reads : Committed.Contract Store.World)
  (first : Committed.Contract.Read reads) where
  module D = Committed.Contract reads
  module Beliefs = RetrievalSnapshot ops reads first

  LearningReply : Learning.World → Set
  LearningReply observed = Σ D.Read (λ event →
    D.snapshot event ≡ Beliefs.world × observed ≡ Store.learningView (D.snapshot event))

  ReplyMeaning : (phase : ContextProtocol.State) → ContextProtocol.Reply phase → Set
  ReplyMeaning (ContextProtocol.opening request) reply = ⊤
  ReplyMeaning (ContextProtocol.owned tx phase) reply = ReplyMeaning phase reply
  ReplyMeaning (ContextProtocol.closing tx terminal) reply = ⊤
  ReplyMeaning (ContextProtocol.retrieving request phase) reply = Beliefs.QueryRead phase reply
  ReplyMeaning (ContextProtocol.listPatterns request beliefs) (inj₁ error) = ⊤
  ReplyMeaning (ContextProtocol.listPatterns request beliefs) (inj₂ observed) = LearningReply observed
  ReplyMeaning (ContextProtocol.countPattern request beliefs remaining ranked hits procedure) (inj₁ error) = ⊤
  ReplyMeaning (ContextProtocol.countPattern request beliefs remaining ranked hits procedure) (inj₂ observed) = LearningReply observed
  ReplyMeaning (ContextProtocol.patternOrigin request beliefs remaining ranked hits procedure) (inj₁ error) = ⊤
  ReplyMeaning (ContextProtocol.patternOrigin request beliefs remaining ranked hits procedure) (inj₂ observed) = LearningReply observed
  ReplyMeaning (ContextProtocol.assessmentGroups request beliefs patterns) (inj₁ error) = ⊤
  ReplyMeaning (ContextProtocol.assessmentGroups request beliefs patterns) (inj₂ observed) = LearningReply observed
  ReplyMeaning ContextProtocol.invalidInput reply = ⊤
  ReplyMeaning ContextProtocol.invalidAssessment reply = ⊤
  ReplyMeaning (ContextProtocol.failed error) reply = ⊤
  ReplyMeaning (ContextProtocol.finished result) reply = ⊤

  contextRowsUseRetrievalView : ∀ observed → LearningReply observed →
    observed ≡ Store.learningView Beliefs.world
  contextRowsUseRetrievalView observed (event , stable , selected) =
    trans selected (cong Store.learningView stable)

-- Concrete read requests carry filters and identities only. In particular,
-- neither a desired answer nor a correctness certificate is an input. Wire
-- scalar formatting is the existing standard-library dependency boundary.
module BasicReads (format : Encoding.Formatting) where
  module Encode = Encoding.Encode format

  data Request : Set where
    getBelief : ℕ → Request
    listBeliefs : Maybe Text → Maybe Candidates.Memory → Request
    beliefPage : Maybe Text → Maybe Candidates.Memory → ℕ → ℕ → Request
    listPatterns : Maybe Text → Request
    contradictions : Maybe Text → Request
    evidence : ℕ → Request
    capabilities : Request

  -- The page constructor receives count-minus-one: every admitted page is
  -- positive, without an upper ceiling or a zero-means-all convention.
  supportingPassages : Store.World → List Store.Ground → List Evidence.Reference
  supportingPassages state [] = []
  supportingPassages state (edgeRow ∷ later) with Store.chunk (Store.Ground.chunk edgeRow) (Store.World.chunks state)
  ... | nothing = supportingPassages state later
  ... | just chunk = Evidence.referenceOf (Store.Ground.weight edgeRow) chunk ∷ supportingPassages state later

  answer : Request → Store.World → Wire.Value
  answer (getBelief id) state = Encoding.optional Encode.belief (Ranking.lookup id (Store.beliefs state))
  answer (listBeliefs project memory) state = Wire.array
    (map Encode.belief (Records.listBeliefs project memory (Store.beliefs state)))
  answer (beliefPage project memory count offset) state = Encode.beliefPage
    (Graph.pageAnswer project memory (suc count) offset state)
  answer (listPatterns project) state = Wire.array
    (map Encode.patternValue (Records.listPatterns project (Store.patterns (Store.nodes state))))
  answer (contradictions project) state = Wire.array (map Encode.identityPair
    (Numeric.activeContradictions (Records.listBeliefs project nothing (Store.beliefs state))
      (Semantics.contradictions project state)))
  answer (evidence id) state = Wire.array (map Encode.reference
    (supportingPassages state (Evidence.ranked id nothing (Semantics.groundRows state))))
  answer capabilities state = Capabilities.encode Capabilities.current

  module Checked = Recovery.ReadOnly answer

  operation : Recovery.Recoverable Store.World Request
  operation = Checked.operation

  completeReplyAndUnchangedWorld : ∀ request initial interrupted final reply →
    Checked.Checked.X.Interrupted (Checked.Checked.script request) initial interrupted →
    Checked.Checked.X.Completed (Checked.Checked.script request) interrupted final reply →
    final ≡ initial × reply ≡ answer request initial
  completeReplyAndUnchangedWorld = Checked.completedRetryPreservesStateAndAnswer
