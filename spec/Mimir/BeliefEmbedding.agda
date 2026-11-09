{-# OPTIONS --safe #-}
-- A new belief is prepared without business writes, then published with its
-- vector and indexed support in one transaction. Backfill remains separate.
-- Reembedding skips the initial snapshot of existing vectors and never grounds.
module Mimir.BeliefEmbedding where

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_)
open import Data.Float.Base using (Float; _<ᵇ_)
open import Data.List using (List; []; _∷_; _++_; map; filterᵇ)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Properties as Lists
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _≟_)
open import Data.Integer using (ℤ)
import Data.Maybe.Properties as Maybes
open import Data.Product using (Σ; _×_; _,_)
open import Data.String using (String; toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.CandidateGraph as G
import Mimir.ApplicationStore as Store
import Mimir.IndependentProvenance as Origin
import Mimir.GroundingProtocol as Grounding
import Mimir.RetrievalRanking as Ranking
import Mimir.RetrievalProtocol as Retrieval
import Mimir.Effects as Effects
import Mimir.DocumentStore as Documents
import Mimir.McpErrors as Errors
import Mimir.Validation as Validation
import Mimir.AssessmentScores as Scores
import Mimir.GraphNumerics as Numeric
import Mimir.GraphWrites as Writes
import Mimir.GroundingPublication as Publication
import Mimir.PosteriorComputation as Posterior
import Mimir.EvidenceValidity as Evidence
import Mimir.LearningTransaction as Transaction
open import Mimir.SourceReview using (_≟Text_)
open import Relation.Nullary using (does)
import Mimir.EmbeddingLifecycle as Lifecycle
import Mimir.SourceText as Quotation
import Data.Char as Chars
import Mimir.Text as Text
import Data.Bool.Properties as BoolProperties
module Correction = Errors.AgentCorrection

-- A citation is a submitting agent's inspectable account of support. Literal
-- reference/quotation integrity is checked; its explanation is not a proof of
-- semantic truth and similarity never occurs in this validity predicate.
Citation = Documents.Citation
module Citation = Documents.Citation

module Quote = Quotation.Matching Chars.Char Chars._≟_

checkCitationText : (fieldName : String) (value : Text) → Validation.Checked (Text.Nonblank value)
checkCitationText fieldName value = Validation.at (Validation.key fieldName) (Validation.check
  (Validation.fault [] Validation.emptyText "The citation field must contain nonblank text; if support is unclear, open the user dialog before publication.")
  (Text.nonblank? value))

CitationValid : G.BeliefValues → Store.World → Citation → Set
CitationValid belief before cited with Store.chunk (Citation.chunk cited) (Store.World.chunks before)
... | nothing = Data.Empty.⊥
  where import Data.Empty
... | just chunk = Text.Nonblank (Citation.document cited) ×
  Citation.document cited ≡ Documents.Chunk.document chunk ×
  Text.Nonblank (Citation.quotation cited) × Quote.Contains (Citation.quotation cited) (Documents.Chunk.content chunk) ×
  Text.Nonblank (Citation.explanation cited) ×
  Grounding.compatible (G.BeliefValues.project belief) (Documents.Chunk.project chunk) ≡ true ×
  Ranking.member (Citation.chunk cited) (map Data.Product.proj₁ (Store.World.chunkVectors before)) ≡ true

validateCitation : ∀ belief before cited → Validation.Checked (CitationValid belief before cited)
validateCitation belief before cited with Store.chunk (Citation.chunk cited) (Store.World.chunks before)
... | nothing = Validation.rejected
  (Validation.fault (Validation.key "chunk_id" ∷ []) Validation.missingReference
    "The cited chunk is not stored. Query the indexed document and copy its current chunk ID; do not invent an ID.") (λ impossible → impossible)
... | just chunk = Validation.combine
  (checkCitationText "document_path" (Citation.document cited))
  (Validation.combine
    (Validation.at (Validation.key "document_path") (Validation.check
      (Validation.fault [] Validation.wrongIdentity "The cited document path must match the indexed chunk's actual document.")
      (Citation.document cited ≟Text Documents.Chunk.document chunk)))
    (Validation.combine
      (checkCitationText "quotation" (Citation.quotation cited))
      (Validation.combine
        (Validation.at (Validation.key "quotation") (Validation.check
          (Validation.fault [] Validation.quotationMismatch "Copy an exact contiguous passage from the indexed chunk; put interpretation in explanation.")
          (Quote.contains? (Citation.quotation cited) (Documents.Chunk.content chunk))))
        (Validation.combine
          (checkCitationText "explanation" (Citation.explanation cited))
          (Validation.combine
            (Validation.check
              (Validation.fault (Validation.key "chunk_id" ∷ []) Validation.missingReference "The indexed document must be compatible with this belief's project.")
              (Grounding.compatible (G.BeliefValues.project belief) (Documents.Chunk.project chunk) BoolProperties.≟ true))
            (Validation.check
              (Validation.fault (Validation.key "chunk_id" ∷ []) Validation.missingReference "The cited chunk must have an indexed document vector before belief publication.")
              (Ranking.member (Citation.chunk cited) (map Data.Product.proj₁ (Store.World.chunkVectors before)) BoolProperties.≟ true)))))))

validCitationAccepted : ∀ belief before cited → CitationValid belief before cited →
  Validation.reported (validateCitation belief before cited) ≡ []
validCitationAccepted belief before cited valid = Validation.noFalseRejection (validateCitation belief before cited) valid

-- All submitted passages must be valid. Missing or faulty support is an
-- explained decision before publication, never a similarity-based substitute.
CitationsValid : G.BeliefValues → Store.World → List Citation → Set
CitationsValid belief before [] = Data.Empty.⊥
  where import Data.Empty
CitationsValid belief before (first ∷ rest) =
  CitationValid belief before first × All (CitationValid belief before) rest

validateCitations : ∀ belief before cited → Validation.Checked (CitationsValid belief before cited)
validateCitations belief before [] = Validation.rejected
  (Validation.fault (Validation.key "grounding" ∷ []) Validation.missingEvidence
    "Supply an indexed-document passage and explain its support. If none is available, open the user dialog before publication.") (λ impossible → impossible)
validateCitations belief before (first ∷ rest) = Validation.at (Validation.key "grounding")
  (Validation.combine (Validation.at (Validation.index 0) (validateCitation belief before first))
    (Validation.allCheckedFrom 1 (validateCitation belief before) rest))

validCitationsAccepted : ∀ belief before cited → CitationsValid belief before cited →
  Validation.reported (validateCitations belief before cited) ≡ []
validCitationsAccepted belief before cited valid = Validation.noFalseRejection (validateCitations belief before cited) valid

Support = Documents.Chunk × Citation

record Prepared : Set where
  constructor prepared
  field
    vector : Store.Vector
    firstSupport : Support
    remainingSupport : List Support

supports : Prepared → List Support
supports value = Prepared.firstSupport value ∷ Prepared.remainingSupport value

finiteVector nonzeroVector : Store.Vector → Bool
finiteVector [] = true
finiteVector (value ∷ rest) = Scores.finite value ∧ finiteVector rest
nonzeroVector [] = false
nonzeroVector (value ∷ rest) = (value <ᵇ 0.0) ∨ (0.0 <ᵇ value) ∨ nonzeroVector rest

usableVector : Store.Vector → Bool
usableVector vector = finiteVector vector ∧ nonzeroVector vector

readback : G.BeliefValues → G.BeliefValues
readback belief = Evidence.updated belief (Posterior.beta (G.BeliefValues.alpha belief) (G.BeliefValues.beta belief))

sameChunk : Documents.Chunk → Documents.Chunk → Bool
sameChunk first second =
  does (Documents.Chunk.identity first ≟ Documents.Chunk.identity second) ∧
  does (Documents.Chunk.document first ≟Text Documents.Chunk.document second) ∧
  does (Lists.≡-dec _≟Text_ (Documents.Chunk.section first) (Documents.Chunk.section second)) ∧
  does (Documents.Chunk.content first ≟Text Documents.Chunk.content second) ∧
  does (Maybes.≡-dec _≟_ (Documents.Chunk.parent first) (Documents.Chunk.parent second)) ∧
  does (Maybes.≡-dec _≟Text_ (Documents.Chunk.project first) (Documents.Chunk.project second))

citationCurrent : G.BeliefValues → Store.World → Citation → Bool
citationCurrent belief before cited with validateCitation belief before cited
... | Validation.accepted _ = true
... | Validation.rejected _ _ = false

supportCurrent : G.BeliefValues → Store.World → Support → Bool
supportCurrent belief before (chunk , cited)
  with Store.chunk (Documents.Chunk.identity chunk) (Store.World.chunks before)
... | nothing = false
... | just current = sameChunk chunk current ∧
  does (Documents.Chunk.identity chunk ≟ Citation.chunk cited) ∧ citationCurrent belief before cited

allSupportCurrent : G.BeliefValues → Store.World → List Support → Bool
allSupportCurrent belief before [] = true
allSupportCurrent belief before (first ∷ rest) =
  supportCurrent belief before first ∧ allSupportCurrent belief before rest

hasSupport : List Support → Bool
hasSupport [] = false
hasSupport (_ ∷ _) = true

selectSupport : G.BeliefValues → Store.World → List Citation → Text ⊎ List Support
selectSupport belief before [] = inj₂ []
selectSupport belief before (cited ∷ rest) with validateCitation belief before cited
... | Validation.rejected fault _ = inj₁ (Validation.Fault.explanation fault)
... | Validation.accepted valid with Store.chunk (Citation.chunk cited) (Store.World.chunks before)
... | nothing = inj₁ (toList "The cited indexed chunk is missing; no belief was stored.")
... | just chunk with selectSupport belief before rest
... | inj₁ reason = inj₁ reason
... | inj₂ following = inj₂ ((chunk , cited) ∷ following)

ownsPreparation : G.BeliefValues → List Store.EmbeddingOwnerRow → Bool
ownsPreparation belief [] = false
ownsPreparation belief (owner ∷ rest) =
  (does (G.BeliefValues.identity belief ≟ Store.EmbeddingOwnerRow.token owner) ∧
   does (Maybes.≡-dec _≟Text_ (G.BeliefValues.project belief) (Store.EmbeddingOwnerRow.project owner))) ∨
  ownsPreparation belief rest

preparationCurrent : G.BeliefValues → List Support → Store.World → Bool
preparationCurrent belief support before = ownsPreparation belief (Store.World.embeddingOwners before) ∧
  hasSupport support ∧ allSupportCurrent belief before support

module OwnerSubscription where
  data Effect : Set where
    connect : ℕ → Effect
    listen : ℕ → Text → Effect
  Reply : Effect → Set
  Reply (connect database) = Text ⊎ ℕ
  Reply (listen handle channel) = Text ⊎ ⊤
  module E = Effects.Protocol Effect Reply
  start : ℕ → E.Script (Text ⊎ ℕ)
  start database = E.ask (connect database) λ where
    (inj₁ error) → E.done (inj₁ error)
    (inj₂ handle) → E.ask (listen handle (toList "mimir_embedding_owners_changed")) λ where
      (inj₁ error) → E.done (inj₁ error)
      (inj₂ tt) → E.done (inj₂ handle)

-- Database hints are not stop instructions for every request. Recheck this
-- exact preparation; only a missing owner revokes its per-call worker.
checkedOwnership : G.BeliefValues → Store.World → Lifecycle.Ownership.State → Lifecycle.Ownership.State
checkedOwnership belief before state with ownsPreparation belief (Store.World.embeddingOwners before)
... | true = state
... | false = Lifecycle.Ownership.stop state

missingOwnerStopsItsJob : ∀ belief before state →
  ownsPreparation belief (Store.World.embeddingOwners before) ≡ false →
  checkedOwnership belief before state ≡ Lifecycle.Ownership.stop state
missingOwnerStopsItsJob belief before state missing
  rewrite missing = refl

retainedOwnerKeepsItsJob : ∀ belief before state →
  ownsPreparation belief (Store.World.embeddingOwners before) ≡ true →
  checkedOwnership belief before state ≡ state
retainedOwnerKeepsItsJob belief before state present rewrite present = refl

checkedPreparation : G.BeliefValues → List Support → Store.World → Lifecycle.Ownership.State → Lifecycle.Ownership.State
checkedPreparation belief support before state with preparationCurrent belief support before
... | true = state
... | false = Lifecycle.Ownership.stop state

changedSourceStopsItsJob : ∀ belief support before state → preparationCurrent belief support before ≡ false →
  checkedPreparation belief support before state ≡ Lifecycle.Ownership.stop state
changedSourceStopsItsJob belief support before state changed rewrite changed = refl

unchangedSourcesKeepTheirJob : ∀ belief support before state → preparationCurrent belief support before ≡ true →
  checkedPreparation belief support before state ≡ state
unchangedSourcesKeepTheirJob belief support before state current rewrite current = refl

-- Backfill belongs to an existing belief, rather than a reservation for a new
-- one. A database hint must recheck this exact target before cancelling.
ownsBackfill : G.BeliefValues → Store.World → Bool
ownsBackfill belief before = Ranking.member (G.BeliefValues.identity belief)
  (map G.BeliefValues.identity (Store.beliefs before))

checkedBackfillOwnership : G.BeliefValues → Store.World → Lifecycle.Ownership.State → Lifecycle.Ownership.State
checkedBackfillOwnership belief before state with ownsBackfill belief before
... | true = state
... | false = Lifecycle.Ownership.stop state

missingBackfillStopsItsJob : ∀ belief before state → ownsBackfill belief before ≡ false →
  checkedBackfillOwnership belief before state ≡ Lifecycle.Ownership.stop state
missingBackfillStopsItsJob belief before state missing rewrite missing = refl

retainedBackfillKeepsItsJob : ∀ belief before state → ownsBackfill belief before ≡ true →
  checkedBackfillOwnership belief before state ≡ state
retainedBackfillKeepsItsJob belief before state present rewrite present = refl

-- User-visible intent: one complete new belief, its provenance, its vector,
-- and every prepared supporting passage. Rechecking cannot silently discard
-- a passage supplied during preparation. Citations are source references;
-- they change neither numerical evidence nor the submitted belief values.
module Atomic (database : ℕ) (calculator : Posterior.Calculator) (publicationTime : ℤ) where
  module P = Publication.Operation database calculator publicationTime
  module T = Transaction.Over Store.World G.BeliefValues Publication.Failure database 671942183
  paired : G.BeliefValues → Maybe Origin.Provenance → Prepared → Store.World → Store.World
  paired belief origin value before = record inserted
    { beliefVectors = Store.putVector (G.BeliefValues.identity belief) (Prepared.vector value) (Store.World.beliefVectors before)
    ; beliefSources = (G.BeliefValues.identity belief , map Data.Product.proj₂ (supports value)) ∷ Store.World.beliefSources before
    ; embeddingOwners = filterᵇ (λ owner → not (does
        (Store.EmbeddingOwnerRow.token owner ≟ G.BeliefValues.identity belief))) (Store.World.embeddingOwners before) }
    where inserted = Writes.insertBelief belief origin before

  intended : G.BeliefValues → Maybe Origin.Provenance → Prepared → Store.World → T.Decision
  intended belief origin value before with Ranking.lookup (G.BeliefValues.identity belief) (Store.beliefs before)
  ... | just _ = T.reject Publication.foreignTarget
  ... | nothing with ownsPreparation belief (Store.World.embeddingOwners before) ∧
    usableVector (Prepared.vector value) ∧ allSupportCurrent belief before (supports value)
  ...   | false = T.reject Publication.missingEndpoint
  ...   | true = T.replace (paired belief origin value before) (readback belief)

  module Run (belief : G.BeliefValues) (origin : Maybe Origin.Provenance) (value : Prepared) where
    module Execution = T.Plan (intended belief origin value)
    module Laws = T.Laws (intended belief origin value)

preparationDecision : Correction.Location → List Validation.Segment → Text → Correction.Claim
preparationDecision location path reason = Correction.claim
  (Correction.item location (Validation.problem path Validation.missingEvidence reason)
    (toList "A complete embedding and a supporting passage from an indexed, project-compatible document before this belief is stored.")
    (toList "Open a dialog with the user explaining the missing prerequisite. Ask whether to repair the configured backend, index a supporting document, revise the belief, or cancel. Do not guess, silently shorten the content, change the model, or store an ungrounded belief.")) []

missingBackend : Correction.Claim
missingBackend = preparationDecision Correction.configuration (Validation.key "embeddings" ∷ [])
  (toList "Embedding is not configured; no belief was stored.")

data Effect : Set where
  backfillEmbedding : G.BeliefValues → Effect
  prepareEmbedding : G.BeliefValues → List Support → Effect
  upsert : ℕ → Store.Vector → Effect
  listBeliefs embeddedIDs : Effect
  progress : G.BeliefValues → Effect
  supportingPassages : G.BeliefValues → List Citation → Effect
  publishPrepared : G.BeliefValues → Maybe Origin.Provenance → Prepared → Effect

Reply : Effect → Set
Reply (backfillEmbedding belief) = Text ⊎ List Store.Vector
Reply (prepareEmbedding belief support) = Text ⊎ List Store.Vector
Reply (upsert id vector) = Text ⊎ ⊤
Reply listBeliefs = Text ⊎ List G.BeliefValues
Reply embeddedIDs = Text ⊎ List ℕ
Reply (progress b) = Text ⊎ ⊤
Reply (supportingPassages b cited) = Text ⊎ List Support
Reply (publishPrepared b origin value) = Text ⊎ (Correction.Claim ⊎ G.BeliefValues)

module E = Effects.Protocol Effect Reply
open E

data Failure : Set where
  nativeFailure : Text → Failure
  needsUserDecision : Correction.Claim → Failure

Result = Failure ⊎ ⊤
InsertionResult = Failure ⊎ G.BeliefValues

backfillDecision : Validation.Code → Text → Correction.Claim
backfillDecision code reason = Correction.claim
  (Correction.item Correction.configuration (Validation.problem (Validation.key "embeddings" ∷ []) code reason)
    (toList "Exactly one complete, finite, nonzero embedding for this stored belief before reporting it embedded.")
    (toList "Open a dialog with the user to repair the configured embedding backend or cancel. Do not silently shorten the content, change the model, or count this belief as embedded.")) []

missingBackfillBackend invalidBackfillShape invalidBackfillVector : Correction.Claim
missingBackfillBackend = backfillDecision Validation.missingEvidence
  (toList "Embedding is not configured; this belief's vector was not written.")
invalidBackfillShape = backfillDecision Validation.malformedInput
  (toList "The backend must return exactly one vector for this belief; its vector was not written.")
invalidBackfillVector = backfillDecision Validation.invalidNumber
  (toList "The backend returned an empty, nonfinite, or zero vector; this belief's vector was not written.")

afterUpsert : Text ⊎ ⊤ → Script Result
afterUpsert (inj₁ error) = done (inj₁ (nativeFailure error))
afterUpsert (inj₂ tt) = done (inj₂ tt)

afterEmbed : G.BeliefValues → Text ⊎ List Store.Vector → Script Result
afterEmbed b (inj₁ error) = done (inj₁ (nativeFailure error))
afterEmbed b (inj₂ (vector ∷ [])) with usableVector vector
... | false = done (inj₁ (needsUserDecision invalidBackfillVector))
... | true = ask (upsert (G.BeliefValues.identity b) vector) afterUpsert
afterEmbed b (inj₂ _) = done (inj₁ (needsUserDecision invalidBackfillShape))

embedBelief : Bool → G.BeliefValues → Script Result
embedBelief false b = done (inj₁ (needsUserDecision missingBackfillBackend))
embedBelief true b = ask (backfillEmbedding b) (afterEmbed b)

afterPublication : Text ⊎ (Correction.Claim ⊎ G.BeliefValues) → Script InsertionResult
afterPublication (inj₁ error) = done (inj₁ (nativeFailure error))
afterPublication (inj₂ (inj₁ report)) = done (inj₁ (needsUserDecision report))
afterPublication (inj₂ (inj₂ belief)) = done (inj₂ belief)

afterPreparationEmbedding : G.BeliefValues → Maybe Origin.Provenance → List Support → Text ⊎ List Store.Vector → Script InsertionResult
afterPreparationEmbedding b origin support (inj₁ error) = done (inj₁ (needsUserDecision
  (preparationDecision Correction.configuration (Validation.key "embeddings" ∷ []) error)))
afterPreparationEmbedding b origin (first ∷ rest) (inj₂ (vector ∷ [])) with usableVector vector
... | true = ask (publishPrepared b origin (prepared vector first rest)) afterPublication
... | false = done (inj₁ (needsUserDecision
  (preparationDecision Correction.configuration (Validation.key "embeddings" ∷ [])
    (toList "The backend returned an empty, nonfinite, or zero vector; no belief was stored."))))
afterPreparationEmbedding b origin _ (inj₂ _) = done (inj₁ (needsUserDecision
  (preparationDecision Correction.configuration (Validation.key "embeddings" ∷ [])
    (toList "The backend must return exactly one complete vector for this belief; no belief was stored."))))

afterSupport : Bool → G.BeliefValues → Maybe Origin.Provenance → Text ⊎ List Support → Script InsertionResult
afterSupport enabled b origin (inj₁ error) = done (inj₁ (needsUserDecision
  (preparationDecision Correction.arguments (Validation.key "grounding" ∷ []) error)))
afterSupport enabled b origin (inj₂ []) = done (inj₁ (needsUserDecision
  (preparationDecision Correction.arguments (Validation.key "grounding" ∷ [])
    (toList "Supply an indexed-document supporting passage and your explanation; no belief was stored."))))
afterSupport false b origin (inj₂ (_ ∷ _)) = done (inj₁ (needsUserDecision missingBackend))
afterSupport true b origin (inj₂ support@(_ ∷ _)) = ask (prepareEmbedding b support) (afterPreparationEmbedding b origin support)

start : Bool → G.BeliefValues → Maybe Origin.Provenance → List Citation → Script InsertionResult
start enabled b origin cited = ask (supportingPassages b cited) (afterSupport enabled b origin)

record Counts : Set where
  constructor counts
  field embedded skipped : ℕ

data Backfill : Set where
  disabled : Backfill
  complete : Counts → Backfill
  interrupted : Counts → Failure → Backfill

mutual
  backfill : List ℕ → List G.BeliefValues → Counts → Script Backfill
  backfill ids [] count = done (complete count)
  backfill ids (b ∷ rest) count with Ranking.member (G.BeliefValues.identity b) ids
  ... | true = backfill ids rest (record count { skipped = suc (Counts.skipped count) })
  ... | false = embedBelief true b >>= afterBackfill ids b rest count

  afterBackfill : List ℕ → G.BeliefValues → List G.BeliefValues → Counts → Result → Script Backfill
  afterBackfill ids b rest count (inj₁ error) = done (interrupted count error)
  afterBackfill ids b rest count (inj₂ tt) = ask (progress b) (λ
    { (inj₁ error) → done (interrupted next (nativeFailure error))
    ; (inj₂ tt) → backfill ids rest next })
    where next = record count { embedded = suc (Counts.embedded count) }

afterList : Text ⊎ List G.BeliefValues → Script Backfill
afterList (inj₁ error) = done (interrupted (counts 0 0) (nativeFailure error))
afterList (inj₂ []) = done (complete (counts 0 0))
afterList (inj₂ beliefs@(_ ∷ _)) = ask embeddedIDs (λ
  { (inj₁ error) → done (interrupted (counts 0 0) (nativeFailure error))
  ; (inj₂ ids) → backfill ids beliefs (counts 0 0) })

reembed : Bool → Script Backfill
reembed false = done disabled
reembed true = ask listBeliefs afterList

disabledEmbeddingHasNoEffects : ∀ b → embedBelief false b ≡ done (inj₁ (needsUserDecision missingBackfillBackend))
disabledEmbeddingHasNoEffects b = refl

-- An empty response cannot flow to the successful branch that increments the
-- embedded count. Disabled embedding is likewise a request for user input.
emptyEmbeddingRequestsCorrection : ∀ b → afterEmbed b (inj₂ []) ≡
  done (inj₁ (needsUserDecision invalidBackfillShape))
emptyEmbeddingRequestsCorrection b = refl

afterEmbedSuccess : ∀ belief raw events → E.Runs (afterEmbed belief raw) events (inj₂ tt) →
  Σ Store.Vector (λ vector → raw ≡ inj₂ (vector ∷ []) × usableVector vector ≡ true ×
    events ≡ ((upsert (G.BeliefValues.identity belief) vector , inj₂ tt) ∷ []))
afterEmbedSuccess belief (inj₁ error) events ()
afterEmbedSuccess belief (inj₂ []) events ()
afterEmbedSuccess belief (inj₂ (vector ∷ [])) events execution with usableVector vector in valid
... | false with execution
... | ()
afterEmbedSuccess belief (inj₂ (vector ∷ [])) ._ (E.replied _ _ (inj₁ error) ()) | true
afterEmbedSuccess belief (inj₂ (vector ∷ [])) ._ (E.replied _ _ (inj₂ tt) (E.returned _)) | true =
  vector , refl , valid , refl
afterEmbedSuccess belief (inj₂ (first ∷ second ∷ rest)) events ()

successfulBackfillHasAcknowledgedVector : ∀ enabled belief events →
  E.Runs (embedBelief enabled belief) events (inj₂ tt) →
  Σ Store.Vector (λ vector → usableVector vector ≡ true × events ≡
    ((backfillEmbedding belief , inj₂ (vector ∷ [])) ∷
      (upsert (G.BeliefValues.identity belief) vector , inj₂ tt) ∷ []))
successfulBackfillHasAcknowledgedVector false belief events ()
successfulBackfillHasAcknowledgedVector true belief ._ (E.replied _ _ reply execution)
  with afterEmbedSuccess belief reply _ execution
... | vector , refl , valid , refl = vector , valid , refl
