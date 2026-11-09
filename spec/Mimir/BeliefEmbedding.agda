{-# OPTIONS --safe #-}
-- A new belief is prepared without business writes, then published with its
-- vector and indexed support in one transaction. Backfill remains separate.
-- Reembedding skips the initial snapshot of existing vectors and never grounds.
module Mimir.BeliefEmbedding where

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_)
open import Data.Float.Base using (Float; _<ᵇ_)
open import Data.List using (List; []; _∷_; _++_; map; filterᵇ)
import Data.List.Properties as Lists
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _≟_)
open import Data.Integer using (ℤ)
import Data.Maybe.Properties as Maybes
open import Data.Product using (Σ; _×_; _,_)
open import Data.String using (toList)
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
import Mimir.LearningTransaction as Transaction
open import Mimir.SourceReview using (_≟Text_)
open import Relation.Nullary using (does)
import Mimir.EmbeddingLifecycle as Lifecycle
module Correction = Errors.AgentCorrection

Support = Documents.Chunk × Float

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

sameChunk : Documents.Chunk → Documents.Chunk → Bool
sameChunk first second =
  does (Documents.Chunk.identity first ≟ Documents.Chunk.identity second) ∧
  does (Documents.Chunk.document first ≟Text Documents.Chunk.document second) ∧
  does (Lists.≡-dec _≟Text_ (Documents.Chunk.section first) (Documents.Chunk.section second)) ∧
  does (Documents.Chunk.content first ≟Text Documents.Chunk.content second) ∧
  does (Maybes.≡-dec _≟_ (Documents.Chunk.parent first) (Documents.Chunk.parent second)) ∧
  does (Maybes.≡-dec _≟Text_ (Documents.Chunk.project first) (Documents.Chunk.project second))

supportCurrent : G.BeliefValues → Store.World → Support → Bool
supportCurrent belief before (chunk , weight)
  with Store.chunk (Documents.Chunk.identity chunk) (Store.World.chunks before)
... | nothing = false
... | just current = sameChunk chunk current ∧ Numeric.probability weight ∧
  not (weight <ᵇ 0.80) ∧ Grounding.compatible (G.BeliefValues.project belief) (Documents.Chunk.project chunk) ∧
  Ranking.member (Documents.Chunk.identity chunk) (map Data.Product.proj₁ (Store.World.chunkVectors before))

allSupportCurrent : G.BeliefValues → Store.World → List Support → Bool
allSupportCurrent belief before [] = true
allSupportCurrent belief before (first ∷ rest) =
  supportCurrent belief before first ∧ allSupportCurrent belief before rest

-- Read every candidate against one stored view. The first supporting passage
-- and the rest retain complete document fields; preparation writes nothing.
selectSupport : G.BeliefValues → Store.World → List (ℕ × Float) → Text ⊎ List Support
selectSupport belief before [] = inj₂ []
selectSupport belief before ((identity , similarity) ∷ rest) with Scores.finite similarity
... | false = inj₁ (toList "An indexed document produced a nonfinite grounding score; check its stored embedding before retrying.")
... | true with similarity <ᵇ 0.80
...   | true = selectSupport belief before rest
...   | false with Numeric.probability similarity
...     | false = inj₁ (toList "An indexed document produced an invalid grounding probability; no belief was stored.")
...     | true with Store.chunk identity (Store.World.chunks before)
...       | nothing = selectSupport belief before rest
...       | just chunk with Documents.Chunk.content chunk
...         | [] = selectSupport belief before rest
...         | _ ∷ _ with Grounding.compatible (G.BeliefValues.project belief) (Documents.Chunk.project chunk)
...           | false = selectSupport belief before rest
...           | true with selectSupport belief before rest
...             | inj₁ error = inj₁ error
...             | inj₂ following = inj₂ ((chunk , similarity) ∷ following)

ownsPreparation : G.BeliefValues → List Store.EmbeddingOwnerRow → Bool
ownsPreparation belief [] = false
ownsPreparation belief (owner ∷ rest) =
  (does (G.BeliefValues.identity belief ≟ Store.EmbeddingOwnerRow.token owner) ∧
   does (Maybes.≡-dec _≟Text_ (G.BeliefValues.project belief) (Store.EmbeddingOwnerRow.project owner))) ∨
  ownsPreparation belief rest

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
-- a passage selected during preparation. Numerical effects reuse the existing
-- whole-world grounding meaning, inside this same publication transaction.
module Atomic (database : ℕ) (calculator : Posterior.Calculator) (publicationTime : ℤ) where
  module P = Publication.Operation database calculator publicationTime
  module T = Transaction.Over Store.World G.BeliefValues Publication.Failure database 671942183
  paired : G.BeliefValues → Maybe Origin.Provenance → Prepared → Store.World → Store.World
  paired belief origin value before = record inserted
    { beliefVectors = Store.putVector (G.BeliefValues.identity belief) (Prepared.vector value) (Store.World.beliefVectors before)
    ; grounds = Store.World.grounds before ++ map
        (λ where (chunk , weight) → Store.ground (Documents.Chunk.identity chunk) (G.BeliefValues.identity belief) weight)
        (supports value)
    ; embeddingOwners = filterᵇ (λ owner → not (does
        (Store.EmbeddingOwnerRow.token owner ≟ G.BeliefValues.identity belief))) (Store.World.embeddingOwners before) }
    where inserted = Writes.insertBelief belief origin before

  finish : ℕ → P.T.Decision → T.Decision
  finish identity (P.T.reject reason) = T.reject reason
  finish identity (P.T.replay tt) = T.reject Publication.foreignTarget
  finish identity (P.T.replace after tt) with Ranking.lookup identity (Store.beliefs after)
  ... | nothing = T.reject Publication.missingEndpoint
  ... | just belief = T.replace after belief

  intended : G.BeliefValues → Maybe Origin.Provenance → Prepared → Store.World → T.Decision
  intended belief origin value before with Ranking.lookup (G.BeliefValues.identity belief) (Store.beliefs before)
  ... | just _ = T.reject Publication.foreignTarget
  ... | nothing with ownsPreparation belief (Store.World.embeddingOwners before) ∧
    usableVector (Prepared.vector value) ∧ allSupportCurrent belief before (supports value)
  ...   | false = T.reject Publication.missingEndpoint
  ...   | true = finish (G.BeliefValues.identity belief)
    (P.recompute (G.BeliefValues.identity belief) (paired belief origin value before))

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
  prepareEmbedding : G.BeliefValues → Effect
  upsert : ℕ → Store.Vector → Effect
  listBeliefs embeddedIDs : Effect
  progress : G.BeliefValues → Effect
  supportingPassages : G.BeliefValues → Store.Vector → Effect
  publishPrepared : G.BeliefValues → Maybe Origin.Provenance → Prepared → Effect

Reply : Effect → Set
Reply (backfillEmbedding belief) = Text ⊎ List Store.Vector
Reply (prepareEmbedding belief) = Text ⊎ List Store.Vector
Reply (upsert id vector) = Text ⊎ ⊤
Reply listBeliefs = Text ⊎ List G.BeliefValues
Reply embeddedIDs = Text ⊎ List ℕ
Reply (progress b) = Text ⊎ ⊤
Reply (supportingPassages b vector) = Text ⊎ List Support
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

afterSupport : G.BeliefValues → Maybe Origin.Provenance → Store.Vector → Text ⊎ List Support → Script InsertionResult
afterSupport b origin vector (inj₁ error) = done (inj₁ (needsUserDecision
  (preparationDecision Correction.configuration (Validation.key "database" ∷ []) error)))
afterSupport b origin vector (inj₂ []) = done (inj₁ (needsUserDecision
  (preparationDecision Correction.arguments (Validation.key "content" ∷ [])
    (toList "No supporting passage was found in an indexed document; no belief was stored."))))
afterSupport b origin vector (inj₂ (first ∷ rest)) =
  ask (publishPrepared b origin (prepared vector first rest)) afterPublication

afterPreparationEmbedding : G.BeliefValues → Maybe Origin.Provenance → Text ⊎ List Store.Vector → Script InsertionResult
afterPreparationEmbedding b origin (inj₁ error) = done (inj₁ (needsUserDecision
  (preparationDecision Correction.configuration (Validation.key "embeddings" ∷ []) error)))
afterPreparationEmbedding b origin (inj₂ (vector ∷ [])) with usableVector vector
... | true = ask (supportingPassages b vector) (afterSupport b origin vector)
... | false = done (inj₁ (needsUserDecision
  (preparationDecision Correction.configuration (Validation.key "embeddings" ∷ [])
    (toList "The backend returned an empty, nonfinite, or zero vector; no belief was stored."))))
afterPreparationEmbedding b origin (inj₂ _) = done (inj₁ (needsUserDecision
  (preparationDecision Correction.configuration (Validation.key "embeddings" ∷ [])
    (toList "The backend must return exactly one complete vector for this belief; no belief was stored."))))

start : Bool → G.BeliefValues → Maybe Origin.Provenance → Script InsertionResult
start false b origin = done (inj₁ (needsUserDecision missingBackend))
start true b origin = ask (prepareEmbedding b) (afterPreparationEmbedding b origin)

unconfiguredCannotStartPublication : ∀ b origin →
  start false b origin ≡ done (inj₁ (needsUserDecision missingBackend))
unconfiguredCannotStartPublication b origin = refl

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
