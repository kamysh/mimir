# How Mimir loads and replaces a document

Loading turns a Markdown file into searchable passages. Mimir resolves
the path, reads the file, and prepares an embedding for each passage.
Once all materials are ready, it replaces the index for that path in
one database transaction.

The caller can search the new passages after commit. Similarity helps
rank search results. Loading does not create evidence links or assign
evidence weight based on similarity.

[Rust loading entry point](../../crates/core/src/lib.rs#L975) · [Weighted evidence](GroundingPublication.lagda.md)

```agda
{-# OPTIONS --safe #-}
-- Loading prepares and validates the replacement before its atomic publication.
-- The existing paired-storage law governs failure behavior. Indexing completes
-- after publication; it never attaches sources to beliefs automatically.
module Mimir.DocumentLoading where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Float.Base using (_<ᵇ_)
open import Data.List using (List; []; _∷_; map; length; filterᵇ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Mimir.UUIDGroups using (UUID)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Mimir.Text using (Text)
import Mimir.ApplicationStore as Store
import Mimir.DocumentStore as Documents
import Mimir.DocumentPublication as Publication
import Mimir.Markdown as Markdown
import Mimir.LearningTransaction as Transaction
import Mimir.Validation as Validation
import Mimir.Effects as Effects
import Mimir.LearningRecompute as Recompute
import Mimir.PosteriorComputation as Posterior
import Mimir.LearningStore as Learning
import Mimir.ReviewPreparationPublication as Reviews
import Mimir.RetrievalRanking as Ranking

```

## Define what replacement commits

The canonical path identifies the old index. The replacement requires
one nonempty, finite vector per passage, all of the same width. Its
passages must belong to that same path, and their recorded identities
must be distinct and must avoid collisions with retained passages.

The write publishes the new passages and vectors together and removes
the old ones. If a removed passage had a positive-weight evidence link,
the same transaction recalculates the target belief and its dependents
from the evidence that remains. The new passages gain no evidence
links just because their embeddings match a belief. A zero-weight
citation is removed with its old passage and contributes no change to
belief values.

[Paired index storage](DocumentPublication.agda) · [Rust replacement transaction](../../crates/core/src/store/conformance.rs#L145)

```agda
data Failure : Set where
  nativeFailure : Text → Failure
  shapeFailure wrongDocument recalculationFailure : Failure
  identityFailure : Validation.Fault → Failure

module Operations (database dimension : ℕ) (calculation : Posterior.Calculation) where
  module P = Publication.Publication dimension
  module T = Transaction.Over Store.World (ℕ × P.D.Store) Failure database 671942183

  affectedBeliefs : Text → Store.World → List UUID
  affectedBeliefs path before = map Store.Ground.belief
    (filterᵇ (λ link → Ranking.member (Store.Ground.chunk link) (Store.documentIDs path before) ∧
      (0.0 <ᵇ Store.Ground.weight link)) (Store.World.grounds before))

  publish : (ℕ × P.D.Store) → List UUID → Store.World → T.Decision
  publish receipt [] proposed = T.replace proposed receipt
  publish receipt affected@(_ ∷ _) proposed with Recompute.runGlobal
    (Recompute.scopedCalculation calculation) affected (Store.nodes proposed) (Store.edges proposed)
    (Recompute.activeReviewsScoped nothing (Learning.identities learn)
      (Reviews.World.ledger (Learning.World.publication learn))) (Store.groundingMasses proposed)
    where learn = Store.World.learning proposed
  ... | Recompute.recomputed nodes _ = T.replace (Store.setNodes nodes proposed) receipt
  ... | _ = T.reject recalculationFailure

  replacePlan : Text → List Documents.Chunk → List Store.Vector → Store.World → T.Decision
  replacePlan path chunks vectors before with P.plan path chunks vectors before
  ... | P.invalidEmbeddingShape = T.reject shapeFailure
  ... | P.wrongDocument = T.reject wrongDocument
  ... | P.invalidIdentity failure = T.reject (identityFailure failure)
  ... | P.replace entries after = publish (length chunks , entries) (affectedBeliefs path before) after

  clearPlan : Text → Store.World → T.Decision
  clearPlan path before = publish (length (Store.documentIDs path before) , [])
    (affectedBeliefs path before) (P.clear path before)

  module ClearRecovery (path : Text) = T.RecoveryPlan (clearPlan path)
  module ReplaceRecovery (path : Text) (chunks : List Documents.Chunk) (vectors : List Store.Vector) =
    T.RecoveryPlan (replacePlan path chunks vectors)

```

## Prepare the replacement and report the result

Without an embedding provider, loading stops before reading the file.
File and embedding failures leave the stored index alone. A malformed
embedding batch cannot start publication. If the database rejects a
replacement or recalculation fails, the transaction keeps the old index
and belief values. A successful response counts the new passages and
ends the operation.

For example, an edit from a 30-day to a 60-day retention policy leaves
the previous index usable if the new vector cannot be saved. Retrying
after fixing the cause publishes the new text. If the old text had
explicitly contributed evidence to a belief, the retry also removes
that contribution.

```agda
  data Effect : Set where
    canonicalize readUTF8 : Text → Effect
    embed : List Text → Effect
    transaction : T.Effect → Effect

  Reply : Effect → Set
  Reply (canonicalize path) = Text ⊎ Text
  Reply (readUTF8 path) = Text ⊎ Text
  Reply (embed texts) = Text ⊎ List Store.Vector
  Reply (transaction effect) = T.Reply effect

  module E = Effects.Protocol Effect Reply
  open E

  data Result : Set where
    embeddingsDisabled invalidEmbeddingShape : Result
    failed : Text → Result
    transactionResult : T.Outcome → Result
    loaded cleared : ℕ → Result

  liftTransaction : T.E.Script T.Outcome → Script T.Outcome
  liftTransaction (T.E.done result) = done result
  liftTransaction (T.E.ask effect next) = ask (transaction effect) (λ reply → liftTransaction (next reply))

  replaceOutcome : T.Outcome → Result
  replaceOutcome (T.applied (count , entries)) = loaded count
  replaceOutcome result = transactionResult result

  afterReplace : T.Outcome → Script Result
  afterReplace result = done (replaceOutcome result)

  indexingFinishesAtPublication : ∀ outcome events result →
    E.Runs (afterReplace outcome) events result →
    events ≡ [] × result ≡ replaceOutcome outcome
  indexingFinishesAtPublication outcome .[] .(replaceOutcome outcome)
    (E.returned .(replaceOutcome outcome)) = refl , refl

  afterEmbedding : Text → List Documents.Chunk → Text ⊎ List Store.Vector → Script Result
  afterEmbedding path chunks (inj₁ error) = done (failed error)
  afterEmbedding path chunks (inj₂ vectors) with P.align chunks vectors
  ... | nothing = done invalidEmbeddingShape
  ... | just aligned = liftTransaction Tx.start >>= afterReplace
    where module Tx = T.Plan (replacePlan path chunks vectors)

  chunksFrom : (ℕ → UUID) → Text → Maybe Text → Text → List Documents.Chunk
  chunksFrom supply path project text = Parser.parse text
    where module Parser = Markdown.Parse path project supply

  afterFile : (ℕ → UUID) → Text → Maybe Text → Text ⊎ Text → Script Result
  afterFile supply path project (inj₁ error) = done (failed error)
  afterFile supply path project (inj₂ text) = ask (embed (map Documents.Chunk.content chunks)) (afterEmbedding path chunks)
    where
    chunks = chunksFrom supply path project text

  afterCanonical : (ℕ → UUID) → Maybe Text → Text ⊎ Text → Script Result
  afterCanonical supply project (inj₁ error) = done (failed error)
  afterCanonical supply project (inj₂ path) = ask (readUTF8 path) (afterFile supply path project)

  -- UUID supply is an external input, with no uniqueness axiom. Publication
  -- validates identity collisions. Path conversion/UTF8 decoding are standard
  -- filesystem dependency operations, not an invented path parser.
  load : Bool → (ℕ → UUID) → Text → Maybe Text → Script Result
  load false supply path project = done embeddingsDisabled
  load true supply path project = ask (canonicalize path) (afterCanonical supply project)

```

## Clear a document

Clearing uses the same path rule. If the file has been moved or deleted
and cannot be resolved, Mimir tries the path string supplied by the
caller. A successful clear returns the number of passages removed.
The removal and any necessary recalculation commit together.

```agda
  clearOutcome : T.Outcome → Result
  clearOutcome (T.applied (count , entries)) = cleared count
  clearOutcome result = transactionResult result

  afterClear : T.Outcome → Script Result
  afterClear result = done (clearOutcome result)

  clearPath : Text → Script Result
  clearPath path = liftTransaction Tx.start >>= afterClear
    where module Tx = T.Plan (clearPlan path)

  clear : Text → Script Result
  clear path = ask (canonicalize path) (λ
    { (inj₁ error) → clearPath path ; (inj₂ canonical) → clearPath canonical })
```
