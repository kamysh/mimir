{-# OPTIONS --safe #-}
-- Loading prepares and validates the replacement before its atomic publication.
-- The existing paired-storage law governs failure behavior. Automatic grounding
-- follows successful publication; a later grounding failure does not undo it.
module Mimir.DocumentLoading where

open import Data.Bool using (Bool; true; false)
open import Data.Float.Base using (Float)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (toList)
open import Data.Unit using (⊤)
open import Mimir.Text using (Text)
import Mimir.ApplicationStore as Store
import Mimir.DocumentStore as Documents
import Mimir.DocumentPublication as Publication
import Mimir.Markdown as Markdown
import Mimir.GroundingProtocol as Grounding
import Mimir.LearningTransaction as Transaction
import Mimir.Validation as Validation
import Mimir.Effects as Effects

data Failure : Set where
  nativeFailure : Text → Failure
  shapeFailure : Failure
  identityFailure : Validation.Fault → Failure

module Operations (database dimension : ℕ) where
  module P = Publication.Publication dimension
  module T = Transaction.Over Store.World (ℕ × P.D.Store) Failure database 671942183

  replacePlan : Text → List Documents.Chunk → List Store.Vector → Store.World → T.Decision
  replacePlan path chunks vectors before with P.plan path chunks vectors before
  ... | P.invalidEmbeddingShape = T.reject shapeFailure
  ... | P.invalidIdentity failure = T.reject (identityFailure failure)
  ... | P.replace entries after = T.replace after (length chunks , entries)

  clearPlan : Text → Store.World → T.Decision
  clearPlan path before = T.replace (P.clear path before) (length (Store.documentIDs path before) , [])

  data Effect : Set where
    canonicalize readUTF8 : Text → Effect
    embed : List Text → Effect
    transaction : T.Effect → Effect
    grounding : Grounding.Effect → Effect

  Reply : Effect → Set
  Reply (canonicalize path) = Text ⊎ Text
  Reply (readUTF8 path) = Text ⊎ Text
  Reply (embed texts) = Text ⊎ List Store.Vector
  Reply (transaction effect) = T.Reply effect
  Reply (grounding effect) = Grounding.Reply effect

  module E = Effects.Protocol Effect Reply
  open E

  data Result : Set where
    embeddingsDisabled invalidEmbeddingShape : Result
    failed : Text → Result
    transactionResult : T.Outcome → Result
    groundingFailed : ℕ → Grounding.Result → Result
    loaded cleared : ℕ → Result

  liftTransaction : T.E.Script T.Outcome → Script T.Outcome
  liftTransaction (T.E.done result) = done result
  liftTransaction (T.E.ask effect next) = ask (transaction effect) (λ reply → liftTransaction (next reply))

  liftGrounding : Grounding.E.Script Grounding.Result → Script Grounding.Result
  liftGrounding (Grounding.E.done result) = done result
  liftGrounding (Grounding.E.ask effect next) = ask (grounding effect) (λ reply → liftGrounding (next reply))

  afterGrounding : ℕ → Grounding.Result → Script Result
  afterGrounding count Grounding.success = done (loaded count)
  afterGrounding count result = done (groundingFailed count result)

  afterReplace : T.Outcome → Script Result
  afterReplace (T.applied (count , entries)) = liftGrounding (Grounding.groundChunks
    (map (λ entry → P.D.Stored.chunk entry , toList (P.D.Stored.embedding entry)) entries)) >>= afterGrounding count
  afterReplace result = done (transactionResult result)

  afterEmbedding : Text → List Documents.Chunk → Text ⊎ List Store.Vector → Script Result
  afterEmbedding path chunks (inj₁ error) = done (failed error)
  afterEmbedding path chunks (inj₂ vectors) with P.align chunks vectors
  ... | nothing = done invalidEmbeddingShape
  ... | just aligned = liftTransaction Tx.start >>= afterReplace
    where module Tx = T.Plan (replacePlan path chunks vectors)

  afterFile : (ℕ → ℕ) → Text → Maybe Text → Text ⊎ Text → Script Result
  afterFile supply path project (inj₁ error) = done (failed error)
  afterFile supply path project (inj₂ text) = ask (embed (map Documents.Chunk.content chunks)) (afterEmbedding path chunks)
    where
    module Parser = Markdown.Parse path project supply
    chunks = Parser.parse text

  afterCanonical : (ℕ → ℕ) → Maybe Text → Text ⊎ Text → Script Result
  afterCanonical supply project (inj₁ error) = done (failed error)
  afterCanonical supply project (inj₂ path) = ask (readUTF8 path) (afterFile supply path project)

  -- UUID supply is an external input, with no uniqueness axiom. Publication
  -- validates identity collisions. Path conversion/UTF8 decoding are standard
  -- filesystem dependency operations, not an invented path parser.
  load : Bool → (ℕ → ℕ) → Text → Maybe Text → Script Result
  load false supply path project = done embeddingsDisabled
  load true supply path project = ask (canonicalize path) (afterCanonical supply project)

  afterClear : T.Outcome → Script Result
  afterClear (T.applied (count , entries)) = done (cleared count)
  afterClear result = done (transactionResult result)

  clearPath : Text → Script Result
  clearPath path = liftTransaction Tx.start >>= afterClear
    where module Tx = T.Plan (clearPlan path)

  clear : Text → Script Result
  clear path = ask (canonicalize path) (λ
    { (inj₁ error) → clearPath path ; (inj₂ canonical) → clearPath canonical })
