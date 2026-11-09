{-# OPTIONS --safe #-}
-- Semantic document query. Project filtering here is exact (no automatic
-- global-document inclusion). After embedding, project selection, vectors and
-- chunk/parent reads share one owned read-only stable transaction.
module Mimir.DocumentQuery where

open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Unit using (⊤)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Mimir.Text using (Text)
import Mimir.ApplicationStore as Store
import Mimir.DocumentStore as Documents
import Mimir.Effects as Effects
import Mimir.RetrievalRanking as Ranking
import Mimir.AssessmentScores as Scores
open import Data.Float.Base using (_<ᵇ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.String using (toList)
import Mimir.Validation as Validation

data PreparationIssue : Set where
  notConfigured noVector unusableVector : PreparationIssue
  backendFailure : Text → PreparationIssue
  extraVectors : PreparationIssue

preparationCode : PreparationIssue → Validation.Code
preparationCode notConfigured = Validation.missingField
preparationCode _ = Validation.unsupportedCombination

preparationDescription : PreparationIssue → Text
preparationDescription notConfigured = toList "Document queries require a configured embedding backend."
preparationDescription (backendFailure error) = toList "The embedding backend could not prepare this document query: " Data.List.++ error
preparationDescription noVector = toList "The embedding backend returned no vector for this document query."
preparationDescription extraVectors = toList "The embedding backend returned more than one vector for a single document query."
preparationDescription unusableVector = toList "The embedding backend returned an empty, nonfinite or all-zero query vector."

usableVector : Store.Vector → Bool
usableVector values = finite values ∧ nonzero values
  where
  finite : Store.Vector → Bool
  finite [] = true
  finite (v ∷ vs) = Scores.finite v ∧ finite vs
  nonzero : Store.Vector → Bool
  nonzero [] = false
  nonzero (v ∷ vs) = (0.0 <ᵇ v) ∨ (v <ᵇ 0.0) ∨ nonzero vs

prepare : Text ⊎ List Store.Vector → PreparationIssue ⊎ Store.Vector
prepare (inj₁ error) = inj₁ (backendFailure error)
prepare (inj₂ []) = inj₁ noVector
prepare (inj₂ (vector ∷ [])) with usableVector vector
... | true = inj₂ vector
... | false = inj₁ unusableVector
prepare (inj₂ (_ ∷ _ ∷ _)) = inj₁ extraVectors

record Hit : Set where
  constructor hit
  field identity : ℕ; document : Text; section : List Text; content : Text; parentContent : Maybe Text

project : Documents.Chunk → Maybe Documents.Chunk → Hit
project c nothing = hit (Documents.Chunk.identity c) (Documents.Chunk.document c)
  (Documents.Chunk.section c) (Documents.Chunk.content c) nothing
project c (just parent) = hit (Documents.Chunk.identity c) (Documents.Chunk.document c)
  (Documents.Chunk.section c) (Documents.Chunk.content c) (just (Documents.Chunk.content parent))

data Effect : Set where
  embed : Text → Effect
  beginRead : Effect
  closeRead : ℕ → Effect
  projectChunkIDs : Text → Effect
  queryVectors : Store.Vector → Ranking.Selection → Maybe (List ℕ) → Effect
  getChunk : ℕ → Effect

Reply : Effect → Set
Reply (embed query) = Text ⊎ List Store.Vector
Reply beginRead = Text ⊎ ℕ
Reply (closeRead tx) = ⊤
Reply (projectChunkIDs project) = Text ⊎ List ℕ
Reply (queryVectors vector limit filter) = Text ⊎ List ℕ
Reply (getChunk id) = Text ⊎ Maybe Documents.Chunk

module E = Effects.Protocol Effect Reply
open E

data Result : Set where
  preparationRequired : PreparationIssue → Result
  failed : Text → Result
  found : List Hit → Result

prepend : Hit → Result → Result
prepend h (found later) = found (h ∷ later)
prepend h result = result

mutual
  materialize : List ℕ → Script Result
  materialize [] = done (found [])
  materialize (id ∷ rest) = ask (getChunk id) (afterChunk rest)

  afterChunk : List ℕ → Text ⊎ Maybe Documents.Chunk → Script Result
  afterChunk rest (inj₁ error) = done (failed error)
  afterChunk rest (inj₂ nothing) = materialize rest
  afterChunk rest (inj₂ (just chunk)) with Documents.Chunk.parent chunk
  ... | nothing = materialize rest >>= λ result → done (prepend (project chunk nothing) result)
  ... | just parent = ask (getChunk parent) (afterParent rest chunk)

  afterParent : List ℕ → Documents.Chunk → Text ⊎ Maybe Documents.Chunk → Script Result
  afterParent rest chunk (inj₁ error) = done (failed error)
  afterParent rest chunk (inj₂ parent) = materialize rest >>= λ result → done (prepend (project chunk parent) result)

afterSearch : Text ⊎ List ℕ → Script Result
afterSearch (inj₁ error) = done (failed error)
afterSearch (inj₂ ids) = materialize ids

search : Store.Vector → Ranking.Selection → Maybe Text → Script Result
search vector limit nothing = ask (queryVectors vector limit nothing) afterSearch
search vector limit (just project) = ask (projectChunkIDs project) (λ
  { (inj₁ error) → done (failed error)
  ; (inj₂ ids) → ask (queryVectors vector limit (just ids)) afterSearch })

afterEmbedding : Ranking.Selection → Maybe Text → Text ⊎ List Store.Vector → Script Result
afterEmbedding limit project response with prepare response
... | inj₁ issue = done (preparationRequired issue)
... | inj₂ vector = ask beginRead (λ
  { (inj₁ error) → done (failed error)
  ; (inj₂ tx) → search vector limit project >>= λ result →
      ask (closeRead tx) (λ _ → done result) })

start : Bool → Text → Ranking.Selection → Maybe Text → Script Result
start false query limit project = done (preparationRequired notConfigured)
start true query limit project = ask (embed query) (afterEmbedding limit project)

refusedPreparationStartsNoRead : ∀ limit project response issue →
  prepare response ≡ inj₁ issue →
  afterEmbedding limit project response ≡ done (preparationRequired issue)
refusedPreparationStartsNoRead limit project response issue refused rewrite refused = refl
