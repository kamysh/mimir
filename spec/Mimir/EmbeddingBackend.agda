{-# OPTIONS --safe #-}
-- Backend-specific application policy. HTTP, tokenization and ONNX execution
-- are dependency operations; caching, complete input, padding, pooling and
-- response alignment are Mimir decisions. No model/network operation is run by
-- checking this specification.
module Mimir.EmbeddingBackend where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_; _++_; length; foldl; replicate)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _⊔_; _∸_; _≤?_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.String using (toList)
import Data.Vec as V
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (does)
open import Mimir.Text using (Text; trim)
import Mimir.RetrievalRanking as Ranking
import Mimir.ConfigurationValues as Config
import Mimir.EmbeddingBatch as Batch
import Mimir.Effects as Effects
import Mimir.ConfigurationPath as Path

endpoint : Config.Backend → Maybe Text
endpoint Config.voyage = just (toList "https://api.voyageai.com/v1/embeddings")
endpoint Config.openai = just (toList "https://api.openai.com/v1/embeddings")
endpoint Config.local = nothing

inputType : Config.Backend → Maybe Text
inputType Config.voyage = just (toList "document")
inputType Config.openai = nothing
inputType Config.local = nothing

cacheOverride : Maybe Text → Maybe Text
cacheOverride nothing = nothing
cacheOverride (just path) with trim path
... | [] = nothing
... | clean@(_ ∷ _) = just clean

record Tokens : Set where
  constructor tokens
  field ids masks types : List ℕ

sequenceLength : List Tokens → ℕ
sequenceLength inputs = foldl (λ n t → n ⊔ length (Tokens.ids t)) 0 inputs

-- This is the configured BGE model's declared position table, explicitly
-- approved by the user. It is checked against complete encodings, including
-- special tokens, before model execution; it never selects a source prefix.
withinModelCapacity : List Tokens → Bool
withinModelCapacity [] = true
withinModelCapacity (first ∷ rest) = does (length (Tokens.ids first) ≤? 512) ∧ withinModelCapacity rest

pad : ℕ → List ℕ → List ℕ
pad size values = values ++ replicate (size ∸ length values) 0

paddingRetainsCompleteInput : ∀ size values → pad size values ≡ values ++ replicate (size ∸ length values) 0
paddingRetainsCompleteInput size values = refl

padTokens : ℕ → Tokens → Tokens
padTokens size t = tokens (pad size (Tokens.ids t)) (pad size (Tokens.masks t)) (pad size (Tokens.types t))

module Remote (float : Ranking.F32) (dimension : ℕ) where
  open Ranking.F32 float
  module B = Batch.Batch Value dimension
  Vector = V.Vec Value dimension

  -- Provider indices, count and dimension are checked before consumers see
  -- vectors. Native parse_embeddings currently ignores indices: that is a
  -- conformance gap, not a reason to weaken EmbeddingBatch's existing laws.
  remoteResult : (count : ℕ) → List B.Row → B.Error ⊎ V.Vec Vector count
  remoteResult count rows with B.align 0 count rows
  ... | inj₁ error = inj₁ error
  ... | inj₂ (vectors , proof) = inj₂ vectors

module Arithmetic (float : Ranking.F32) where
  open Ranking.F32 float
  Vector = V.Vec Value 768

  accumulate : Vector × Value → Bool × Vector → Vector × Value
  accumulate state (false , hidden) = state
  accumulate (sum , count) (true , hidden) = V.zipWith add sum hidden , add count (fromNat 1)

  meanPool : List (Bool × Vector) → Vector
  meanPool hidden with foldl accumulate (V.replicate 768 (fromNat 0) , fromNat 0) hidden
  ... | sum , count with less (fromNat 0) count
  ...   | false = sum
  ...   | true = V.map (λ value → divide value count) sum

  data Effect : Set where
    cached : Path.Path → Effect
    mkdirParents : Path.Path → Effect
    downloadToPart : Text → Path.Path → Effect -- URL and owned partial path; no deadline or redirect quota
    rename : Path.Path → Path.Path → Effect
    loadTokenizer loadModel optimizeModel makeRunnable : Path.Path → Effect
    tokenize : List Text → Bool → Effect
    runModel : List Tokens → ℕ → Effect

  Reply : Effect → Set
  Reply (cached path) = Bool
  Reply (mkdirParents path) = Text ⊎ ⊤
  Reply (downloadToPart url path) = Text ⊎ ⊤
  Reply (rename source destination) = Text ⊎ ⊤
  Reply (loadTokenizer path) = Text ⊎ ⊤
  Reply (loadModel path) = Text ⊎ ⊤
  Reply (optimizeModel path) = Text ⊎ ⊤
  Reply (makeRunnable path) = Text ⊎ ⊤
  Reply (tokenize texts specialTokens) = Text ⊎ V.Vec Tokens (length texts)
  -- Successful tensor extraction exposes exactly the addressed [batch,seq,768]
  -- slice. Dtype/rank/index failures are dependency failures (a native panic is
  -- surfaced by the spawn_blocking join). Masks come from Mimir's input tensor,
  -- not from a model-supplied Boolean attached to each output vector.
  Reply (runModel inputs seqLength) = Text ⊎ V.Vec (V.Vec Vector seqLength) (length inputs)

  module E = Effects.Protocol Effect Reply
  open E

  ensureFile : Text → Path.Path → Path.Path → Script (Text ⊎ ⊤)
  ensureFile url destination part = ask (cached destination) (λ
    { true → done (inj₂ tt)
    ; false → ask (mkdirParents destination) (λ
      { (inj₁ error) → done (inj₁ error)
      ; (inj₂ tt) → ask (downloadToPart url part) (λ
        { (inj₁ error) → done (inj₁ error)
        ; (inj₂ tt) → ask (rename part destination) done }) }) })

  mask : ℕ → Bool
  mask zero = false
  mask (suc _) = true

  masked : ∀ {size} → List ℕ → V.Vec Vector size → List (Bool × Vector)
  masked masks V.[] = []
  masked [] (hidden V.∷ rest) = (false , hidden) ∷ masked [] rest
  masked (m ∷ ms) (hidden V.∷ rest) = (mask m , hidden) ∷ masked ms rest

  pool : ∀ {count size} → V.Vec Tokens count → V.Vec (V.Vec Vector size) count → List Vector
  pool V.[] V.[] = []
  pool (encoded V.∷ rest) (hidden V.∷ later) = meanPool (masked (Tokens.masks encoded) hidden) ∷ pool rest later

  encodedBatch : ∀ {count} → V.Vec Tokens count → Script (Text ⊎ List Vector)
  encodedBatch encoded with withinModelCapacity (V.toList encoded)
  ... | false = done (inj₁ (toList "Complete input exceeds BAAI/bge-base-en-v1.5's declared 512 positions, including special tokens. Open a user dialog; do not truncate, split, or change models automatically."))
  ... | true = ask (runModel inputs size) (λ
    { (inj₁ error) → done (inj₁ error)
    ; (inj₂ hidden) → done (inj₂ (pool (V.fromList inputs) hidden)) })
    where
    size = sequenceLength (V.toList encoded)
    inputs = Data.List.map (padTokens size) (V.toList encoded)

  afterTokenization : ∀ {count} → Text ⊎ V.Vec Tokens count → Script (Text ⊎ List Vector)
  afterTokenization (inj₁ error) = done (inj₁ error)
  afterTokenization (inj₂ encoded) = encodedBatch encoded

  batch : List Text → Script (Text ⊎ List Vector)
  batch texts = ask (tokenize texts true) afterTokenization

  complete : List Text → Script (Text ⊎ List Vector)
  complete [] = done (inj₂ [])
  complete texts@(_ ∷ _) = batch texts

  completeRequestTokenizedTogether : ∀ first rest →
    complete (first ∷ rest) ≡ ask (tokenize (first ∷ rest) true) afterTokenization
  completeRequestTokenizedTogether first rest = refl

data CacheState : Set where unloaded loading ready poisoned : CacheState
data CacheEvent : Set where acquire loaded failed releasePoison : CacheEvent

data CacheStep : CacheState → CacheEvent → CacheState → Set where
  beginLoad : CacheStep unloaded acquire loading
  reuse : CacheStep ready acquire ready
  publishReady : CacheStep loading loaded ready
  retryable : CacheStep loading failed unloaded
  poison : ∀ before → CacheStep before releasePoison poisoned

-- Only successful complete loading publishes the reusable model state.
failedLoadCanRetry : CacheStep loading failed unloaded
failedLoadCanRetry = retryable
