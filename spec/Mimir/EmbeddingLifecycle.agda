{-# OPTIONS --safe #-}
-- Local loading and remote request policy. Dependency calls expose their
-- failures; neither an attempted load nor a model answer publishes readiness.
module Mimir.EmbeddingLifecycle where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; length; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Data.Product using (Σ; _×_; _,_)
open import Data.String using (toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Mimir.Text using (Text)
open import Mimir.RecordDecoding using (_>>=_; mapResult)
import Mimir.EmbeddingBackend as Backend
import Mimir.ConfigurationPath as Path
import Mimir.ConfigurationValues as Config
import Mimir.RetrievalRanking as Ranking
import Mimir.StructuredValue as V
import Mimir.PublicInput as Input
import Mimir.Validation as Validation
import Mimir.Binary64 as Binary
import Mimir.Effects as Effects
import Data.Vec

-- One source per embedding call. Stop and completion are terminal, ordered
-- transitions; finishing cannot revive cancelled work or revoke a result.
module Ownership where
  data State : Set where running cancelled finished : State

  stop complete : State → State
  stop running = cancelled
  stop cancelled = cancelled
  stop finished = finished
  complete running = finished
  complete cancelled = cancelled
  complete finished = finished

  owned : State → Bool
  owned running = true
  owned cancelled = false
  owned finished = false

  stopReleasesOwnership : ∀ state → owned (stop state) ≡ false
  stopReleasesOwnership running = refl
  stopReleasesOwnership cancelled = refl
  stopReleasesOwnership finished = refl

  completionReleasesOwnership : ∀ state → owned (complete state) ≡ false
  completionReleasesOwnership running = refl
  completionReleasesOwnership cancelled = refl
  completionReleasesOwnership finished = refl

  completionCannotUndoStop : ∀ state → complete (stop state) ≡ stop state
  completionCannotUndoStop running = refl
  completionCannotUndoStop cancelled = refl
  completionCannotUndoStop finished = refl

  World = ℕ → State
  stopJob : ℕ → World → World
  stopJob identity world observed with observed ≟ identity
  ... | yes _ = stop (world observed)
  ... | no _ = world observed

  otherJobsKeepTheirOwnership : ∀ identity other world → other ≢ identity →
    stopJob identity world other ≡ world other
  otherJobsKeepTheirOwnership identity other world different with other ≟ identity
  ... | yes same = ⊥-elim (different same)
  ... | no _ = refl

root : Maybe Text → Maybe Path.NativePath → Maybe Path.Path
root override home with Backend.cacheOverride override
... | just path = just (Path.utf8 path)
... | nothing with home
...   | nothing = nothing
...   | just path = just (Path.join (Path.native path) (toList ".cache/mimir/models"))

modelDirectory : Path.Path → Path.Path
modelDirectory path = Path.join path (toList "BAAI--bge-base-en-v1.5")

tokenizerPath modelPath : Path.Path → Path.Path
tokenizerPath path = Path.join (modelDirectory path) (toList "tokenizer.json")
modelPath path = Path.join (modelDirectory path) (toList "onnx/model.onnx")

-- Stopping a local worker is independent of progress by its model. A stop
-- result requires the OS wait receipt, rather than merely sending a signal.
module WorkerStop where
  data Effect : Set where kill waitForExit : Effect
  Reply : Effect → Set
  Reply _ = Text ⊎ ⊤
  module E = Effects.Protocol Effect Reply
  stop : E.Script (Text ⊎ ⊤)
  stop = E.ask kill λ _ → E.ask waitForExit E.done

  killAlwaysPrecedesWait : ∀ continuation →
    stop ≢ E.ask waitForExit continuation
  killAlwaysPrecedesWait continuation ()

  stopRequiresExitReceipt : ∀ {events result} → E.Runs stop events result →
    Σ (Reply kill) (λ acknowledgement →
      events ≡ (kill , acknowledgement) ∷ (waitForExit , result) ∷ [])
  stopRequiresExitReceipt (E.replied _ _ acknowledgement (E.replied _ _ result (E.returned _))) =
    acknowledgement , refl

module Local (float : Ranking.F32) where
  module A = Backend.Arithmetic float
  open A.E using (Script; done; ask) renaming (_>>=_ to _then_)

  -- withExtension follows the platform Path::with_extension dependency. PID
  -- is part of the suffix; a different process never intentionally shares it.
  load : (Path.Path → Text → Path.Path) → Text → Path.Path → Script (Text ⊎ ⊤)
  load withExtension pid base = let tokenizer = tokenizerPath base; model = modelPath base in A.ensureFile
    (toList "https://huggingface.co/BAAI/bge-base-en-v1.5/resolve/main/tokenizer.json")
    tokenizer (withExtension tokenizer (toList "part-" ++ pid)) then λ where
      (inj₁ error) → done (inj₁ error)
      (inj₂ tt) → A.ensureFile
        (toList "https://huggingface.co/BAAI/bge-base-en-v1.5/resolve/main/onnx/model.onnx")
        model (withExtension model (toList "part-" ++ pid)) then λ where
          (inj₁ error) → done (inj₁ error)
          (inj₂ tt) → ask (A.loadTokenizer tokenizer) λ where
            (inj₁ error) → done (inj₁ error)
            (inj₂ tt) → ask (A.loadModel model) λ where
              (inj₁ error) → done (inj₁ error)
              (inj₂ tt) → ask (A.optimizeModel model) λ where
                (inj₁ error) → done (inj₁ error)
                (inj₂ tt) → ask (A.makeRunnable model) done

  data State : Set where
    idle : Backend.CacheState → State
    loading : A.E.Script (Text ⊎ ⊤) → State
    embedding : A.E.Script (Text ⊎ List A.Vector) → State
    joining : Text ⊎ List A.Vector → State
    returned : Backend.CacheState → Text ⊎ List A.Vector → State
    stopping : WorkerStop.E.Script (Text ⊎ ⊤) → State
    stopped : Text ⊎ ⊤ → State

  data Step (withExtension : Path.Path → Text → Path.Path) (pid : Text)
    (base : Path.Path) (texts : List Text) : State → State → Set where
    fresh : Step withExtension pid base texts (idle Backend.unloaded)
      (loading (load withExtension pid base))
    reuse : Step withExtension pid base texts (idle Backend.ready)
      (embedding (A.complete texts))
    poisoned : Step withExtension pid base texts (idle Backend.poisoned)
      (returned Backend.poisoned (inj₁ (toList "embed state mutex poisoned")))
    loadReply : ∀ effect continuation reply →
      Step withExtension pid base texts (loading (ask effect continuation)) (loading (continuation reply))
    loadFailed : ∀ error → Step withExtension pid base texts (loading (done (inj₁ error)))
      (returned Backend.unloaded (inj₁ error))
    loaded : Step withExtension pid base texts (loading (done (inj₂ tt)))
      (embedding (A.complete texts))
    batchReply : ∀ effect continuation reply → Step withExtension pid base texts
      (embedding (ask effect continuation)) (embedding (continuation reply))
    completed : ∀ result → Step withExtension pid base texts (embedding (done result)) (joining result)
    joined : ∀ result → Step withExtension pid base texts (joining result) (returned Backend.ready result)
    joinFailed : ∀ result error → Step withExtension pid base texts (joining result)
      (returned Backend.ready (inj₁ error))
    cancelLoading : ∀ script → Step withExtension pid base texts
      (loading script) (stopping WorkerStop.stop)
    cancelEmbedding : ∀ script → Step withExtension pid base texts
      (embedding script) (stopping WorkerStop.stop)
    cancelJoining : ∀ result → Step withExtension pid base texts
      (joining result) (stopping WorkerStop.stop)
    stopReply : ∀ effect continuation reply → Step withExtension pid base texts
      (stopping (WorkerStop.E.ask effect continuation)) (stopping (continuation reply))
    stopReturned : ∀ result → Step withExtension pid base texts
      (stopping (WorkerStop.E.done result)) (stopped result)

  -- Quantification includes a blocked dependency at any point of either
  -- script: cancellation needs no tokenizer, download or inference reply.
  canStopEveryLoadingStage : ∀ extension pid base texts script →
    Step extension pid base texts (loading script) (stopping WorkerStop.stop)
  canStopEveryLoadingStage extension pid base texts script = cancelLoading script

  canStopEveryInferenceStage : ∀ extension pid base texts script →
    Step extension pid base texts (embedding script) (stopping WorkerStop.stop)
  canStopEveryInferenceStage extension pid base texts script = cancelEmbedding script

  start : Backend.CacheState → List Text → State
  start cached [] = returned cached (inj₂ [])
  start cached (_ ∷ _) = idle cached

  emptyDoesNotLoad : ∀ cached → start cached [] ≡ returned cached (inj₂ [])
  emptyDoesNotLoad cached = refl

module Remote (float : Ranking.F32) (dimension maximumIndex : ℕ)
  (numeric : V.Value → Validation.Fault ⊎ Ranking.F32.Value float) where
  module R = Backend.Remote float dimension
  module B = R.B

  numbers : List V.Value → Validation.Fault ⊎ List (Ranking.F32.Value float)
  numbers [] = inj₂ []
  numbers (value ∷ rest) = numeric value >>= λ number → mapResult (number ∷_) (numbers rest)

  row : V.Value → Validation.Fault ⊎ B.Row
  row raw = V.asObject raw >>= λ fields →
    Input.required "index" (Input.unsigned maximumIndex) (V.Object.normalize fields) >>= λ index →
    Input.required "embedding" V.asArray (V.Object.normalize fields) >>= λ values →
    mapResult (B.row index) (numbers values)

  rows : List V.Value → Validation.Fault ⊎ List B.Row
  rows [] = inj₂ []
  rows (value ∷ rest) = row value >>= λ first → mapResult (first ∷_) (rows rest)

  decode : V.Value → Validation.Fault ⊎ List B.Row
  decode raw = V.asObject raw >>= λ fields →
    Input.required "data" V.asArray (V.Object.normalize fields) >>= rows

  requestFields : Config.Backend → List (Text × V.Value)
  requestFields Config.voyage = (toList "input_type" , V.string (toList "document")) ∷
    (toList "truncation" , V.boolean false) ∷ []
  requestFields Config.openai = []
  requestFields Config.local = []

  request : Config.Backend → Text → List Text → V.Value
  request backend model texts = V.object
    ((toList "input" , V.array (map V.string texts)) ∷ (toList "model" , V.string model) ∷ requestFields backend)

  data Failure : Set where
    invalidBackend : Failure
    transport httpStatus json : Text → Failure
    schema : Validation.Fault → Failure
    alignment : B.Error → Failure

  data Effect : Set where
    post : Text → Text → V.Value → Effect -- endpoint, bearer key, body
    status jsonBody : Effect

  Reply : Effect → Set
  Reply (post _ _ _) = Text ⊎ ⊤
  Reply status = Text ⊎ ⊤
  Reply jsonBody = Text ⊎ V.Value
  module P = Effects.Protocol Effect Reply

  check : (count : ℕ) → V.Value → Failure ⊎ List R.Vector
  check count value with decode value
  ... | inj₁ error = inj₁ (schema error)
  ... | inj₂ values with R.remoteResult count values
  ...   | inj₁ error = inj₁ (alignment error)
  ...   | inj₂ vectors = inj₂ (Data.Vec.toList vectors)

  run : Config.Backend → Text → Text → List Text → P.Script (Failure ⊎ List R.Vector)
  run backend key model texts with Backend.endpoint backend
  ... | nothing = P.done (inj₁ invalidBackend)
  ... | just url = P.ask (post url key (request backend model texts)) λ where
    (inj₁ error) → P.done (inj₁ (transport error))
    (inj₂ tt) → P.ask status λ where
      (inj₁ error) → P.done (inj₁ (httpStatus error))
      (inj₂ tt) → P.ask jsonBody λ where
        (inj₁ error) → P.done (inj₁ (json error))
        (inj₂ value) → P.done (check (length texts) value)
