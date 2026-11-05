{-# OPTIONS --safe #-}
-- Public graph mutations and their ordered service effects. DEFEATS is stored
-- before propagation; propagation failure does not imply the edge disappeared.
module Mimir.GraphMutationProtocol where

open import Data.Bool using (Bool; true; false)
open import Data.Float.Base using (Float)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Mimir.Text using (Text)
open import Mimir.Binary64 using (Number)
import Mimir.ApplicationFloat as Numeric
import Mimir.CandidateGraph as G
import Mimir.LearningCandidates as C
import Mimir.GraphRecords as Records
import Mimir.GraphNumerics as Numbers
import Mimir.GraphWrites as Writes
import Mimir.ApplicationStore as Store
import Mimir.IndependentProvenance as Origin
import Mimir.BeliefEmbedding as Embedding
import Mimir.InferenceProtocol as Inference
import Mimir.ReviewSchema as R
import Mimir.DatabaseTransaction as DB
import Mimir.Effects as Effects
import Mimir.Validation as Validation

data Request : Set where
  belief : Text → Float → Float → Maybe Text → C.Memory → Maybe Origin.Provenance → Request
  patternNode : Text → Text → Float → Maybe Text → Request
  edge : ℕ → ℕ → R.Relation → Number → Request

data Statement : Set where
  insertPattern : G.PatternValues → Statement
  insertEdge : ℕ → ℕ → R.Relation → Number → Statement

meaning : Statement → Store.World → Writes.Result
meaning (insertPattern p) w = Writes.applied (Writes.insertPattern p w)
meaning (insertEdge from to relation weight) w = Writes.insertEdge from to relation weight w

-- A successful statement receipt is tied to this statement's write set.
data StatementReceipt (command : Statement) (before : Store.World) : DB.Receipt → Store.World → Set where
  published : ∀ proposed receipt after → meaning command before ≡ Writes.applied proposed →
    DB.Atomic before proposed receipt after → StatementReceipt command before receipt after

data Effect : Set where
  newIdentityAndTime : Effect
  statement : Statement → Effect
  embedding : Embedding.Effect → Effect
  inference : Inference.Effect → Effect

Reply : Effect → Set
Reply newIdentityAndTime = ℕ × ℤ
Reply (statement command) = Text ⊎ DB.Receipt
Reply (embedding effect) = Embedding.Reply effect
Reply (inference effect) = Inference.Reply effect

module E = Effects.Protocol Effect Reply
open E

data Result : Set where
  invalidNumbers invalidOrigin : Result
  failed : Text → Result
  aborted uncertain : Result
  insertedBelief : G.BeliefValues → Result
  insertedPattern : G.PatternValues → Result
  embeddingFailed : Embedding.Failure → Result
  propagationFailed : Inference.Result → Result
  edgeInserted : Result

liftEmbedding : Embedding.E.Script Embedding.Result → Script Embedding.Result
liftEmbedding (Embedding.E.done result) = done result
liftEmbedding (Embedding.E.ask effect next) = ask (embedding effect) (λ reply → liftEmbedding (next reply))

liftInference : Inference.E.Script Inference.Result → Script Inference.Result
liftInference (Inference.E.done result) = done result
liftInference (Inference.E.ask effect next) = ask (inference effect) (λ reply → liftInference (next reply))

afterEmbedding : G.BeliefValues → Embedding.Result → Script Result
afterEmbedding b (inj₁ error) = done (embeddingFailed error)
afterEmbedding b (inj₂ tt) = done (insertedBelief b)

makeBelief : Bool → Text → Float → Float → Maybe Text → C.Memory → Maybe Origin.Provenance → ℕ × ℤ → Script Result
makeBelief enabled content probability confidence project memory origin (id , now)
  with Records.newBelief id now content probability confidence project memory
... | nothing = done invalidNumbers
... | just b = liftEmbedding (Embedding.start enabled b origin) >>= afterEmbedding b

write : Statement → Script Result → Script Result
write command next = ask (statement command) (λ
  { (inj₁ error) → done (failed error)
  ; (inj₂ DB.committed) → next
  ; (inj₂ DB.aborted) → done aborted
  ; (inj₂ DB.acknowledgementLost) → done uncertain })

makePattern : Text → Text → Float → Maybe Text → ℕ × ℤ → Script Result
makePattern situation approach success project (id , now) with Records.newPattern id now situation approach success
... | nothing = done invalidNumbers
... | just p = write (insertPattern scoped) (done (insertedPattern scoped))
  where scoped = record p { project = project }

afterPropagation : Inference.Result → Script Result
afterPropagation (Inference.propagated values limit) = done edgeInserted
afterPropagation result = done (propagationFailed result)

afterEdge : R.Relation → ℕ → Script Result
afterEdge R.defeats from = liftInference (Inference.start (Inference.propagate from)) >>= afterPropagation
afterEdge R.supports from = done edgeInserted
afterEdge R.causes from = done edgeInserted
afterEdge R.contradicts from = done edgeInserted

start : Bool → Request → Script Result
start enabled (belief content probability confidence project memory nothing) = ask newIdentityAndTime
  (makeBelief enabled content probability confidence project memory nothing)
start enabled (belief content probability confidence project memory (just origin)) with Origin.validate origin
... | Validation.rejected fault invalid = done invalidOrigin
... | Validation.accepted valid = ask newIdentityAndTime (makeBelief enabled content probability confidence project memory (just origin))
start enabled (patternNode situation approach success project) = ask newIdentityAndTime (makePattern situation approach success project)
start enabled (edge from to relation weight) with Numeric.number weight
... | nothing = done invalidNumbers
... | just value with Numbers.probability value
...   | false = done invalidNumbers
...   | true = write (insertEdge from to relation weight) (afterEdge relation from)
