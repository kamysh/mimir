{-# OPTIONS --safe #-}
-- Public graph mutations publish complete operations atomically. Defeat-link
-- creation and recalculation commit together or leave no changes.
module Mimir.GraphMutationProtocol where

open import Data.Bool using (Bool; true; false)
open import Data.Float.Base using (Float)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Mimir.UUIDGroups using (UUID)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.Binary64 using (Number)
import Mimir.ApplicationFloat as Numeric
import Mimir.CandidateGraph as G
import Mimir.LearningCandidates as C
import Mimir.GraphNumerics as Numbers
import Mimir.GraphWrites as Writes
import Mimir.ApplicationStore as Store
import Mimir.IndependentProvenance as Origin
import Mimir.BeliefEmbedding as Embedding
import Mimir.InferenceProtocol as Inference
import Mimir.ReviewSchema as R
import Mimir.ReviewEdges as Edges
import Mimir.DatabaseTransaction as DB
import Mimir.Effects as Effects
import Mimir.Validation as Validation
import Mimir.Recovery as Recovery
open import Data.Empty using (⊥; ⊥-elim)

data Request : Set where
  belief : Text → Float → Float → Maybe Text → C.Memory → Maybe Origin.Provenance → Request
  patternNode : Text → Text → Float → Maybe Text → Request
  edge : UUID → UUID → R.Relation → Number → Request

data Statement : Set where
  insertEdge : UUID → UUID → R.Relation → Number → Statement

meaning : Statement → Store.World → Writes.Result
meaning (insertEdge from to relation weight) w = Writes.insertEdge from to relation weight w

-- The link and its completed recalculation are prepared privately and
-- published together. An abort publishes neither part.
data DefeatReceipt (from to : UUID) (weight : Number) (before : Store.World) :
  DB.Receipt → Store.World → Set where
  rolledBack : DefeatReceipt from to weight before DB.aborted before
  published : ∀ linked events proposed values after →
    Writes.insertEdge from to R.defeats weight before ≡ Writes.applied linked →
    Inference.PrivateRuns (Inference.start (Inference.propagate from)) linked events proposed
      (Inference.propagated values false) →
    DB.Atomic before proposed DB.committed after →
    DefeatReceipt from to weight before DB.committed after

-- A successful statement receipt is tied to this statement's write set.
data StatementReceipt (command : Statement) (before : Store.World) : DB.Receipt → Store.World → Set where
  published : ∀ proposed receipt after → meaning command before ≡ Writes.applied proposed →
    DB.Atomic before proposed receipt after → StatementReceipt command before receipt after

data Effect : Set where
  -- PostgreSQL creates the pattern and returns its stored identity.
  createPattern : Text → Text → Float → Maybe Text → Effect
  statement : Statement → Effect
  -- Link creation and recalculation have one atomic outcome.
  recordDefeat : UUID → UUID → Number → Effect
  embedding : Embedding.Effect → Effect

Reply : Effect → Set
Reply (createPattern situation approach success project) = Text ⊎ G.PatternValues
Reply (statement command) = Text ⊎ DB.Receipt
Reply (recordDefeat from to weight) = Text ⊎ DB.Receipt
Reply (embedding effect) = Embedding.Reply effect

module E = Effects.Protocol Effect Reply
open E

data Result : Set where
  invalidPatternRate invalidEdgeWeight invalidOrigin : Result
  failed : Text → Result
  aborted : Result
  insertedBelief : G.BeliefValues → Result
  insertedPattern : G.PatternValues → Result
  embeddingFailed : Embedding.Failure → Result
  edgeInserted : Result

liftEmbedding : Embedding.E.Script Embedding.Result → Script Embedding.Result
liftEmbedding (Embedding.E.done result) = done result
liftEmbedding (Embedding.E.ask effect next) = ask (embedding effect) (λ reply → liftEmbedding (next reply))

afterEmbedding : Embedding.Result → Script Result
afterEmbedding (inj₁ error) = done (embeddingFailed error)
afterEmbedding (inj₂ b) = done (insertedBelief b)

makeBelief : Bool → Text → Float → Float → Maybe Text → C.Memory → Maybe Origin.Provenance → Script Result
makeBelief enabled content probability confidence project memory origin =
  liftEmbedding (Embedding.start enabled
    (Embedding.draft content probability confidence project memory origin)) >>= afterEmbedding

write : Statement → Script Result → Script Result
write command next = ask (statement command) (λ
  { (inj₁ error) → done (failed error)
  ; (inj₂ DB.committed) → next
  ; (inj₂ DB.aborted) → done aborted })

makePattern : Text → Text → Float → Maybe Text → Script Result
makePattern situation approach success project with Numbers.probability success
... | false = done invalidPatternRate
... | true = ask (createPattern situation approach success project) λ where
  (inj₁ error) → done (failed error)
  (inj₂ patternValue) → done (insertedPattern patternValue)

makeDefeat : UUID → UUID → Number → Script Result
makeDefeat from to weight = ask (recordDefeat from to weight) λ where
  (inj₁ error) → done (failed error)
  (inj₂ DB.aborted) → done aborted
  (inj₂ DB.committed) → done edgeInserted

start : Bool → Request → Script Result
start enabled (belief content probability confidence project memory nothing) =
  makeBelief enabled content probability confidence project memory nothing
start enabled (belief content probability confidence project memory (just origin)) with Origin.validate origin
... | Validation.rejected fault invalid = done invalidOrigin
... | Validation.accepted valid = makeBelief enabled content probability confidence project memory (just origin)
start enabled (patternNode situation approach success project) = makePattern situation approach success project
start enabled (edge from to relation weight) with Numeric.number weight
... | nothing = done invalidEdgeWeight
... | just value with Numbers.probability value
...   | false = done invalidEdgeWeight
...   | true with relation
...     | R.defeats = makeDefeat from to weight
...     | R.supports = write (insertEdge from to R.supports weight) (done edgeInserted)
...     | R.causes = write (insertEdge from to R.causes weight) (done edgeInserted)
...     | R.contradicts = write (insertEdge from to R.contradicts weight) (done edgeInserted)

-- The recovery instruction says the link is already saved. This is justified
-- by the actual execution, not by the error's name.
module StatementRecovery (command : Statement) where
  finalState : Writes.Result → Store.World → Store.World
  finalState (Writes.applied proposed) before = proposed
  finalState _ before = before

  intended : Store.World → Store.World
  intended before = finalState (meaning command before) before

  Successful : Result → Set
  Successful edgeInserted = ⊤
  Successful _ = ⊥

  Atomic : Store.World → (effect : Effect) → Reply effect → Store.World → Set
  Atomic before (statement actual) (inj₂ receipt) after = StatementReceipt actual before receipt after
  Atomic before _ _ after = after ≡ before

  module Proof = Recovery Store.World Effect Result (λ _ → ⊤) Reply Atomic
    (λ before after → after ≡ before) (λ _ _ → Store.World) (λ _ _ world → world)
    (λ _ world → world) Successful (λ _ → ⊤)

  program = write command (done edgeInserted)

  interruptedUnchanged : ∀ before after → Proof.Interrupted program before after → after ≡ before
  interruptedUnchanged before after (Proof.stopped same) = same
  interruptedUnchanged before after (Proof.replied {reply = inj₁ error} atomic ())
  interruptedUnchanged before after (Proof.replied {reply = inj₂ DB.aborted} atomic ())
  interruptedUnchanged before after (Proof.replied {reply = inj₂ DB.committed} atomic ())

  failedUnchanged : ∀ before after → Proof.Failed program before after → after ≡ before
  failedUnchanged before after (Proof.failedReply {reply = inj₁ error} same (Proof.failedReturn notSuccessful)) = same
  failedUnchanged before after (Proof.failedReply {reply = inj₂ DB.aborted}
    (published proposed _ _ equation DB.abortedNone) (Proof.failedReturn notSuccessful)) = refl
  failedUnchanged before after (Proof.failedReply {reply = inj₂ DB.committed} atomic (Proof.failedReturn notSuccessful)) =
    ⊥-elim (notSuccessful tt)

  achieves : ∀ before after → Proof.Completed program before after → after ≡ intended before
  achieves before after (Proof.replied {reply = inj₁ error} atomic (Proof.returned ()))
  achieves before after (Proof.replied {reply = inj₂ DB.aborted} atomic (Proof.returned ()))
  achieves before after (Proof.replied {reply = inj₂ DB.committed}
    (published proposed _ _ equation DB.committedAll) (Proof.returned succeeded)) rewrite equation = refl

  atomicStatement : Proof.AllOrNothing ⊤
  atomicStatement = record
    { expected = λ _ before _ → intended before
    ; script = λ _ → program
    ; interruptedUnchanged = λ _ → interruptedUnchanged
    ; failedUnchanged = λ _ → failedUnchanged
    ; achieves = λ _ before after complete _ → achieves before after complete
    }
  module Certified = Proof.Transactional atomicStatement
  recovery : Proof.Recoverable ⊤
  recovery = Certified.transactional

module DefeatRecovery (from to : UUID) (weight : Number) where
  intendedLinks : Store.World → List Edges.Edge
  intendedLinks before with Writes.insertEdge from to R.defeats weight before
  ... | Writes.invalidWeight = Store.edges before
  ... | Writes.missingEndpoint = Store.edges before
  ... | Writes.applied proposed = Store.edges proposed

  Atomic : Store.World → ⊤ → Text ⊎ DB.Receipt → Store.World → Set
  Atomic before tt (inj₁ detail) after = after ≡ before
  Atomic before tt (inj₂ receipt) after = DefeatReceipt from to weight before receipt after

  answer : Text ⊎ DB.Receipt → Result
  answer (inj₁ detail) = failed detail
  answer (inj₂ DB.aborted) = aborted
  answer (inj₂ DB.committed) = edgeInserted

  module Proof = Recovery Store.World ⊤ Result (λ _ → ⊤) (λ _ → Text ⊎ DB.Receipt)
    Atomic (λ before after → after ≡ before)
    (λ _ _ → List Edges.Edge) (λ _ _ → Store.edges) (λ _ before → before)
    (λ result → result ≡ edgeInserted) (λ _ → ⊤)

  achieves : (input : ⊤) → ∀ before reply after → Atomic before tt reply after →
    answer reply ≡ edgeInserted → (index : ⊤) → Store.edges after ≡ intendedLinks before
  achieves input before (inj₁ detail) after atomic () index
  achieves input before (inj₂ DB.aborted) after atomic () index
  achieves input before (inj₂ DB.committed) after
    (published linked events proposed values .proposed equation calculation DB.committedAll) success index
    rewrite equation = Inference.privateCalculationPreservesLinks calculation

  failedUnchanged : ∀ before reply after → Atomic before tt reply after →
    (answer reply ≡ edgeInserted → ⊥) → after ≡ before
  failedUnchanged before (inj₁ detail) after same notSuccessful = same
  failedUnchanged before (inj₂ DB.aborted) .before rolledBack notSuccessful = refl
  failedUnchanged before (inj₂ DB.committed) after atomic notSuccessful = ⊥-elim (notSuccessful refl)

  call : Proof.FinalCall ⊤
  call = record
    { effect = λ _ → tt
    ; answer = λ _ → answer
    ; expected = λ _ before _ → intendedLinks before
    ; success = achieves
    ; failureUnchanged = λ _ → failedUnchanged
    ; crashUnchanged = λ _ _ same → same
    }
  module Certified = Proof.FinalPublication call
  recovery : Proof.Recoverable ⊤
  recovery = Certified.finalPublication
