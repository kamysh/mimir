{-# OPTIONS --safe #-}
-- Project deletion is a sequence of independently committed store operations.
-- Its returned count is the observed belief count plus the observed chunk
-- count; patterns are removed but do not contribute to that count.
module Mimir.ProjectDeletion where

open import Data.Bool using (Bool; true; false; not)
open import Data.List using (List; []; _∷_; filterᵇ; map; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _+_; z≤n)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.ApplicationStore as Store
import Mimir.GraphWrites as Writes
import Mimir.LearningStore as Learning
import Mimir.ReviewPreparationPublication as Publication
import Mimir.ReviewLedger as Ledger
import Mimir.ExperienceRead as Read
import Mimir.ExperienceSchema as Experience
import Mimir.ReviewObservation as Observation
import Mimir.CandidateRegistry as Candidates
import Mimir.AssessmentWrites as Assessments
import Mimir.ItemOwners as Owners
import Mimir.RetrievalRanking as Ranking
import Mimir.DocumentStore as Documents
import Mimir.LearningTransaction as Transaction
import Mimir.DatabaseTransaction as DB
import Mimir.Effects as Effects

ownedExperiences : Text → Learning.World → List ℕ
ownedExperiences project w = map Read.identity (filterᵇ (Read.scopeMatches (just project)) (Learning.World.current w))

-- SQL foreign-key cascades remove relational history and ownership. Graph
-- nodes/edges are not FK targets; the preceding graph DELETE phases own them.
forgetLearning : Text → Store.World → Store.World
forgetLearning project w = record w { learning = record learn
  { current = filterᵇ (λ r → keep (Read.identity r)) (Learning.World.current learn)
  ; sources = filterᵇ (λ r → keep (Experience.Experience.identity (Learning.SourceVersion.payload r))) (Learning.World.sources learn)
  ; reviewTimes = filterᵇ (λ r → keep (Learning.ReviewTime.experience r)) (Learning.World.reviewTimes learn)
  ; itemKeys = keys
  ; publication = record pub
    { ledger = Ledger.world cells histories
    ; registry = filterᵇ (λ r → keep (Candidates.Entry.experienceID r)) (Publication.World.registry pub)
    ; assessments = filterᵇ (λ r → keep (Assessments.Row.experience r)) (Publication.World.assessments pub)
    ; owners = owners } } }
  where
  learn = Store.World.learning w
  pub = Learning.World.publication learn
  ledger = Publication.World.ledger pub
  ids = ownedExperiences project learn
  keep : ℕ → Bool
  keep id = not (Ranking.member id ids)
  keys : ℕ → Text → Maybe ℕ
  keys experience name with Ranking.member experience ids
  ... | true = nothing
  ... | false = Learning.World.itemKeys learn experience name
  cells : ℕ → Ledger.R.Cell
  cells id with Ranking.member id ids
  ... | true = Ledger.R.cell [] 0 0 0 nothing z≤n
  ... | false = Ledger.World.cells ledger id
  histories : ℕ → List Ledger.Version
  histories id with Ranking.member id ids
  ... | true = []
  ... | false = Ledger.World.histories ledger id
  owners : Owners.Registry
  owners id with Publication.World.owners pub id
  ... | nothing = nothing
  ... | just (owner , provenance) with Ranking.member owner ids
  ...   | true = nothing
  ...   | false = just (owner , provenance)

forgottenExperienceKeysRemoved : ∀ project before experience name →
  Ranking.member experience (ownedExperiences project (Store.World.learning before)) ≡ true →
  Learning.World.itemKeys (Store.World.learning (forgetLearning project before)) experience name ≡ nothing
forgottenExperienceKeysRemoved project before experience name removed rewrite removed = refl

otherExperienceKeysPreserved : ∀ project before experience name →
  Ranking.member experience (ownedExperiences project (Store.World.learning before)) ≡ false →
  Learning.World.itemKeys (Store.World.learning (forgetLearning project before)) experience name ≡
    Learning.World.itemKeys (Store.World.learning before) experience name
otherExperienceKeysPreserved project before experience name retained rewrite retained = refl

projectChunks : Text → Store.World → List ℕ
projectChunks project w = map Documents.Chunk.identity
  (filterᵇ (λ c → Writes.tagged project (Documents.Chunk.project c)) (Store.World.chunks w))

data Statement : Set where
  beliefs patterns : Text → Statement
  beliefVectors chunks chunkVectors : List ℕ → Statement

apply : Statement → Store.World → Store.World
apply (beliefs project) = Writes.deleteProjectBeliefs project
apply (patterns project) = Writes.deleteProjectPatterns project
apply (beliefVectors ids) = Store.removeBeliefVectors ids
apply (chunks ids) = Store.removeChunks ids
apply (chunkVectors ids) = Store.removeChunkVectors ids

module Operation (database : ℕ) where
  module T = Transaction.Over Store.World ⊤ Text database 671942183

  plan : Text → Store.World → T.Decision
  plan project w = T.replace (forgetLearning project w) tt

  data Effect : Set where
    observedBeliefs observedChunks : Text → Effect
    statement : Statement → Effect
    learning : T.Effect → Effect

  Reply : Effect → Set
  Reply (observedBeliefs project) = Text ⊎ List ℕ
  Reply (observedChunks project) = Text ⊎ List ℕ
  Reply (statement command) = Text ⊎ DB.Receipt
  Reply (learning effect) = T.Reply effect

  module E = Effects.Protocol Effect Reply
  open E

  data Result : Set where
    failed : Text → Result
    aborted uncertain : Statement → Result
    learningResult : T.Outcome → Result
    deleted : ℕ → Result

  liftLearning : T.E.Script T.Outcome → Script T.Outcome
  liftLearning (T.E.done result) = done result
  liftLearning (T.E.ask effect next) = ask (learning effect) (λ reply → liftLearning (next reply))

  write : Statement → Script Result → Script Result
  write command next = ask (statement command) (λ
    { (inj₁ error) → done (failed error)
    ; (inj₂ DB.aborted) → done (aborted command)
    ; (inj₂ DB.acknowledgementLost) → done (uncertain command)
    ; (inj₂ DB.committed) → next })

  finish : ℕ → T.Outcome → Script Result
  finish count (T.applied tt) = done (deleted count)
  finish count result = done (learningResult result)

  afterChunks : Text → ℕ → Text ⊎ List ℕ → Script Result
  afterChunks project count (inj₁ error) = done (failed error)
  afterChunks project count (inj₂ ids) = write (chunks ids) (write (chunkVectors ids)
    (liftLearning Tx.start >>= finish (count + length ids)))
    where module Tx = T.Plan (plan project)

  afterBeliefs : Text → Text ⊎ List ℕ → Script Result
  afterBeliefs project (inj₁ error) = done (failed error)
  afterBeliefs project (inj₂ ids) = write (beliefs project) (write (patterns project)
    (write (beliefVectors ids) (ask (observedChunks project) (afterChunks project (length ids)))))

  start : Text → Script Result
  start project = ask (observedBeliefs project) (afterBeliefs project)

  StatementPublication : Statement → Store.World → DB.Receipt → Store.World → Set
  StatementPublication command before receipt after = DB.Atomic before (apply command before) receipt after

  learningPreservesGraph : ∀ project before → Store.nodes (forgetLearning project before) ≡ Store.nodes before
  learningPreservesGraph project before = refl
