{-# OPTIONS --safe #-}
-- The complete project ownership closure is published in one transaction.
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

-- Select ownership from the original world, before removing discovery roots.
-- These are components of one proposed world, not separately committed steps.
eraseProject : Text → Store.World → Store.World
eraseProject project before = forgetLearning project
  (Store.removeChunkVectors chunkIDs (Store.removeChunks chunkIDs
    (Store.removeBeliefVectors beliefIDs
      (Writes.deleteProjectPatterns project (Writes.deleteProjectBeliefs project before)))))
  where
  beliefIDs = Writes.projectBeliefs project before
  chunkIDs = projectChunks project before

deletedCount : Text → Store.World → ℕ
deletedCount project before = length (Writes.projectBeliefs project before) + length (projectChunks project before)

module Operation (database : ℕ) where
  module T = Transaction.Over Store.World ℕ Text database 671942183

  plan : Text → Store.World → T.Decision
  plan project before = T.replace (eraseProject project before) (deletedCount project before)

  Effect = T.Effect
  Reply = T.Reply
  module E = T.E

  data Result : Set where
    transactionResult : T.Outcome → Result
    deleted : ℕ → Result

  finish : T.Outcome → E.Script Result
  finish (T.applied count) = E.done (deleted count)
  finish result = E.done (transactionResult result)

  start : Text → E.Script Result
  start project = E._>>=_ Tx.start finish
    where module Tx = T.Plan (plan project)

  Publication : Text → Store.World → DB.Receipt → Store.World → Set
  Publication project before receipt after = DB.Atomic before (eraseProject project before) receipt after

  noPartiallyDeletedPublication : ∀ project before receipt after →
    Publication project before receipt after →
    after ≡ before ⊎ after ≡ eraseProject project before
  noPartiallyDeletedPublication project before .DB.committed .(eraseProject project before) DB.committedAll = inj₂ refl
  noPartiallyDeletedPublication project before .DB.aborted .before DB.abortedNone = inj₁ refl
  noPartiallyDeletedPublication project before .DB.acknowledgementLost .before DB.unknownBefore = inj₁ refl
  noPartiallyDeletedPublication project before .DB.acknowledgementLost .(eraseProject project before) DB.unknownAfter = inj₂ refl
