{-# OPTIONS --safe #-}
-- The intended replacement is the complete new index plus recomputation of
-- surviving beliefs that lost weighted evidence from the old document.
-- Indexing does not create new evidence from similarity scores.
module Mimir.DocumentReplacementRecovery where

open import Data.Bool using (true; false)
open import Data.Float.Base using (Float)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String using (toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Mimir.Text using (Text)
import Mimir.ApplicationStore as Store
import Mimir.DocumentStore as Documents
import Mimir.DocumentPublication as Publication
import Mimir.DocumentRemovalRecovery as Removal
import Mimir.GroundingRecovery as Ground
import Mimir.InferenceStorageBinding as Inference
import Mimir.PosteriorComputation as P
import Mimir.StructuredValue as Wire
import Mimir.Validation as Validation

answer : List Documents.Chunk → Wire.Value
answer chunks = Wire.object ((toList "loaded" , Wire.unsigned (length chunks)) ∷ [])

shapeFault : Validation.Fault
shapeFault = Validation.fault [] Validation.malformedInput
  "Prepare one complete usable vector of the declared dimension for every original document chunk before replacement. No partial document may be published."

module Business (dimension : ℕ) (databaseSum : List Float → Float) (calculator : P.Calculator) where
  module D = Publication.Publication dimension
  module G = Ground.Business databaseSum calculator
  module N = Inference.NumericalOutcome databaseSum
  Outcome = G.Diagnostic ⊎ (Store.World × Wire.Value)

  -- This function describes the stored result, independently of SQL order.
  -- Publication.clear removes old chunks, vectors and their GROUNDS edges.
  intendedIndex : Text → D.D.Store → Store.World → Store.World
  intendedIndex = D.publish

  module Selected (publicationTime : ℤ) (path : Text)
    (chunks : List Documents.Chunk) (entries : D.D.Store)
    (initial : Store.World) (selected : N.Context) where
    module Checked = G.Selected publicationTime selected

    Goal : Outcome → Set
    Goal (inj₁ diagnostic) = Checked.DiagnosticGoal diagnostic
    Goal (inj₂ (final , reply)) = Σ (List (ℕ × Float)) (λ numericalReply →
      N.Completed publicationTime selected (intendedIndex path entries initial) final numericalReply ×
      reply ≡ answer chunks)

    checked : Σ Outcome Goal
    checked with Checked.checked (intendedIndex path entries initial)
    ... | inj₁ diagnostic , correct = inj₁ diagnostic , correct
    ... | inj₂ (final , oldReply) , numericalReply , completed , replied =
      inj₂ (final , answer chunks) , numericalReply , completed , refl

    keepsJournal : ∀ final reply → Goal (inj₂ (final , reply)) →
      Store.World.operations final ≡ Store.World.operations initial
    keepsJournal final reply
      (numericalReply , (incoming , permutation , counts , valid , shape , complete , framed , answered) , replied)
      rewrite framed with N.Context.readOnly selected
    ... | true = refl
    ... | false = refl

  Goal : ℤ → Text → List Documents.Chunk → List Store.Vector → Store.World → Outcome → Set
  Goal publicationTime path chunks vectors initial outcome with D.plan path chunks vectors initial
  ... | D.invalidEmbeddingShape = outcome ≡ inj₁ (G.requestFault shapeFault)
  ... | D.invalidIdentity fault = outcome ≡ inj₁ (G.requestFault fault)
  ... | D.replace entries proposed with N.prepare (N.recompute (Removal.affected path initial)) proposed
  ...   | inj₁ problem = outcome ≡ inj₁ (G.preparation problem)
  ...   | inj₂ selected = Selected.Goal publicationTime path chunks entries initial selected outcome

  checked : ∀ publicationTime path chunks vectors initial →
    Σ Outcome (Goal publicationTime path chunks vectors initial)
  checked publicationTime path chunks vectors initial with D.plan path chunks vectors initial
  ... | D.invalidEmbeddingShape = inj₁ (G.requestFault shapeFault) , refl
  ... | D.invalidIdentity fault = inj₁ (G.requestFault fault) , refl
  ... | D.replace entries proposed with N.prepare (N.recompute (Removal.affected path initial)) proposed
  ...   | inj₁ problem = inj₁ (G.preparation problem) , refl
  ...   | inj₂ selected = Selected.checked publicationTime path chunks entries initial selected

  publicationKeepsJournal : ∀ publicationTime path chunks vectors initial final reply →
    Goal publicationTime path chunks vectors initial (inj₂ (final , reply)) →
    Store.World.operations final ≡ Store.World.operations initial
  publicationKeepsJournal publicationTime path chunks vectors initial final reply correct
    with D.plan path chunks vectors initial
  ... | D.invalidEmbeddingShape with correct
  ...   | ()
  publicationKeepsJournal publicationTime path chunks vectors initial final reply correct | D.invalidIdentity fault with correct
  ... | ()
  publicationKeepsJournal publicationTime path chunks vectors initial final reply correct | D.replace entries proposed
    with N.prepare (N.recompute (Removal.affected path initial)) proposed
  ... | inj₁ problem with correct
  ...   | ()
  publicationKeepsJournal publicationTime path chunks vectors initial final reply correct | D.replace entries proposed | inj₂ selected =
    Selected.keepsJournal publicationTime path chunks entries initial selected final reply correct

  journalUnchanged : ∀ publicationTime path chunks vectors initial final reply →
    proj₁ (checked publicationTime path chunks vectors initial) ≡ inj₂ (final , reply) →
    Store.World.operations final ≡ Store.World.operations initial
  journalUnchanged publicationTime path chunks vectors initial final reply accepted =
    publicationKeepsJournal publicationTime path chunks vectors initial final reply
      (subst (Goal publicationTime path chunks vectors initial) accepted
        (proj₂ (checked publicationTime path chunks vectors initial)))
