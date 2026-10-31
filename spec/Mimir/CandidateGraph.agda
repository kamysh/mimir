{-# OPTIONS --safe #-}
-- Complete node-creation values for experience-owned candidates and their
-- relationship to checked reservation batches. Numeric constants here are
-- exactly representable. Standard Float is the application numeric carrier;
-- clock and generated identities are explicit inputs.
module Mimir.CandidateGraph where

open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.All.Properties as AllProperties
open import Data.Maybe using (Maybe; just)
open import Data.Integer using (ℤ)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Unit using (tt)
open import Data.Float.Base using (Float)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
open import Mimir.Text using (Text)
open import Mimir.LearningCandidates using (Candidate; Memory; belief; patternCandidate; candidateKey)
import Mimir.CandidateRegistry as Registry
import Mimir.CandidateBatch as Batch

record BeliefValues : Set where
  constructor beliefValues
  field
    identity : ℕ
    content : Text
    project : Maybe Text
    memory : Memory
    created activated : ℤ
    probability confidence alpha beta alpha0 beta0 : Float

record PatternValues : Set where
  constructor patternValues
  field
    identity : ℕ
    situation approach : Text
    project : Maybe Text
    created : ℤ
    activationCount : ℕ
    successRate : Float

data Node : Set where
  beliefNode : BeliefValues → Node
  patternNode : PatternValues → Node

record Creation : Set where
  constructor creation
  field
    experience identity : ℕ
    declaration : Candidate
    project : Text
    timestamp : ℤ

value : Creation → Node
value (creation experience identity (belief name content memory) project timestamp) =
  beliefNode (beliefValues identity content (just project) memory timestamp timestamp 0.5 0.0 1.0 1.0 1.0 1.0)
value (creation experience identity (patternCandidate name situation approach) project timestamp) =
  patternNode (patternValues identity situation approach (just project) timestamp 0 0.5)

nodeID : Node → ℕ
nodeID (beliefNode fields) = BeliefValues.identity fields
nodeID (patternNode fields) = PatternValues.identity fields

nodeProject : Node → Maybe Text
nodeProject (beliefNode fields) = BeliefValues.project fields
nodeProject (patternNode fields) = PatternValues.project fields

identityExact : ∀ command → nodeID (value command) ≡ Creation.identity command
identityExact (creation experience identity (belief name content memory) project timestamp) = refl
identityExact (creation experience identity (patternCandidate name situation approach) project timestamp) = refl

projectExact : ∀ command → nodeProject (value command) ≡ just (Creation.project command)
projectExact (creation experience identity (belief name content memory) project timestamp) = refl
projectExact (creation experience identity (patternCandidate name situation approach) project timestamp) = refl

-- Reused reservations issue no CREATE. A new reservation issues one command
-- with exactly its assigned identity and original declaration.
commands : ∀ {occupied experience before candidates after bindings} → Text → (Candidate → ℤ) →
  Batch.Batch occupied experience before candidates after bindings → List Creation
commands project clock (Batch.done before) = []
commands project clock (Batch.next (Registry.reuse row found valid) remainder) = commands project clock remainder
commands {experience = experience} project clock
  (Batch.next {candidate = declaration} (Registry.create fresh absent unused) remainder) =
  creation experience fresh declaration project (clock declaration) ∷ commands project clock remainder

Linked : Registry.Registry → Creation → Set
Linked after command = Σ Registry.Entry (λ row →
  Registry.lookup (Creation.experience command , candidateKey (Creation.declaration command)) after ≡ just row ×
  Registry.Entry.nodeID row ≡ Creation.identity command × Registry.Entry.declaration row ≡ Creation.declaration command)

allLinked : ∀ {occupied experience before candidates after bindings} project clock
  (batch : Batch.Batch occupied experience before candidates after bindings) →
  All (Linked after) (commands project clock batch)
allLinked project clock (Batch.done before) = []
allLinked project clock (Batch.next (Registry.reuse row found valid) remainder) = allLinked project clock remainder
allLinked {experience = experience} project clock
  (Batch.next {before = before} {candidate = declaration} (Registry.create fresh absent unused) remainder) = (_ ,
     Batch.batchPreserves remainder
     (experience , candidateKey declaration) _
     (Registry.lookupInserted experience declaration fresh before)
     , refl , refl)
    ∷ allLinked project clock remainder

-- A collision with any independently existing graph node is a refusal even
-- if that identity does not yet appear in the candidates SQL table.
allFreshForGraph : ∀ {occupied experience before candidates after bindings} project clock
  (batch : Batch.Batch occupied experience before candidates after bindings) →
  All (λ command → Registry.IDs.Absent (Creation.identity command) occupied) (commands project clock batch)
allFreshForGraph project clock (Batch.done before) = []
allFreshForGraph project clock (Batch.next (Registry.reuse row found valid) remainder) = allFreshForGraph project clock remainder
allFreshForGraph project clock (Batch.next (Registry.create fresh absent unused) remainder) = AllProperties.++⁻ˡ _ unused ∷
  allFreshForGraph project clock remainder

allFreshForRegistry : ∀ {occupied experience before candidates after bindings} project clock
  (batch : Batch.Batch occupied experience before candidates after bindings) →
  All (λ command → Registry.IDs.Absent (Creation.identity command) (map Registry.Entry.nodeID before))
    (commands project clock batch)
allFreshForRegistry project clock (Batch.done before) = []
allFreshForRegistry project clock (Batch.next (Registry.reuse row found valid) remainder) = allFreshForRegistry project clock remainder
allFreshForRegistry project clock (Batch.next (Registry.create fresh absent unused) remainder) = AllProperties.++⁻ʳ _ unused ∷
  All.map (λ { (_ ∷ earlier) → earlier })
  (allFreshForRegistry project clock remainder)

commandsDistinct : ∀ {occupied experience before candidates after bindings} project clock
  (batch : Batch.Batch occupied experience before candidates after bindings) →
  Registry.IDs.Unique (map Creation.identity (commands project clock batch))
commandsDistinct project clock (Batch.done before) = tt
commandsDistinct project clock (Batch.next (Registry.reuse row found valid) remainder) = commandsDistinct project clock remainder
commandsDistinct project clock (Batch.next (Registry.create fresh absent unused) remainder) = AllProperties.map⁺
  (All.map (λ { (different ∷ earlier) same → different (sym same) })
   (allFreshForRegistry project clock remainder))
  , commandsDistinct project clock remainder
