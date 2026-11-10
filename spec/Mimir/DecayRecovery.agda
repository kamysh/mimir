{-# OPTIONS --safe #-}
-- Current counts carry the time they already represent. Registered retries
-- use the original PostgreSQL time, arguments and saved answer.
module Mimir.DecayRecovery where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Float.Base using (Float)
open import Data.Integer using (ℤ)
import Data.Integer as Integer
import Data.Integer.Properties as IntegerProps
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String using (toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Mimir.Text using (Text)
import Mimir.ApplicationStore as Store
import Mimir.CandidateGraph as Graph
import Mimir.EvidenceValidity as Evidence
import Mimir.GraphNumerics as Numeric
import Mimir.GraphRecords as Records
import Mimir.InferenceProtocol as Inference
import Mimir.LearningCandidates as Candidates
import Mimir.PosteriorComputation as Posterior
import Mimir.PublicRequest as Public
import Mimir.RecoverableStoreStep as Step
import Mimir.RegisteredStoreAdmission as Admission
import Mimir.RetrievalRanking as Ranking
import Mimir.StandardLibrary as Conversion
import Mimir.StorageSemantics as Semantics
import Mimir.StructuredValue as Wire
import Mimir.ToolCatalog as Tools
import Mimir.Validation as Validation

record Request : Set where
  constructor request
  field publicationTime : ℤ; factor : Float; project : Maybe Text

-- A different operation token at the same accounted time has no interval
-- left to charge. This follows from the stored baseline, not saved replies.
sameTimeCannotChargeAgain : ∀ now factor mass belief →
  Numeric.decayed now factor mass (Evidence.accounted now belief) ≡ Evidence.current belief
sameTimeCannotChargeAgain now factor mass belief = Numeric.noElapsedInterval now factor mass
  (Evidence.accounted now belief)
  (IntegerProps.≤-trans (Evidence.accountedThroughPublicationTime now belief)
    (subst (λ limit → baseline Integer.≤ limit) (IntegerProps.⊔-comm baseline activation)
      (IntegerProps.i≤i⊔j baseline activation)))
  where
  baseline = Graph.BeliefValues.decayAccountedAt (Evidence.accounted now belief)
  activation = Graph.BeliefValues.activated belief

module Business (databaseSum : List Float → Float) where
  data Diagnostic : Set where
    requestFault : Validation.Fault → Diagnostic
    invalidStoredInputs : Diagnostic
  Outcome = Diagnostic ⊎ (Store.World × Wire.Value)

  selected : Request → Store.World → List Graph.BeliefValues
  selected requested before = Records.listBeliefs (Request.project requested) nothing (Store.beliefs before)

  desiredNode : Request → List (ℕ × Float) → Graph.Node → Graph.Node
  desiredNode requested masses (Graph.patternNode fields) = Graph.patternNode fields
  desiredNode requested masses (Graph.beliefNode belief)
    with Ranking.visible (Request.project requested) (Graph.BeliefValues.project belief)
  ... | false = Graph.beliefNode belief
  ... | true with Graph.BeliefValues.memory belief
  ... | Candidates.experiential = Graph.beliefNode belief
  ... | Candidates.working = Graph.beliefNode belief
  ... | Candidates.fact = Graph.beliefNode (Evidence.accounted (Request.publicationTime requested)
    (Evidence.updated belief (Numeric.decayed (Request.publicationTime requested) (Request.factor requested)
      (Numeric.massOf (Graph.BeliefValues.identity belief) masses) belief)))

  -- Independent desired outcome: update exactly the visible fact beliefs;
  -- all other nodes, priors and every other stored component survive.
  intended : Request → Store.World → Store.World
  intended requested before = Store.setNodes
    (map (desiredNode requested (Semantics.groundTotals databaseSum before)) (Store.nodes before)) before

  calculated : Request → Store.World → Maybe Posterior.State
  calculated requested before = Numeric.decay (Request.publicationTime requested) (Request.factor requested)
    (Semantics.groundTotals databaseSum before) (selected requested before)

  reply : Request → Store.World → Posterior.State → Wire.Value
  reply requested before writes = Wire.object
    ((toList "decayed" , Wire.unsigned (Numeric.changedCount (selected requested before) writes)) ∷ [])

  Goal : Request → Store.World → Outcome → Set
  Goal requested before outcome with calculated requested before
  ... | nothing = outcome ≡ inj₁ invalidStoredInputs
  ... | just writes = outcome ≡ inj₂ (intended requested before , reply requested before writes)

  checked : ∀ requested before → Σ Outcome (Goal requested before)
  checked requested before with calculated requested before
  ... | nothing = inj₁ invalidStoredInputs , refl
  ... | just writes = inj₂ (intended requested before , reply requested before writes) , refl

  journalUnchanged : ∀ requested before after answer → proj₁ (checked requested before) ≡ inj₂ (after , answer) →
    Store.World.operations after ≡ Store.World.operations before
  journalUnchanged requested before after answer accepted with calculated requested before
  ... | nothing with accepted
  ... | ()
  journalUnchanged requested before .(intended requested before) .(reply requested before writes) refl | just writes = refl

module Registered (conversion : Conversion.Contract) (databaseSum : List Float → Float) where
  module B = Business databaseSum
  module PublicDecode = Public.Decode conversion

  descriptor = Admission.descriptor (toList "decay_all") (toList "store.decay_locked")
    (toList "[\"store.decay_locked\",null]")
  key : ℕ → Text
  key _ = Admission.Descriptor.key descriptor
  distinct : ∀ token → key token ≡ Step.resultKey → ⊥
  distinct token ()

  mismatch = Validation.fault [] Validation.malformedInput
    "Read the original decay request and outcome. Correct its declared factor and project fields; retain its original token and settings rather than inventing replacements."

  decode : ℤ → Wire.Value → Validation.Fault ⊎ Request
  decode publicationTime raw with PublicDecode.readBoundTool Tools.decayAll raw
  ... | inj₁ fault = inj₁ fault
  ... | inj₂ (Public.inference (Inference.decay project factor)) = inj₂ (request publicationTime factor project)
  ... | inj₂ _ = inj₁ mismatch

  original : ℕ → Step.Registration → Validation.Fault ⊎ Request
  original token registration with Admission.resolve descriptor token registration
  ... | inj₁ fault = inj₁ fault
  ... | inj₂ (reserved , binding) with Store.BindingRow.settings binding
  ... | Wire.object [] = decode (Store.ReservationRow.reservedAt reserved) (Store.BindingRow.arguments binding)
  ... | _ = inj₁ mismatch

  admit : ℕ → Step.Registration → Maybe B.Diagnostic
  admit token registration with original token registration
  ... | inj₁ fault = just (B.requestFault fault)
  ... | inj₂ _ = nothing

  decide : ℕ → Store.World → B.Outcome
  decide token before with original token (Step.registration before)
  ... | inj₁ fault = inj₁ (B.requestFault fault)
  ... | inj₂ requested = proj₁ (B.checked requested before)

  keepsJournal : ∀ token before after reply → decide token before ≡ inj₂ (after , reply) →
    Store.World.operations after ≡ Store.World.operations before
  keepsJournal token before after reply accepted with original token (Step.registration before)
  ... | inj₁ fault with accepted
  ... | ()
  keepsJournal token before after reply accepted | inj₂ requested = B.journalUnchanged requested before after reply accepted

  module Saved = Step.Admitted ℕ B.Diagnostic (λ token → token) key distinct decide keepsJournal admit

  FreshGoal : ℕ → Request → Store.World → Store.World → Saved.Reply → Set
  FreshGoal token requested before after (Step.done reply) = Σ Store.World (λ changed →
    B.Goal requested before (inj₂ (changed , reply)) × after ≡ Saved.Kernel.publication token changed reply)
  FreshGoal token requested before after (Step.needsInput diagnostic) =
    after ≡ before × B.Goal requested before (inj₁ diagnostic)
  FreshGoal token requested before after _ = ⊥

  originalDecides : ∀ token before requested → original token (Step.registration before) ≡ inj₂ requested →
    decide token before ≡ proj₁ (B.checked requested before)
  originalDecides token before requested bound rewrite bound = refl

  freshMeaning : ∀ token requested before → original token (Step.registration before) ≡ inj₂ requested →
    FreshGoal token requested before (proj₁ (Saved.Kernel.fresh token before)) (proj₂ (Saved.Kernel.fresh token before))
  freshMeaning token requested before bound rewrite originalDecides token before requested bound
    with B.checked requested before
  ... | inj₁ diagnostic , correct = refl , correct
  ... | inj₂ (changed , reply) , correct = changed , correct , refl

  Goal : ℕ → Store.World → Store.World → Saved.Reply → Set
  Goal token before after reply with original token (Step.registration before)
  ... | inj₁ fault = after ≡ before × reply ≡ Step.needsInput (B.requestFault fault)
  ... | inj₂ requested with Store.lookupCancellation before token
  ... | just cancelled = after ≡ before × reply ≡ Step.cancelled cancelled
  ... | nothing with Store.lookupSaved before token (key token) | Store.lookupSaved before token Step.resultKey
  ... | just saved | just _ = after ≡ before × reply ≡ Step.done saved
  ... | just _ | nothing = after ≡ before × reply ≡ Step.needsRecovery
  ... | nothing | just _ = after ≡ before × reply ≡ Step.needsRecovery
  ... | nothing | nothing = FreshGoal token requested before after reply

  meaning : ∀ token before → Goal token before (proj₁ (Saved.execute token before)) (proj₂ (Saved.execute token before))
  meaning token before with original token (Step.registration before) in bound
  ... | inj₁ fault = refl , refl
  ... | inj₂ requested with Store.lookupCancellation before token
  ... | just cancelled = refl , refl
  ... | nothing with Store.lookupSaved before token (key token) | Store.lookupSaved before token Step.resultKey
  ... | just saved | just _ = refl , refl
  ... | just _ | nothing = refl , refl
  ... | nothing | just _ = refl , refl
  ... | nothing | nothing = freshMeaning token requested before bound

  module Certified = Saved.Certified Goal meaning
  operation = Certified.operation
