{-# OPTIONS --safe #-}
-- Evidence intent includes its complete posterior consequences. A saved
-- addition is replayed without creating another contribution.
module Mimir.GroundingRecovery where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Float.Base using (Float)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String using (toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Mimir.Text using (Text)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Mimir.ApplicationStore as Store
import Mimir.GroundingPublication as Ground
import Mimir.GraphNumerics as Numeric
import Mimir.InferenceStorageBinding as Inference
import Mimir.PosteriorComputation as P
import Mimir.RecoverableStoreStep as Step
import Mimir.RetrievalRanking as Ranking
import Mimir.StructuredValue as Wire
import Mimir.Validation as Validation
import Mimir.RegisteredStoreAdmission as Admission
import Mimir.PublicInput as Input
import Mimir.PublicRequest as Public
import Mimir.ToolCatalog as Tools
import Mimir.RecordDecoding as Decode
import Mimir.JsonObjects as Objects
import Mimir.StandardLibrary as Conversion

answer : Wire.Value
answer = Wire.object ((toList "ok" , Wire.boolean true) ∷ [])

root : Ground.Request → ℕ
root (Ground.add chunk belief weight) = belief
root (Ground.remove chunk belief) = belief

-- The requested evidence contribution is independent of SQL and of the
-- numerical solver. Removing a pair removes all its existing contributions.
intendedEvidence : Ground.Request → Store.World → Validation.Fault ⊎ Store.World
intendedEvidence (Ground.remove chunk belief) before = inj₂ (Ground.unlink chunk belief before)
intendedEvidence (Ground.add chunk belief weight) before with Numeric.probability weight
... | false = inj₁ (Validation.fault (Validation.key "weight" ∷ []) Validation.invalidNumber
  "Supply a finite evidence weight between 0 and 1 inclusive. Correct the original request; do not clamp or guess a replacement.")
... | true with Store.chunk chunk (Store.World.chunks before) | Ranking.lookup belief (Store.beliefs before)
... | nothing | _ = inj₁ (Validation.fault (Validation.key "chunk_id" ∷ []) Validation.malformedInput
  "The requested passage is not indexed. Use query_document or list_documents to find the intended passage. Ask the user whether to index a missing document; do not invent an identifier.")
... | just _ | nothing = inj₁ (Validation.fault (Validation.key "belief_id" ∷ []) Validation.malformedInput
  "The requested belief is absent. Use list_beliefs or query_relevant to find the intended belief. If its identity is unknown, ask the user; do not invent an identifier.")
... | just _ | just _ = inj₂ (record before
  { grounds = Store.World.grounds before ++ (Store.ground chunk belief weight ∷ []) })

intendedKeepsJournal : ∀ request before after → intendedEvidence request before ≡ inj₂ after →
  Store.World.operations after ≡ Store.World.operations before
intendedKeepsJournal (Ground.remove chunk belief) before .(Ground.unlink chunk belief before) refl = refl
intendedKeepsJournal (Ground.add chunk belief weight) before after observed with Numeric.probability weight
... | false with observed
... | ()
intendedKeepsJournal (Ground.add chunk belief weight) before after observed | true
  with Store.chunk chunk (Store.World.chunks before) | Ranking.lookup belief (Store.beliefs before)
... | nothing | _ with observed
... | ()
intendedKeepsJournal (Ground.add chunk belief weight) before after observed | true | just _ | nothing with observed
... | ()
intendedKeepsJournal (Ground.add chunk belief weight) before after observed | true | just _ | just _ with observed
... | refl = refl

module Business (databaseSum : List Float → Float) (calculator : P.Calculator) where
  module N = Inference.NumericalOutcome databaseSum

  data Diagnostic : Set where
    requestFault : Validation.Fault → Diagnostic
    preparation : N.PreparationIssue → Diagnostic
    rejectedReport : P.CalculationReport → Diagnostic
    repeated : P.State → List P.State → Diagnostic

  Outcome = Diagnostic ⊎ (Store.World × Wire.Value)

  module Selected (selected : N.Context) where
    open N.Context selected
    module A = P.Assess seed external edges targets
    module C = N.Cycle selected edges

    DiagnosticGoal : Diagnostic → Set
    DiagnosticGoal (rejectedReport report) = A.check report ≡ A.rejected
    DiagnosticGoal (repeated final visited) = C.Repeated final visited
    DiagnosticGoal _ = ⊥

    Goal : Store.World → Outcome → Set
    Goal before (inj₁ diagnostic) = DiagnosticGoal diagnostic
    Goal before (inj₂ (after , reply)) = Σ (List (ℕ × Float)) (λ numericalReply →
      N.Completed selected before after numericalReply × reply ≡ answer)

    report = calculator seed external edges targets

    checked : ∀ before → Σ Outcome (Goal before)
    checked before with A.check report in assessed
    ... | A.rejected = inj₁ (rejectedReport report) , assessed
    ... | A.accepted counts valid shape complete =
      inj₂ (N.proposed selected before counts , answer) ,
      Numeric.project (N.writes selected counts) ,
      (edges , Perm.↭-refl , counts , valid , shape , complete , refl , refl) , refl
    ... | A.repeated final visited seen incomplete runs =
      inj₁ (repeated final visited) , seen , incomplete , runs

    publicationKeepsJournal : ∀ before after reply → Goal before (inj₂ (after , reply)) →
      Store.World.operations after ≡ Store.World.operations before
    publicationKeepsJournal before after reply
      (numericalReply , (incoming , permutation , counts , valid , shape , complete , framed , answered) , successful)
      rewrite framed with readOnly
    ... | true = refl
    ... | false = refl

  Goal : Ground.Request → Store.World → Outcome → Set
  Goal request before outcome with intendedEvidence request before
  ... | inj₁ fault = outcome ≡ inj₁ (requestFault fault)
  ... | inj₂ proposed with N.prepare (N.recompute (root request ∷ [])) proposed
  ... | inj₁ issue = outcome ≡ inj₁ (preparation issue)
  ... | inj₂ selected = Selected.Goal selected proposed outcome

  checked : ∀ request before → Σ Outcome (Goal request before)
  checked request before with intendedEvidence request before
  ... | inj₁ fault = inj₁ (requestFault fault) , refl
  ... | inj₂ proposed with N.prepare (N.recompute (root request ∷ [])) proposed
  ... | inj₁ issue = inj₁ (preparation issue) , refl
  ... | inj₂ selected = Selected.checked selected proposed

  publicationKeepsJournal : ∀ request before after reply → Goal request before (inj₂ (after , reply)) →
    Store.World.operations after ≡ Store.World.operations before
  publicationKeepsJournal request before after reply correct with intendedEvidence request before in intended
  ... | inj₁ fault with correct
  ... | ()
  publicationKeepsJournal request before after reply correct | inj₂ proposed
    with N.prepare (N.recompute (root request ∷ [])) proposed
  ... | inj₁ issue with correct
  ... | ()
  publicationKeepsJournal request before after reply correct | inj₂ proposed | inj₂ selected =
    Relation.Binary.PropositionalEquality.trans
      (Selected.publicationKeepsJournal selected proposed after reply correct)
      (intendedKeepsJournal request before proposed intended)

  journalUnchanged : ∀ request before after reply → proj₁ (checked request before) ≡ inj₂ (after , reply) →
    Store.World.operations after ≡ Store.World.operations before
  journalUnchanged request before after reply accepted = publicationKeepsJournal request before after reply
    (subst (Goal request before) accepted (proj₂ (checked request before)))

data Kind : Set where addition removal : Kind

descriptorFor : Kind → Admission.Descriptor
descriptorFor addition = Admission.descriptor (toList "add_evidence") (toList "store.insert_evidence")
  (toList "[\"store.insert_evidence\",null]")
descriptorFor removal = Admission.descriptor (toList "delete_evidence") (toList "store.delete_evidence")
  (toList "[\"store.delete_evidence\",null]")

distinctFor : ∀ kind → Admission.Descriptor.key (descriptorFor kind) ≡ Step.resultKey → ⊥
distinctFor addition ()
distinctFor removal ()

module Registered (kind : Kind) (conversion : Conversion.Contract)
  (databaseSum : List Float → Float) (calculator : P.Calculator) where
  module B = Business databaseSum calculator
  module PublicDecode = Public.Decode conversion

  descriptor : Admission.Descriptor
  descriptor = descriptorFor kind

  key : ℕ → Text
  key _ = Admission.Descriptor.key descriptor

  distinct : ∀ token → key token ≡ Step.resultKey → ⊥
  distinct token = distinctFor kind

  mismatch : Validation.Fault
  mismatch = Validation.fault [] Validation.malformedInput
    "Read the original evidence request and outcome before continuing. Correct its exact declared fields; do not replace its arguments or settings."

  requestFor : Kind → Wire.Value → Validation.Fault ⊎ Ground.Request
  requestFor addition raw with PublicDecode.readTool Tools.addEvidence raw
  ... | inj₁ fault = inj₁ fault
  ... | inj₂ (Public.addEvidence belief chunk weight) = inj₂ (Ground.add chunk belief weight)
  ... | inj₂ _ = inj₁ mismatch
  requestFor removal raw = Decode.readRecord Objects.forbid Objects.rejectKnownRepeated
    (toList "belief_id" ∷ toList "chunk_id" ∷ [])
    (λ fields → Input.required "belief_id" (Input.readUUID conversion) fields Decode.>>= λ belief →
      Input.required "chunk_id" (Input.readUUID conversion) fields Decode.>>= λ chunk → inj₂ (Ground.remove chunk belief)) raw

  request : Wire.Value → Validation.Fault ⊎ Ground.Request
  request = requestFor kind

  original : ℕ → Step.Registration → Validation.Fault ⊎ Ground.Request
  original token registration with Admission.resolve descriptor token registration
  ... | inj₁ fault = inj₁ fault
  ... | inj₂ (reserved , binding) with Store.BindingRow.settings binding
  ... | Wire.object [] = request (Store.BindingRow.arguments binding)
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

  FreshGoal : ℕ → Ground.Request → Store.World → Store.World → Saved.Reply → Set
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
