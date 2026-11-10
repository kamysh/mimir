{-# OPTIONS --safe #-}
-- The deletion goal keeps the complete store and requires every affected
-- posterior equation. Raw calculator output is checked before publication.
module Mimir.BeliefDeletionRecovery where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.Float.Base using (Float)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.Integer using (ℤ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String using (toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Mimir.Text using (Text)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Mimir.ApplicationStore as Store
import Mimir.GraphDeletion as Delete
import Mimir.GraphNumerics as Numeric
import Mimir.InferenceStorageBinding as Inference
import Mimir.PosteriorComputation as P
import Mimir.RecoverableStoreStep as Step
import Mimir.StructuredValue as Wire
import Mimir.Validation as Validation
import Mimir.RegisteredStoreAdmission as Admission
import Mimir.PublicInput as Input
import Mimir.RecordDecoding as Decode
import Mimir.JsonObjects as Objects
import Mimir.StandardLibrary as Conversion

answer : Data.Bool.Bool → Wire.Value
answer deleted = Wire.object ((toList "deleted" , Wire.boolean deleted) ∷ [])

erased : ℕ → Store.World → Store.World
erased identity before = Store.removeBeliefVectors (identity ∷ [])
  (Store.removeNodes (identity ∷ []) true before)

module Business (databaseSum : List Float → Float) (calculator : P.Calculator) where
  module N = Inference.NumericalOutcome databaseSum

  data Diagnostic : Set where
    requestFault : Validation.Fault → Diagnostic
    preparation : N.PreparationIssue → Diagnostic
    rejectedReport : P.CalculationReport → Diagnostic
    repeated : P.State → List P.State → Diagnostic

  Outcome = Diagnostic ⊎ (Store.World × Wire.Value)

  module Selected (publicationTime : ℤ) (selected : N.Context) where
    open N.Context selected
    module A = P.Assess seed external edges targets
    module C = N.Cycle selected edges

    -- Refusal has no business publication. A repeated state must be backed by
    -- the actual replay of the calculation, not an arbitrary pass allowance.
    DiagnosticGoal : Diagnostic → Set
    DiagnosticGoal (rejectedReport report) = A.check report ≡ A.rejected
    DiagnosticGoal (repeated final visited) = C.Repeated final visited
    DiagnosticGoal _ = ⊥

    Goal : Store.World → Outcome → Set
    Goal before (inj₁ diagnostic) = DiagnosticGoal diagnostic
    Goal before (inj₂ (after , reply)) = Σ (List (ℕ × Float)) (λ numericalReply →
      N.Completed publicationTime selected before after numericalReply × reply ≡ answer true)

    report : P.CalculationReport
    report = calculator seed external edges targets

    checked : ∀ before → Σ Outcome (Goal before)
    checked before with A.check report in assessed
    ... | A.rejected = inj₁ (rejectedReport report) , assessed
    ... | A.accepted counts valid shape complete =
      inj₂ (N.proposed publicationTime selected before counts , answer true) ,
      Numeric.project (N.writes selected counts) ,
      (edges , Perm.↭-refl , counts , valid , shape , complete , refl , refl) , refl
    ... | A.repeated final visited seen incomplete runs =
      inj₁ (repeated final visited) , seen , incomplete , runs

    publicationKeepsJournal : ∀ before after reply → Goal before (inj₂ (after , reply)) →
      Store.World.operations after ≡ Store.World.operations before
    publicationKeepsJournal before after reply
      (numericalReply , (incoming , permutation , counts , valid , shape , complete , framed , answered) , deleted)
      rewrite framed with readOnly
    ... | true = refl
    ... | false = refl

  -- This meaning comes from the initial world, not from runGlobal or a list
  -- of SQL statements. Unrelated records remain in the world equality.
  Goal : ℤ → ℕ → Store.World → Outcome → Set
  Goal publicationTime identity before outcome with Delete.exists Delete.belief identity before
  ... | false with outcome
  ... | inj₁ _ = ⊥
  ... | inj₂ (after , reply) = after ≡ before × reply ≡ answer false
  Goal publicationTime identity before outcome | true with N.prepare (N.recompute (Delete.children identity before)) (erased identity before)
  ... | inj₁ issue = outcome ≡ inj₁ (preparation issue)
  ... | inj₂ selected = Selected.Goal publicationTime selected (erased identity before) outcome

  checked : ∀ publicationTime identity before → Σ Outcome (Goal publicationTime identity before)
  checked publicationTime identity before with Delete.exists Delete.belief identity before
  ... | false = inj₂ (before , answer false) , refl , refl
  ... | true with N.prepare (N.recompute (Delete.children identity before)) (erased identity before)
  ... | inj₁ issue = inj₁ (preparation issue) , refl
  ... | inj₂ selected = Selected.checked publicationTime selected (erased identity before)

  publicationKeepsJournal : ∀ publicationTime identity before after reply → Goal publicationTime identity before (inj₂ (after , reply)) →
    Store.World.operations after ≡ Store.World.operations before
  publicationKeepsJournal publicationTime identity before after reply correct with Delete.exists Delete.belief identity before
  ... | false with correct
  ... | refl , answered = refl
  publicationKeepsJournal publicationTime identity before after reply correct | true
    with N.prepare (N.recompute (Delete.children identity before)) (erased identity before)
  ... | inj₁ issue with correct
  ... | ()
  publicationKeepsJournal publicationTime identity before after reply correct | true | inj₂ selected =
    Selected.publicationKeepsJournal publicationTime selected (erased identity before) after reply correct

  journalUnchanged : ∀ publicationTime identity before after reply → proj₁ (checked publicationTime identity before) ≡ inj₂ (after , reply) →
    Store.World.operations after ≡ Store.World.operations before
  journalUnchanged publicationTime identity before after reply accepted = publicationKeepsJournal publicationTime identity before after reply
    (subst (Goal publicationTime identity before) accepted (proj₂ (checked publicationTime identity before)))

module Registered (conversion : Conversion.Contract)
  (databaseSum : List Float → Float) (calculator : P.Calculator)
  (serverTime : ℕ → Store.World → ℤ) where
  module B = Business databaseSum calculator

  descriptor : Admission.Descriptor
  descriptor = Admission.descriptor (toList "delete_belief") (toList "store.delete_belief")
    (toList "[\"store.delete_belief\",null]")

  key : ℕ → Text
  key _ = Admission.Descriptor.key descriptor

  distinct : ∀ token → key token ≡ Step.resultKey → ⊥
  distinct token ()

  -- This is the same required UUID decoder and strict object-field policy as
  -- the public delete_belief request. The original stored request supplies it.
  original : ℕ → Step.Registration → Validation.Fault ⊎ (ℕ × ℤ)
  original token registration with Admission.resolve descriptor token registration
  ... | inj₁ fault = inj₁ fault
  ... | inj₂ (reserved , binding) with Store.BindingRow.settings binding
  ... | Wire.object [] = Decode.mapResult (λ identity → identity , Store.ReservationRow.reservedAt reserved)
    (Decode.readRecord Objects.forbid Objects.rejectKnownRepeated
    (toList "id" ∷ []) (λ view → Input.required "id" (Input.readUUID conversion) view)
    (Store.BindingRow.arguments binding))
  ... | _ = inj₁ (Validation.fault (Validation.key "settings" ∷ []) Validation.unknownField
    "delete_belief has no per-request settings. Read the original binding and outcome; resolve this token with the user rather than replacing its settings.")

  admit : ℕ → Step.Registration → Data.Maybe.Maybe B.Diagnostic
  admit token registration with original token registration
  ... | inj₁ fault = just (B.requestFault fault)
  ... | inj₂ _ = nothing

  module AtReceipt (observedTime : ℤ) where
    decide : ℕ → Store.World → B.Outcome
    decide token before with original token (Step.registration before)
    ... | inj₁ fault = inj₁ (B.requestFault fault)
    ... | inj₂ (identity , publicationTime) = proj₁ (B.checked observedTime identity before)

    keepsJournal : ∀ token before after reply → decide token before ≡ inj₂ (after , reply) →
      Store.World.operations after ≡ Store.World.operations before
    keepsJournal token before after reply accepted with original token (Step.registration before)
    ... | inj₁ fault with accepted
    ... | ()
    keepsJournal token before after reply accepted | inj₂ (identity , publicationTime) =
      B.journalUnchanged observedTime identity before after reply accepted

    module Saved = Step.Admitted ℕ B.Diagnostic (λ token → token) key distinct decide keepsJournal admit

    -- Publication adds both immutable original answers to the complete world
    -- whose independent business condition was established above.
    FreshGoal : ℕ → ℕ → ℤ → Store.World → Store.World → Saved.Reply → Set
    FreshGoal token identity publicationTime before after (Step.done reply) = Σ Store.World (λ changed →
      B.Goal publicationTime identity before (inj₂ (changed , reply)) × after ≡ Saved.Kernel.publication token changed reply)
    FreshGoal token identity publicationTime before after (Step.needsInput diagnostic) =
      after ≡ before × B.Goal publicationTime identity before (inj₁ diagnostic)
    FreshGoal token identity publicationTime before after _ = ⊥

    originalDecides : ∀ token before identity publicationTime → original token (Step.registration before) ≡ inj₂ (identity , publicationTime) →
      decide token before ≡ proj₁ (B.checked observedTime identity before)
    originalDecides token before identity publicationTime bound rewrite bound = refl

    freshMeaning : ∀ token identity publicationTime before → original token (Step.registration before) ≡ inj₂ (identity , publicationTime) →
      FreshGoal token identity observedTime before (proj₁ (Saved.Kernel.fresh token before)) (proj₂ (Saved.Kernel.fresh token before))
    freshMeaning token identity publicationTime before bound rewrite originalDecides token before identity publicationTime bound
      with B.checked observedTime identity before
    ... | inj₁ diagnostic , correct = refl , correct
    ... | inj₂ (changed , reply) , correct = changed , correct , refl

    Goal : ℕ → Store.World → Store.World → Saved.Reply → Set
    Goal token before after reply with original token (Step.registration before)
    ... | inj₁ fault = after ≡ before × reply ≡ Step.needsInput (B.requestFault fault)
    ... | inj₂ (identity , publicationTime) with Store.lookupCancellation before token
    ... | just cancelled = after ≡ before × reply ≡ Step.cancelled cancelled
    ... | nothing with Store.lookupSaved before token (key token) | Store.lookupSaved before token Step.resultKey
    ... | just saved | just _ = after ≡ before × reply ≡ Step.done saved
    ... | just _ | nothing = after ≡ before × reply ≡ Step.needsRecovery
    ... | nothing | just _ = after ≡ before × reply ≡ Step.needsRecovery
    ... | nothing | nothing = FreshGoal token identity observedTime before after reply

    meaning : ∀ token before → Goal token before (proj₁ (Saved.execute token before)) (proj₂ (Saved.execute token before))
    meaning token before with original token (Step.registration before) in bound
    ... | inj₁ fault = refl , refl
    ... | inj₂ (identity , publicationTime) with Store.lookupCancellation before token
    ... | just cancelled = refl , refl
    ... | nothing with Store.lookupSaved before token (key token) | Store.lookupSaved before token Step.resultKey
    ... | just saved | just _ = refl , refl
    ... | just _ | nothing = refl , refl
    ... | nothing | just _ = refl , refl
    ... | nothing | nothing = freshMeaning token identity publicationTime before bound


  Internal = ℕ × ℤ
  decide : Internal → Store.World → B.Outcome
  decide (token , time) = AtReceipt.decide time token
  keepsJournal : ∀ input before after reply → decide input before ≡ inj₂ (after , reply) →
    Store.World.operations after ≡ Store.World.operations before
  keepsJournal (token , time) = AtReceipt.keepsJournal time token

  module Run = Step.Observed ℤ B.Diagnostic key distinct
    (λ token time → AtReceipt.decide time token)
    (λ token time → AtReceipt.keepsJournal time token) admit serverTime

  receiptMatches : ∀ token time before →
    Run.Saved.execute (token , time) before ≡ AtReceipt.Saved.execute time token before
  receiptMatches token time before with admit token (Step.registration before)
  ... | just _ = refl
  ... | nothing with Store.lookupCancellation before token
  ... | just _ = refl
  ... | nothing with Store.lookupSaved before token (key token) | Store.lookupSaved before token Step.resultKey
  ... | just _ | just _ = refl
  ... | just _ | nothing = refl
  ... | nothing | just _ = refl
  ... | nothing | nothing with AtReceipt.decide time token before
  ... | inj₁ _ = refl
  ... | inj₂ _ = refl

  receiptMeaning : ∀ token time before → AtReceipt.Goal time token before
    (proj₁ (Run.Saved.execute (token , time) before)) (proj₂ (Run.Saved.execute (token , time) before))
  receiptMeaning token time before = subst
    (λ outcome → AtReceipt.Goal time token before (proj₁ outcome) (proj₂ outcome))
    (Relation.Binary.PropositionalEquality.sym (receiptMatches token time before)) (AtReceipt.meaning time token before)

  module Certified = Run.Certified (λ token time → AtReceipt.Goal time token)
    receiptMeaning
  Effect = Run.Effect
  Reply = Run.Reply
  Atomic = Run.Atomic
  script = Run.script
  completedObservation = Run.completedObservation
  interruptionState = Run.interruptionState
  interruptedKeepsRegistration = Run.interruptedKeepsRegistration
  progress = Run.progress
  everyDatabaseReceiptCovered = Run.everyDatabaseReceiptCovered
  module X = Run.X
  module E = Run.E
  module Saved = Run.Saved
  Goal = Certified.Goal
  operation = Certified.operation
  cachedReplay = Run.cachedReplay
