{-# OPTIONS --safe #-}
-- Standalone propagation returns the changed probabilities, not an edge ack.
module Mimir.PropagationRecovery where

open import Data.Empty using (⊥)
open import Data.Float.Base using (Float)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String using (toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Mimir.Text using (Text)
import Mimir.ApplicationStore as Store
import Mimir.GroundingRecovery as Ground
import Mimir.InferenceStorageBinding as Inference
import Mimir.InferenceProtocol as Protocol
import Mimir.PosteriorComputation as P
import Mimir.PublicEncoding as Encoding
import Mimir.PublicRequest as Public
import Mimir.RecordDecoding as Decode
import Mimir.RecoverableStoreStep as Step
import Mimir.RegisteredStoreAdmission as Admission
import Mimir.StandardLibrary as Conversion
import Mimir.StructuredValue as Wire
import Mimir.ToolCatalog as Tools
import Mimir.Validation as Validation

module Business (format : Encoding.Formatting)
  (databaseSum : List Float → Float) (calculator : P.Calculator) where
  module G = Ground.Business databaseSum calculator
  module N = Inference.NumericalOutcome databaseSum
  module Encode = Encoding.Encode format
  open G public using (Diagnostic; requestFault; preparation)
  Outcome = G.Outcome

  answer : List (ℕ × Float) → Wire.Value
  answer rows = Wire.array (map (λ { (identity , probability) → Encoding.object
    (("id" , Encode.uuid identity) ∷ ("new_probability" , Encode.real probability) ∷ []) }) rows)

  module Selected (publicationTime : ℤ) (selected : N.Context) where
    Goal : Store.World → Outcome → Set
    Goal before (inj₁ diagnostic) = G.Selected.DiagnosticGoal publicationTime selected diagnostic
    Goal before (inj₂ (after , reply)) = Σ (List (ℕ × Float)) (λ numericalReply →
      N.Completed publicationTime selected before after numericalReply × reply ≡ answer numericalReply)

    checked : ∀ before → Σ Outcome (Goal before)
    checked before with G.Selected.checked publicationTime selected before
    ... | inj₁ diagnostic , correct = inj₁ diagnostic , correct
    ... | inj₂ (after , acknowledged) , numericalReply , complete , successful =
      inj₂ (after , answer numericalReply) , numericalReply , complete , refl

    publicationKeepsJournal : ∀ before after reply → Goal before (inj₂ (after , reply)) →
      Store.World.operations after ≡ Store.World.operations before
    publicationKeepsJournal before after reply (numericalReply , complete , successful) =
      G.Selected.publicationKeepsJournal publicationTime selected before after Ground.answer
        (numericalReply , complete , refl)

  Goal : ℤ → ℕ → Store.World → Outcome → Set
  Goal publicationTime identity before outcome with N.prepare (N.propagate identity) before
  ... | inj₁ issue = outcome ≡ inj₁ (preparation issue)
  ... | inj₂ selected = Selected.Goal publicationTime selected before outcome

  checked : ∀ publicationTime identity before → Σ Outcome (Goal publicationTime identity before)
  checked publicationTime identity before with N.prepare (N.propagate identity) before
  ... | inj₁ issue = inj₁ (preparation issue) , refl
  ... | inj₂ selected = Selected.checked publicationTime selected before

  journalUnchanged : ∀ publicationTime identity before after reply →
    proj₁ (checked publicationTime identity before) ≡ inj₂ (after , reply) →
    Store.World.operations after ≡ Store.World.operations before
  journalUnchanged publicationTime identity before after reply accepted with N.prepare (N.propagate identity) before
  ... | inj₁ issue with accepted
  ... | ()
  journalUnchanged publicationTime identity before after reply accepted | inj₂ selected =
    Selected.publicationKeepsJournal publicationTime selected before after reply
      (subst (Selected.Goal publicationTime selected before) accepted
        (proj₂ (Selected.checked publicationTime selected before)))

module Registered (format : Encoding.Formatting) (conversion : Conversion.Contract)
  (databaseSum : List Float → Float) (calculator : P.Calculator)
  (serverTime : ℕ → Store.World → ℤ) where
  module B = Business format databaseSum calculator
  module PublicDecode = Public.Decode conversion

  descriptor : Admission.Descriptor
  descriptor = Admission.descriptor (toList "propagate_from") (toList "store.propagate_locked")
    (toList "[\"store.propagate_locked\",null]")

  key : ℕ → Text
  key _ = Admission.Descriptor.key descriptor

  distinct : ∀ token → key token ≡ Step.resultKey → ⊥
  distinct token ()

  mismatch : Validation.Fault
  mismatch = Validation.fault [] Validation.malformedInput
    "Read the original propagation request and outcome before continuing. Correct its exact declared fields; do not replace its arguments or settings."

  request : Wire.Value → Validation.Fault ⊎ ℕ
  request raw with PublicDecode.readBoundTool Tools.propagateFrom raw
  ... | inj₁ fault = inj₁ fault
  ... | inj₂ (Public.inference (Protocol.propagate identity)) = inj₂ identity
  ... | inj₂ _ = inj₁ mismatch

  original : ℕ → Step.Registration → Validation.Fault ⊎ (ℕ × ℤ)
  original token registration with Admission.resolve descriptor token registration
  ... | inj₁ fault = inj₁ fault
  ... | inj₂ (reserved , binding) with Store.BindingRow.settings binding
  ... | Wire.object [] = Decode.mapResult (λ requested → requested , Store.ReservationRow.reservedAt reserved)
    (request (Store.BindingRow.arguments binding))
  ... | _ = inj₁ mismatch

  admit : ℕ → Step.Registration → Maybe B.Diagnostic
  admit token registration with original token registration
  ... | inj₁ fault = just (B.requestFault fault)
  ... | inj₂ _ = nothing

  module AtReceipt (observedTime : ℤ) where
    decide : ℕ → Store.World → B.Outcome
    decide token before with original token (Step.registration before)
    ... | inj₁ fault = inj₁ (B.requestFault fault)
    ... | inj₂ (requested , publicationTime) = proj₁ (B.checked observedTime requested before)

    keepsJournal : ∀ token before after reply → decide token before ≡ inj₂ (after , reply) →
      Store.World.operations after ≡ Store.World.operations before
    keepsJournal token before after reply accepted with original token (Step.registration before)
    ... | inj₁ fault with accepted
    ... | ()
    keepsJournal token before after reply accepted | inj₂ (requested , publicationTime) = B.journalUnchanged observedTime requested before after reply accepted

    module Saved = Step.Admitted ℕ B.Diagnostic (λ token → token) key distinct decide keepsJournal admit

    FreshGoal : ℕ → ℕ → ℤ → Store.World → Store.World → Saved.Reply → Set
    FreshGoal token requested publicationTime before after (Step.done reply) = Σ Store.World (λ changed →
      B.Goal publicationTime requested before (inj₂ (changed , reply)) × after ≡ Saved.Kernel.publication token changed reply)
    FreshGoal token requested publicationTime before after (Step.needsInput diagnostic) =
      after ≡ before × B.Goal publicationTime requested before (inj₁ diagnostic)
    FreshGoal token requested publicationTime before after _ = ⊥

    originalDecides : ∀ token before requested publicationTime → original token (Step.registration before) ≡ inj₂ (requested , publicationTime) →
      decide token before ≡ proj₁ (B.checked observedTime requested before)
    originalDecides token before requested publicationTime bound rewrite bound = refl

    freshMeaning : ∀ token requested publicationTime before → original token (Step.registration before) ≡ inj₂ (requested , publicationTime) →
      FreshGoal token requested observedTime before (proj₁ (Saved.Kernel.fresh token before)) (proj₂ (Saved.Kernel.fresh token before))
    freshMeaning token requested publicationTime before bound rewrite originalDecides token before requested publicationTime bound
      with B.checked observedTime requested before
    ... | inj₁ diagnostic , correct = refl , correct
    ... | inj₂ (changed , reply) , correct = changed , correct , refl

    Goal : ℕ → Store.World → Store.World → Saved.Reply → Set
    Goal token before after reply with original token (Step.registration before)
    ... | inj₁ fault = after ≡ before × reply ≡ Step.needsInput (B.requestFault fault)
    ... | inj₂ (requested , publicationTime) with Store.lookupCancellation before token
    ... | just cancelled = after ≡ before × reply ≡ Step.cancelled cancelled
    ... | nothing with Store.lookupSaved before token (key token) | Store.lookupSaved before token Step.resultKey
    ... | just saved | just _ = after ≡ before × reply ≡ Step.done saved
    ... | just _ | nothing = after ≡ before × reply ≡ Step.needsRecovery
    ... | nothing | just _ = after ≡ before × reply ≡ Step.needsRecovery
    ... | nothing | nothing = FreshGoal token requested observedTime before after reply

    meaning : ∀ token before → Goal token before (proj₁ (Saved.execute token before)) (proj₂ (Saved.execute token before))
    meaning token before with original token (Step.registration before) in bound
    ... | inj₁ fault = refl , refl
    ... | inj₂ (requested , publicationTime) with Store.lookupCancellation before token
    ... | just cancelled = refl , refl
    ... | nothing with Store.lookupSaved before token (key token) | Store.lookupSaved before token Step.resultKey
    ... | just saved | just _ = refl , refl
    ... | just _ | nothing = refl , refl
    ... | nothing | just _ = refl , refl
    ... | nothing | nothing = freshMeaning token requested publicationTime before bound


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
  interruptedKeepsCancellation = Run.interruptedKeepsCancellation
  progress = Run.progress
  everyDatabaseReceiptCovered = Run.everyDatabaseReceiptCovered
  module X = Run.X
  module E = Run.E
  module Saved = Run.Saved
  Goal = Certified.Goal
  operation = Certified.operation
