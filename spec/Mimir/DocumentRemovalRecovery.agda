{-# OPTIONS --safe #-}
-- Removing an indexed document also removes its evidence contributions and
-- recomputes every affected surviving belief, in the same publication.
module Mimir.DocumentRemovalRecovery where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.Float.Base using (Float)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_; map; filterᵇ; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String using (toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Mimir.Text using (Text)
import Mimir.ApplicationStore as Store
import Mimir.DocumentPublication as Documents
import Mimir.GroundingRecovery as Ground
import Mimir.InferenceStorageBinding as Inference
import Mimir.PosteriorComputation as P
import Mimir.RetrievalRanking as Ranking
import Mimir.StructuredValue as Wire
import Mimir.JsonObjects as Objects
import Mimir.PublicInput as Input
import Mimir.PublicRequest as Public
import Mimir.RecordDecoding as Decode
import Mimir.RecoverableStoreStep as Step
import Mimir.RegisteredStoreAdmission as Admission
import Mimir.StandardLibrary as Conversion
import Mimir.ToolCatalog as Tools
import Mimir.Validation as Validation

module D = Documents.Publication 0

-- This is an outcome on the complete world, independent of SQL order.
-- removeChunks also detaches every GROUNDS contribution from those chunks.
intendedRemoval : Text → Store.World → Store.World
intendedRemoval = D.clear

affected : Text → Store.World → List ℕ
affected path before = Ranking.unique (map Store.Ground.belief
  (filterᵇ (λ ground → Ranking.member (Store.Ground.chunk ground) ids)
    (Store.World.grounds before)))
  where ids = Store.documentIDs path before

answer : Text → Store.World → Wire.Value
answer path before = Wire.object ((toList "cleared" , Wire.unsigned (length (Store.documentIDs path before))) ∷ [])

module Business (databaseSum : List Float → Float) (calculator : P.Calculator) where
  module G = Ground.Business databaseSum calculator
  module N = Inference.NumericalOutcome databaseSum
  Outcome = G.Diagnostic ⊎ (Store.World × Wire.Value)

  module Selected (publicationTime : ℤ) (path : Text) (before : Store.World) (selected : N.Context) where
    module Checked = G.Selected publicationTime selected

    -- The numerical certificate is reused. Only this operation's public
    -- answer differs: its original number of removed chunks is retained.
    Goal : Outcome → Set
    Goal (inj₁ diagnostic) = Checked.DiagnosticGoal diagnostic
    Goal (inj₂ (after , reply)) = Σ (List (ℕ × Float)) (λ numericalReply →
      N.Completed publicationTime selected (intendedRemoval path before) after numericalReply ×
      reply ≡ answer path before)

    checked : Σ Outcome Goal
    checked with Checked.checked (intendedRemoval path before)
    ... | inj₁ diagnostic , correct = inj₁ diagnostic , correct
    ... | inj₂ (after , oldReply) , numericalReply , completed , replied =
      inj₂ (after , answer path before) , numericalReply , completed , refl

    keepsJournal : ∀ after reply → Goal (inj₂ (after , reply)) →
      Store.World.operations after ≡ Store.World.operations before
    keepsJournal after reply
      (numericalReply , (incoming , permutation , counts , valid , shape , complete , framed , answered) , replied)
      rewrite framed with N.Context.readOnly selected
    ... | true = refl
    ... | false = refl

  Goal : ℤ → Text → Store.World → Outcome → Set
  Goal publicationTime path before outcome with N.prepare (N.recompute (affected path before)) (intendedRemoval path before)
  ... | inj₁ issue = outcome ≡ inj₁ (G.preparation issue)
  ... | inj₂ selected = Selected.Goal publicationTime path before selected outcome

  checked : ∀ publicationTime path before → Σ Outcome (Goal publicationTime path before)
  checked publicationTime path before with N.prepare (N.recompute (affected path before)) (intendedRemoval path before)
  ... | inj₁ issue = inj₁ (G.preparation issue) , refl
  ... | inj₂ selected = Selected.checked publicationTime path before selected

  publicationKeepsJournal : ∀ publicationTime path before after reply →
    Goal publicationTime path before (inj₂ (after , reply)) →
    Store.World.operations after ≡ Store.World.operations before
  publicationKeepsJournal publicationTime path before after reply correct
    with N.prepare (N.recompute (affected path before)) (intendedRemoval path before)
  ... | inj₁ issue with correct
  ... | ()
  publicationKeepsJournal publicationTime path before after reply correct | inj₂ selected =
    Selected.keepsJournal publicationTime path before selected after reply correct

  journalUnchanged : ∀ publicationTime path before after reply →
    proj₁ (checked publicationTime path before) ≡ inj₂ (after , reply) →
    Store.World.operations after ≡ Store.World.operations before
  journalUnchanged publicationTime path before after reply accepted =
    publicationKeepsJournal publicationTime path before after reply
      (subst (Goal publicationTime path before) accepted (proj₂ (checked publicationTime path before)))

-- Admission retains the original request and the server's filesystem
-- preparation result separately. A retry never resolves the path afresh.
-- The existing canonicalize dependency supplies this preparation; no path
-- parser or filesystem-normalization theorem is invented here.
module Registered (conversion : Conversion.Contract)
  (databaseSum : List Float → Float) (calculator : P.Calculator)
  (serverTime : ℕ → Store.World → ℤ) where
  module B = Business databaseSum calculator
  module PublicDecode = Public.Decode conversion

  descriptor : Admission.Descriptor
  descriptor = Admission.descriptor (toList "clear_document") (toList "store.clear_document")
    (toList "[\"store.clear_document\",null]")

  key : ℕ → Text
  key _ = Admission.Descriptor.key descriptor

  distinct : ∀ token → key token ≡ Step.resultKey → ⊥
  distinct token ()

  mismatch : Validation.Fault
  mismatch = Validation.fault [] Validation.malformedInput
    "Read the original document-removal request, its prepared path and its outcome. If its bound request or server preparation is invalid, ask the user whether to cancel this unfinished token and reserve corrected work. Do not guess a path or replace this token's arguments."

  request : Wire.Value → Validation.Fault ⊎ Text
  request raw with PublicDecode.readBoundTool Tools.clearDocument raw
  ... | inj₁ fault = inj₁ fault
  ... | inj₂ (Public.clearDocument path) = inj₂ path
  ... | inj₂ _ = inj₁ mismatch

  prepared : Wire.Value → Validation.Fault ⊎ Text
  prepared = Decode.readRecord Objects.forbid Objects.rejectKnownRepeated
    (toList "resolved_path" ∷ [])
    (λ fields → Input.required "resolved_path" Wire.asString fields)

  original : ℕ → Step.Registration → Validation.Fault ⊎ (Text × ℤ)
  original token registration with Admission.resolve descriptor token registration
  ... | inj₁ fault = inj₁ fault
  ... | inj₂ (reserved , binding) with request (Store.BindingRow.arguments binding)
  ... | inj₁ fault = inj₁ fault
  ... | inj₂ requested = Decode.mapResult (λ path → path , Store.ReservationRow.reservedAt reserved)
    (prepared (Store.BindingRow.settings binding))

  admit : ℕ → Step.Registration → Maybe B.G.Diagnostic
  admit token registration with original token registration
  ... | inj₁ fault = just (B.G.requestFault fault)
  ... | inj₂ _ = nothing

  module AtReceipt (observedTime : ℤ) where
    decide : ℕ → Store.World → B.Outcome
    decide token before with original token (Step.registration before)
    ... | inj₁ fault = inj₁ (B.G.requestFault fault)
    ... | inj₂ (path , publicationTime) = proj₁ (B.checked observedTime path before)

    keepsJournal : ∀ token before after reply → decide token before ≡ inj₂ (after , reply) →
      Store.World.operations after ≡ Store.World.operations before
    keepsJournal token before after reply accepted with original token (Step.registration before)
    ... | inj₁ fault with accepted
    ... | ()
    keepsJournal token before after reply accepted | inj₂ (path , publicationTime) =
      B.journalUnchanged observedTime path before after reply accepted

    module Saved = Step.Admitted ℕ B.G.Diagnostic (λ token → token) key distinct decide keepsJournal admit

    FreshGoal : ℕ → Text → ℤ → Store.World → Store.World → Saved.Reply → Set
    FreshGoal token path publicationTime before after (Step.done reply) = Σ Store.World (λ changed →
      B.Goal publicationTime path before (inj₂ (changed , reply)) ×
      after ≡ Saved.Kernel.publication token changed reply)
    FreshGoal token path publicationTime before after (Step.needsInput diagnostic) =
      after ≡ before × B.Goal publicationTime path before (inj₁ diagnostic)
    FreshGoal token path publicationTime before after _ = ⊥

    originalDecides : ∀ token before path publicationTime →
      original token (Step.registration before) ≡ inj₂ (path , publicationTime) →
      decide token before ≡ proj₁ (B.checked observedTime path before)
    originalDecides token before path publicationTime bound rewrite bound = refl

    freshMeaning : ∀ token path publicationTime before →
      original token (Step.registration before) ≡ inj₂ (path , publicationTime) →
      FreshGoal token path observedTime before (proj₁ (Saved.Kernel.fresh token before))
        (proj₂ (Saved.Kernel.fresh token before))
    freshMeaning token path publicationTime before bound
      rewrite originalDecides token before path publicationTime bound
      with B.checked observedTime path before
    ... | inj₁ diagnostic , correct = refl , correct
    ... | inj₂ (changed , reply) , correct = changed , correct , refl

    Goal : ℕ → Store.World → Store.World → Saved.Reply → Set
    Goal token before after reply with original token (Step.registration before)
    ... | inj₁ fault = after ≡ before × reply ≡ Step.needsInput (B.G.requestFault fault)
    ... | inj₂ (path , publicationTime) with Store.lookupCancellation before token
    ... | just cancelled = after ≡ before × reply ≡ Step.cancelled cancelled
    ... | nothing with Store.lookupSaved before token (key token) | Store.lookupSaved before token Step.resultKey
    ... | just saved | just _ = after ≡ before × reply ≡ Step.done saved
    ... | just _ | nothing = after ≡ before × reply ≡ Step.needsRecovery
    ... | nothing | just _ = after ≡ before × reply ≡ Step.needsRecovery
    ... | nothing | nothing = FreshGoal token path observedTime before after reply

    meaning : ∀ token before → Goal token before (proj₁ (Saved.execute token before))
      (proj₂ (Saved.execute token before))
    meaning token before with original token (Step.registration before) in bound
    ... | inj₁ fault = refl , refl
    ... | inj₂ (path , publicationTime) with Store.lookupCancellation before token
    ... | just cancelled = refl , refl
    ... | nothing with Store.lookupSaved before token (key token) | Store.lookupSaved before token Step.resultKey
    ... | just _ | just _ = refl , refl
    ... | just _ | nothing = refl , refl
    ... | nothing | just _ = refl , refl
    ... | nothing | nothing = freshMeaning token path publicationTime before bound


  Internal = ℕ × ℤ
  decide : Internal → Store.World → B.Outcome
  decide (token , time) = AtReceipt.decide time token
  keepsJournal : ∀ input before after reply → decide input before ≡ inj₂ (after , reply) →
    Store.World.operations after ≡ Store.World.operations before
  keepsJournal (token , time) = AtReceipt.keepsJournal time token

  module Run = Step.Observed ℤ B.G.Diagnostic key distinct
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
