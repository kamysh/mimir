{-# OPTIONS --safe #-}
-- An acknowledged rollback asks for input without saving completion. A
-- publication commits data and both original answers. Assembly fixes Goal.
module Mimir.RecoverableStoreStep where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String using (toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Relation.Nullary using (¬_)
open import Mimir.Text using (Text)
import Mimir.ApplicationStore as Store
import Mimir.DatabaseTransaction as DB
import Mimir.Recovery as Recovery
import Mimir.StructuredValue as Wire

data Result (Diagnostic : Set) : Set where
  done : Wire.Value → Result Diagnostic
  needsInput : Diagnostic → Result Diagnostic
  needsRecovery : Result Diagnostic
  cancelled : Store.CancellationRow → Result Diagnostic

resultKey : Text
resultKey = toList "@operation-result"

receiptFor : ∀ {Diagnostic} → Result Diagnostic → DB.Receipt
receiptFor (done _) = DB.committed
receiptFor (needsInput _) = DB.aborted
receiptFor needsRecovery = DB.aborted
receiptFor (cancelled _) = DB.aborted

-- Immutable stored input, distinct from business state and saved answers. This
-- projection controls admission only; every outcome still concerns the full World.
Registration : Set
Registration = List Store.ReservationRow × List Store.RequestKeyRow ×
  List Store.BindingRow × List Store.PlanRow

registration : Store.World → Registration
registration before = Store.OperationTables.reservations tables ,
  Store.OperationTables.requestKeys tables , Store.OperationTables.bindings tables ,
  Store.OperationTables.plans tables
  where tables = Store.World.operations before

-- Fixed physical semantics for one acknowledged transaction. Callers supply
-- executable meaning and its proofs, never an arbitrary Atomic relation.
module AtomicStep (Input Diagnostic : Set)
  (execute : Input → Store.World → Store.World × Result Diagnostic)
  (stable : ∀ input before → execute input (proj₁ (execute input before)) ≡ execute input before)
  (expectedPhysical : ∀ input before → DB.Atomic before (proj₁ (execute input before))
    (receiptFor (proj₂ (execute input before))) (proj₁ (execute input before))) where
  Reply = Result Diagnostic
  receipt : Reply → DB.Receipt
  receipt = receiptFor

  data Acknowledged : DB.Receipt → Set where
    commit : Acknowledged DB.committed
    rollback : Acknowledged DB.aborted

  receiptKnown : ∀ reply → Acknowledged (receipt reply)
  receiptKnown (done _) = commit
  receiptKnown (needsInput _) = rollback
  receiptKnown needsRecovery = rollback
  receiptKnown (cancelled _) = rollback

  acknowledgedUnique : ∀ {before proposed first second : Store.World} {tag : DB.Receipt} → Acknowledged tag →
    DB.Atomic before proposed tag first → DB.Atomic before proposed tag second → first ≡ second
  acknowledgedUnique commit DB.committedAll DB.committedAll = refl
  acknowledgedUnique rollback DB.abortedNone DB.abortedNone = refl

  Atomic : Store.World → Input → Reply → Store.World → Set
  Atomic before input reply after = reply ≡ proj₂ (execute input before) ×
    DB.Atomic before (proj₁ (execute input before)) (receipt reply) after

  module X = Recovery.Execution Store.World Input (λ _ → Reply) Atomic
  module E = X.E

  script : Input → E.Script Reply
  script input = E.ask input E.done

  atomicObservation : ∀ input before after reply → Atomic before input reply after →
    (after , reply) ≡ execute input before
  atomicObservation input before after .(proj₂ (execute input before)) (refl , physical) =
    cong (λ world → world , proj₂ (execute input before))
      (acknowledgedUnique (receiptKnown _) physical (expectedPhysical input before))

  oneObservation : ∀ input before after reply →
    X.Changes before ((input , reply) ∷ []) after → (after , reply) ≡ execute input before
  oneObservation input before after reply (X.changed _ _ _ _ physical (X.unchanged _)) =
    atomicObservation input before after reply physical

  completedObservation : ∀ input before after reply →
    X.Completed (script input) before after reply → (after , reply) ≡ execute input before
  completedObservation input before after reply
    (X.completed _ (E.replied _ _ _ (E.returned _)) physical) = oneObservation input before after reply physical

  interruptionState : ∀ input initial interrupted → X.Interrupted (script input) initial interrupted →
    interrupted ≡ initial ⊎ interrupted ≡ proj₁ (execute input initial)
  interruptionState input initial interrupted (X.atPrefix _ _ _ (E.stopped _) (X.unchanged _)) = inj₁ refl
  interruptionState input initial interrupted (X.atPrefix _ _ _ (E.replied _ _ _ (E.stopped _)) physical) =
    inj₂ (cong proj₁ (oneObservation input initial interrupted _ physical))
  interruptionState input initial interrupted
    (X.beforeReply _ _ _ _ _ _ (E.stopped _) (X.unchanged _) physical) =
    inj₂ (cong proj₁ (atomicObservation input initial interrupted _ physical))
  interruptionState input initial interrupted (X.beforeReply _ _ _ _ _ _ (E.replied _ _ _ ()) physical active)

  everyDatabaseReceiptCovered : ∀ input before tag actual →
    DB.Atomic before (proj₁ (execute input before)) tag actual → X.Interrupted (script input) before actual
  everyDatabaseReceiptCovered input before .DB.committed _ DB.committedAll =
    X.beforeReply [] input E.done before (proj₂ (execute input before)) _
      (E.stopped _) (X.unchanged before) (refl , expectedPhysical input before)
  everyDatabaseReceiptCovered input before .DB.aborted _ DB.abortedNone =
    X.atPrefix [] (script input) before (E.stopped _) (X.unchanged before)
  everyDatabaseReceiptCovered input before .DB.acknowledgementLost _ DB.unknownBefore =
    X.atPrefix [] (script input) before (E.stopped _) (X.unchanged before)
  everyDatabaseReceiptCovered input before .DB.acknowledgementLost _ DB.unknownAfter =
    X.beforeReply [] input E.done before (proj₂ (execute input before)) _
      (E.stopped _) (X.unchanged before) (refl , expectedPhysical input before)

  progress : ∀ input initial → Σ Store.World (λ final → Σ Reply (λ reply → X.Completed (script input) initial final reply))
  progress input initial = proj₁ expected , proj₂ expected ,
    X.completed ((input , proj₂ expected) ∷ [])
      (E.replied input E.done (proj₂ expected) (E.returned _))
      (X.changed initial input _ _ (refl , expectedPhysical input initial) (X.unchanged _))
    where expected = execute input initial

  module Certified (Goal : Input → Store.World → Store.World → Reply → Set)
    (meaning : ∀ input initial → Goal input initial (proj₁ (execute input initial)) (proj₂ (execute input initial))) where

    fromObservation : ∀ input initial final reply → (final , reply) ≡ execute input initial → Goal input initial final reply
    fromObservation input initial final reply observed = subst
      (λ outcome → Goal input initial (proj₁ outcome) (proj₂ outcome)) (sym observed) (meaning input initial)

    converges : ∀ input initial interrupted final reply →
      X.Interrupted (script input) initial interrupted → X.Completed (script input) interrupted final reply →
      Goal input initial final reply
    converges input initial interrupted final reply interruption completion
      with interruptionState input initial interrupted interruption
    ... | inj₁ before = fromObservation input initial final reply
      (trans (completedObservation input interrupted final reply completion) (cong (execute input) before))
    ... | inj₂ after = fromObservation input initial final reply
      (trans (completedObservation input interrupted final reply completion)
        (trans (cong (execute input) after) (stable input initial)))

    operation : Recovery.RecoverableFor Store.World Input Reply Goal
    operation = record
      { Effect = Input; Reply = λ _ → Reply; script = script; Atomic = Atomic
      ; converges = converges; progress = progress }

module For (Input Diagnostic : Set)
  (token : Input → ℕ) (key : Input → Text)
  (distinct : ∀ input → ¬ (key input ≡ resultKey))
  (decide : Input → Store.World → Diagnostic ⊎ (Store.World × Wire.Value))
  (keepsJournal : ∀ input before changed reply → decide input before ≡ inj₂ (changed , reply) →
    Store.World.operations changed ≡ Store.World.operations before) where

  Reply = Result Diagnostic

  firstPublication : Input → Store.World → Wire.Value → Store.World
  firstPublication input changed reply = Store.saveAnswer changed (token input) (key input) reply

  publication : Input → Store.World → Wire.Value → Store.World
  publication input changed reply = Store.saveAnswer (firstPublication input changed reply) (token input) resultKey reply

  fresh : Input → Store.World → Store.World × Reply
  fresh input before with decide input before
  ... | inj₁ diagnostic = before , needsInput diagnostic
  ... | inj₂ (changed , reply) = publication input changed reply , done reply

  executeActive : Input → Store.World → Store.World × Reply
  executeActive input before with Store.lookupSaved before (token input) (key input)
    | Store.lookupSaved before (token input) resultKey
  ... | just saved | just _ = before , done saved
  ... | just _ | nothing = before , needsRecovery
  ... | nothing | just _ = before , needsRecovery
  ... | nothing | nothing = fresh input before

  execute : Input → Store.World → Store.World × Reply
  execute input before with Store.lookupCancellation before (token input)
  ... | just original = before , cancelled original
  ... | nothing = executeActive input before

  replay : ∀ input before saved final →
    Store.lookupCancellation before (token input) ≡ nothing →
    Store.lookupSaved before (token input) (key input) ≡ just saved →
    Store.lookupSaved before (token input) resultKey ≡ just final →
    execute input before ≡ (before , done saved)
  replay input before saved final active step result rewrite active | step | result = refl

  changedLookup : ∀ input before changed reply step → decide input before ≡ inj₂ (changed , reply) →
    Store.lookupSaved changed (token input) step ≡ Store.lookupSaved before (token input) step
  changedLookup input before changed reply step accepted = cong
    (λ tables → Store.lookupReply (token input) step (Store.OperationTables.savedReplies tables))
    (keepsJournal input before changed reply accepted)

  firstReadable : ∀ input before changed reply → decide input before ≡ inj₂ (changed , reply) →
    Store.lookupSaved before (token input) (key input) ≡ nothing →
    Store.lookupSaved (firstPublication input changed reply) (token input) (key input) ≡ just reply
  firstReadable input before changed reply accepted absent
    rewrite changedLookup input before changed reply (key input) accepted | absent =
    Store.headReplyReadable (token input) (key input) reply _

  publishedStepReadable : ∀ input before changed reply → decide input before ≡ inj₂ (changed , reply) →
    Store.lookupSaved before (token input) (key input) ≡ nothing →
    Store.lookupSaved (publication input changed reply) (token input) (key input) ≡ just reply
  publishedStepReadable input before changed reply accepted absent = trans
    (Store.otherSavedAnswerPreserved (firstPublication input changed reply) (token input) resultKey
      reply (token input) (key input) (λ same → distinct input (proj₂ same)))
    (firstReadable input before changed reply accepted absent)

  firstHasNoResult : ∀ input before changed reply → decide input before ≡ inj₂ (changed , reply) →
    Store.lookupSaved before (token input) resultKey ≡ nothing →
    Store.lookupSaved (firstPublication input changed reply) (token input) resultKey ≡ nothing
  firstHasNoResult input before changed reply accepted absent = trans
    (Store.otherSavedAnswerPreserved changed (token input) (key input) reply (token input) resultKey
      (λ same → distinct input (sym (proj₂ same))))
    (trans (changedLookup input before changed reply resultKey accepted) absent)

  publishedResultReadable : ∀ input before changed reply → decide input before ≡ inj₂ (changed , reply) →
    Store.lookupSaved before (token input) resultKey ≡ nothing →
    Store.lookupSaved (publication input changed reply) (token input) resultKey ≡ just reply
  publishedResultReadable input before changed reply accepted absent
    rewrite firstHasNoResult input before changed reply accepted absent =
    Store.headReplyReadable (token input) resultKey reply _

  publicationKeepsCancellation : ∀ input before changed reply → decide input before ≡ inj₂ (changed , reply) →
    Store.lookupCancellation (publication input changed reply) (token input) ≡ Store.lookupCancellation before (token input)
  publicationKeepsCancellation input before changed reply accepted = trans
    (Store.savingAnswerPreservesCancellation (firstPublication input changed reply) (token input) resultKey reply (token input))
    (trans (Store.savingAnswerPreservesCancellation changed (token input) (key input) reply (token input))
      (cong (λ tables → Store.lookupCancellationRows (token input) (Store.OperationTables.cancellations tables))
        (keepsJournal input before changed reply accepted)))

  stable : ∀ input before → execute input (proj₁ (execute input before)) ≡ execute input before
  stable input before with Store.lookupCancellation before (token input) in active
  ... | just original rewrite active = refl
  ... | nothing with Store.lookupSaved before (token input) (key input) in step
    | Store.lookupSaved before (token input) resultKey in result
  ... | just saved | just final = replay input before saved final active step result
  ... | just _ | nothing rewrite active | step | result = refl
  ... | nothing | just _ rewrite active | step | result = refl
  ... | nothing | nothing with decide input before in accepted
  ... | inj₁ diagnostic rewrite active | step | result | accepted = refl
  ... | inj₂ (changed , reply) = replay input _ reply reply
    (trans (publicationKeepsCancellation input before changed reply accepted) active)
    (publishedStepReadable input before changed reply accepted step)
    (publishedResultReadable input before changed reply accepted result)

  receipt : Reply → DB.Receipt
  receipt = receiptFor

  expectedPhysical : ∀ input before → DB.Atomic before (proj₁ (execute input before))
    (receipt (proj₂ (execute input before))) (proj₁ (execute input before))
  expectedPhysical input before with Store.lookupCancellation before (token input)
  ... | just _ = DB.abortedNone
  ... | nothing with Store.lookupSaved before (token input) (key input)
    | Store.lookupSaved before (token input) resultKey
  ... | just _ | just _ = DB.committedAll
  ... | just _ | nothing = DB.abortedNone
  ... | nothing | just _ = DB.abortedNone
  ... | nothing | nothing with decide input before
  ... | inj₁ _ = DB.abortedNone
  ... | inj₂ _ = DB.committedAll

  refusalRemainsPending : ∀ input before diagnostic →
    Store.lookupCancellation before (token input) ≡ nothing →
    Store.lookupSaved before (token input) (key input) ≡ nothing →
    Store.lookupSaved before (token input) resultKey ≡ nothing →
    decide input before ≡ inj₁ diagnostic → execute input before ≡ (before , needsInput diagnostic)
  refusalRemainsPending input before diagnostic active step result refused
    rewrite active | step | result | refused = refl


  publicationKeepsRegistration : ∀ input before changed reply → decide input before ≡ inj₂ (changed , reply) →
    registration (publication input changed reply) ≡ registration before
  publicationKeepsRegistration input before changed reply accepted = trans
    (Store.savingAnswerPreservesOperationInputs (firstPublication input changed reply) (token input) resultKey reply)
    (trans (Store.savingAnswerPreservesOperationInputs changed (token input) (key input) reply)
      (cong (λ tables → Store.OperationTables.reservations tables , Store.OperationTables.requestKeys tables ,
        Store.OperationTables.bindings tables , Store.OperationTables.plans tables)
        (keepsJournal input before changed reply accepted)))

  registrationUnchanged : ∀ input before → registration (proj₁ (execute input before)) ≡ registration before
  registrationUnchanged input before with Store.lookupCancellation before (token input)
  ... | just _ = refl
  ... | nothing with Store.lookupSaved before (token input) (key input) | Store.lookupSaved before (token input) resultKey
  ... | just _ | just _ = refl
  ... | just _ | nothing = refl
  ... | nothing | just _ = refl
  ... | nothing | nothing with decide input before in accepted
  ... | inj₁ _ = refl
  ... | inj₂ (changed , reply) = publicationKeepsRegistration input before changed reply accepted

  module Core = AtomicStep Input Diagnostic execute stable expectedPhysical
  open Core public hiding (Reply; receipt)

-- Metadata admission precedes cancellation/readback as well as fresh execution.
-- A stored answer cannot hide an invalid binding or a mismatched saved plan.
module Admitted (Input Diagnostic : Set)
  (token : Input → ℕ) (key : Input → Text)
  (distinct : ∀ input → ¬ (key input ≡ resultKey))
  (decide : Input → Store.World → Diagnostic ⊎ (Store.World × Wire.Value))
  (keepsJournal : ∀ input before changed reply → decide input before ≡ inj₂ (changed , reply) →
    Store.World.operations changed ≡ Store.World.operations before)
  (admit : Input → Registration → Maybe Diagnostic) where

  module Kernel = For Input Diagnostic token key distinct decide keepsJournal
  Reply = Result Diagnostic

  execute : Input → Store.World → Store.World × Reply
  execute input before with admit input (registration before)
  ... | just diagnostic = before , needsInput diagnostic
  ... | nothing = Kernel.execute input before

  stable : ∀ input before → execute input (proj₁ (execute input before)) ≡ execute input before
  stable input before with admit input (registration before) in admitted
  ... | just diagnostic rewrite admitted = refl
  ... | nothing rewrite Kernel.registrationUnchanged input before | admitted = Kernel.stable input before

  expectedPhysical : ∀ input before → DB.Atomic before (proj₁ (execute input before))
    (receiptFor (proj₂ (execute input before))) (proj₁ (execute input before))
  expectedPhysical input before with admit input (registration before)
  ... | just _ = DB.abortedNone
  ... | nothing = Kernel.expectedPhysical input before

  admissionRefusalChangesNothing : ∀ input before diagnostic →
    admit input (registration before) ≡ just diagnostic → execute input before ≡ (before , needsInput diagnostic)
  admissionRefusalChangesNothing input before diagnostic refused rewrite refused = refl

  module Core = AtomicStep Input Diagnostic execute stable expectedPhysical
  open Core public hiding (Reply)
