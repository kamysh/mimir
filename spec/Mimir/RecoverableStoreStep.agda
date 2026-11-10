{-# OPTIONS --safe #-}
-- An acknowledged rollback asks for input without saving completion. A
-- publication commits data and both original answers. Assembly fixes Goal.
module Mimir.RecoverableStoreStep where

open import Data.List using (List; []; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe.Properties as Maybes
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

  atomicDoneOrUnchanged : ∀ input before after reply → Atomic before input reply after →
    after ≡ before ⊎ Σ Wire.Value (λ value → (after , done value) ≡ execute input before)
  atomicDoneOrUnchanged input before after (done value) physical =
    inj₂ (value , atomicObservation input before after (done value) physical)
  atomicDoneOrUnchanged input before .before (needsInput _) (observed , DB.abortedNone) = inj₁ refl
  atomicDoneOrUnchanged input before .before needsRecovery (observed , DB.abortedNone) = inj₁ refl
  atomicDoneOrUnchanged input before .before (cancelled _) (observed , DB.abortedNone) = inj₁ refl

  interruptedDoneOrUnchanged : ∀ input before after → X.Interrupted (script input) before after →
    after ≡ before ⊎ Σ Wire.Value (λ value → (after , done value) ≡ execute input before)
  interruptedDoneOrUnchanged input before after (X.atPrefix _ _ _ (E.stopped _) (X.unchanged _)) = inj₁ refl
  interruptedDoneOrUnchanged input before after
    (X.atPrefix _ _ _ (E.replied _ _ reply (E.stopped _))
      (X.changed _ _ _ _ physical (X.unchanged _))) = atomicDoneOrUnchanged input before after reply physical
  interruptedDoneOrUnchanged input before after
    (X.beforeReply _ _ _ _ reply _ (E.stopped _) (X.unchanged _) physical) =
    atomicDoneOrUnchanged input before after reply physical
  interruptedDoneOrUnchanged input before after (X.beforeReply _ _ _ _ _ _ (E.replied _ _ _ ()) _ _)

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

  -- A cached answer must admit an actual read-only execution of this fixed
  -- statement. The equation is about the real executor and complete World.
  readOnlyCompletion : ∀ input before value → execute input before ≡ (before , done value) →
    X.Completed (script input) before before (done value)
  readOnlyCompletion input before value observed = subst
    (λ outcome → X.Completed (script input) before (proj₁ outcome) (proj₂ outcome))
    observed (proj₂ (proj₂ (progress input before)))

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

  publicationKeepsCancellations : ∀ wanted input before changed reply → decide input before ≡ inj₂ (changed , reply) →
    Store.lookupCancellation (publication input changed reply) wanted ≡ Store.lookupCancellation before wanted
  publicationKeepsCancellations wanted input before changed reply accepted = trans
    (Store.savingAnswerPreservesCancellation (firstPublication input changed reply) (token input) resultKey reply wanted)
    (trans (Store.savingAnswerPreservesCancellation changed (token input) (key input) reply wanted)
      (cong (λ tables → Store.lookupCancellationRows wanted (Store.OperationTables.cancellations tables))
        (keepsJournal input before changed reply accepted)))

  -- A returned answer either read the existing World or published both of
  -- its matching immutable answers. A later readback cannot invent a third
  -- value for a newly completed operation.
  doneOrigin : ∀ input before after value → execute input before ≡ (after , done value) →
    after ≡ before ⊎
    (Store.lookupCancellation after (token input) ≡ nothing ×
      Store.lookupSaved after (token input) (key input) ≡ just value ×
      Store.lookupSaved after (token input) resultKey ≡ just value)
  doneOrigin input before after value observed with Store.lookupCancellation before (token input) in active
  ... | just _ with observed
  ... | ()
  doneOrigin input before after value observed | nothing
    with Store.lookupSaved before (token input) (key input) in step
      | Store.lookupSaved before (token input) resultKey in final
  ... | just saved | just result with observed
  ... | refl = inj₁ refl
  doneOrigin input before after value () | nothing | just _ | nothing
  doneOrigin input before after value () | nothing | nothing | just _
  doneOrigin input before after value observed | nothing | nothing | nothing
    with decide input before in accepted
  ... | inj₁ _ with observed
  ... | ()
  doneOrigin input before after value observed | nothing | nothing | nothing | inj₂ (changed , reply)
    with observed
  ... | refl = inj₂
    (trans (publicationKeepsCancellation input before changed reply accepted) active ,
      publishedStepReadable input before changed reply accepted step ,
      publishedResultReadable input before changed reply accepted final)

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

  cancellationUnchanged : ∀ wanted input before →
    Store.lookupCancellation (proj₁ (execute input before)) wanted ≡ Store.lookupCancellation before wanted
  cancellationUnchanged wanted input before with Store.lookupCancellation before (token input)
  ... | just _ = refl
  ... | nothing with Store.lookupSaved before (token input) (key input) | Store.lookupSaved before (token input) resultKey
  ... | just _ | just _ = refl
  ... | just _ | nothing = refl
  ... | nothing | just _ = refl
  ... | nothing | nothing with decide input before in accepted
  ... | inj₁ _ = refl
  ... | inj₂ (changed , reply) = publicationKeepsCancellations wanted input before changed reply accepted

  module Core = AtomicStep Input Diagnostic execute stable expectedPhysical
  open Core public hiding (Reply; receipt)

  atomicKeepsCancellation : ∀ wanted before input reply after → Atomic before input reply after →
    Store.lookupCancellation after wanted ≡ Store.lookupCancellation before wanted
  atomicKeepsCancellation wanted before input reply after physical = trans
    (cong (λ outcome → Store.lookupCancellation (proj₁ outcome) wanted) (atomicObservation input before after reply physical))
    (cancellationUnchanged wanted input before)

  changesKeepCancellation : ∀ wanted {before events after} → X.Changes before events after →
    Store.lookupCancellation after wanted ≡ Store.lookupCancellation before wanted
  changesKeepCancellation wanted (X.unchanged _) = refl
  changesKeepCancellation wanted (X.changed before input reply middle physical later) = trans
    (changesKeepCancellation wanted later) (atomicKeepsCancellation wanted before input reply middle physical)

  interruptedKeepsCancellation : ∀ wanted input before after → X.Interrupted (script input) before after →
    Store.lookupCancellation after wanted ≡ Store.lookupCancellation before wanted
  interruptedKeepsCancellation wanted input before after (X.atPrefix _ _ _ _ physical) = changesKeepCancellation wanted physical
  interruptedKeepsCancellation wanted input before after (X.beforeReply _ effect _ middle reply _ _ previous physical) = trans
    (atomicKeepsCancellation wanted middle effect reply after physical) (changesKeepCancellation wanted previous)

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

  replay : ∀ input before saved final →
    admit input (registration before) ≡ nothing →
    Store.lookupCancellation before (token input) ≡ nothing →
    Store.lookupSaved before (token input) (key input) ≡ just saved →
    Store.lookupSaved before (token input) resultKey ≡ just final →
    execute input before ≡ (before , done saved)
  replay input before saved final admitted active step result rewrite admitted =
    Kernel.replay input before saved final active step result

  doneOrigin : ∀ input before after value → execute input before ≡ (after , done value) →
    after ≡ before ⊎
    (Store.lookupCancellation after (token input) ≡ nothing ×
      Store.lookupSaved after (token input) (key input) ≡ just value ×
      Store.lookupSaved after (token input) resultKey ≡ just value)
  doneOrigin input before after value observed with admit input (registration before)
  ... | just _ with observed
  ... | ()
  doneOrigin input before after value observed | nothing = Kernel.doneOrigin input before after value observed

  doneIsAdmitted : ∀ input before after value → execute input before ≡ (after , done value) →
    admit input (registration before) ≡ nothing
  doneIsAdmitted input before after value observed with admit input (registration before)
  ... | just _ with observed
  ... | ()
  doneIsAdmitted input before after value observed | nothing = refl

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

  registrationUnchanged : ∀ input before → registration (proj₁ (execute input before)) ≡ registration before
  registrationUnchanged input before with admit input (registration before)
  ... | just _ = refl
  ... | nothing = Kernel.registrationUnchanged input before

  cancellationUnchanged : ∀ wanted input before →
    Store.lookupCancellation (proj₁ (execute input before)) wanted ≡ Store.lookupCancellation before wanted
  cancellationUnchanged wanted input before with admit input (registration before)
  ... | just _ = refl
  ... | nothing = Kernel.cancellationUnchanged wanted input before

  module Core = AtomicStep Input Diagnostic execute stable expectedPhysical
  open Core public hiding (Reply)

  atomicKeepsRegistration : ∀ before input reply after → Atomic before input reply after →
    registration after ≡ registration before
  atomicKeepsRegistration before input reply after physical = trans
    (cong (λ outcome → registration (proj₁ outcome)) (atomicObservation input before after reply physical))
    (registrationUnchanged input before)

  changesKeepRegistration : ∀ {before events after} → X.Changes before events after → registration after ≡ registration before
  changesKeepRegistration (X.unchanged _) = refl
  changesKeepRegistration (X.changed before input reply middle physical later) = trans
    (changesKeepRegistration later) (atomicKeepsRegistration before input reply middle physical)

  interruptedKeepsRegistration : ∀ input before after → X.Interrupted (script input) before after →
    registration after ≡ registration before
  interruptedKeepsRegistration input before after (X.atPrefix _ _ _ _ physical) = changesKeepRegistration physical
  interruptedKeepsRegistration input before after (X.beforeReply _ effect _ middle reply _ _ previous physical) = trans
    (atomicKeepsRegistration middle effect reply after physical) (changesKeepRegistration previous)

  atomicKeepsCancellation : ∀ wanted before input reply after → Atomic before input reply after →
    Store.lookupCancellation after wanted ≡ Store.lookupCancellation before wanted
  atomicKeepsCancellation wanted before input reply after physical = trans
    (cong (λ outcome → Store.lookupCancellation (proj₁ outcome) wanted) (atomicObservation input before after reply physical))
    (cancellationUnchanged wanted input before)

  changesKeepCancellation : ∀ wanted {before events after} → X.Changes before events after →
    Store.lookupCancellation after wanted ≡ Store.lookupCancellation before wanted
  changesKeepCancellation wanted (X.unchanged _) = refl
  changesKeepCancellation wanted (X.changed before input reply middle physical later) = trans
    (changesKeepCancellation wanted later) (atomicKeepsCancellation wanted before input reply middle physical)

  interruptedKeepsCancellation : ∀ wanted input before after → X.Interrupted (script input) before after →
    Store.lookupCancellation after wanted ≡ Store.lookupCancellation before wanted
  interruptedKeepsCancellation wanted input before after (X.atPrefix _ _ _ _ physical) = changesKeepCancellation wanted physical
  interruptedKeepsCancellation wanted input before after (X.beforeReply _ effect _ middle reply _ _ previous physical) = trans
    (atomicKeepsCancellation wanted middle effect reply after physical) (changesKeepCancellation wanted previous)

  cachedReplay : ∀ input before current raw →
    Store.lookupSaved before (token input) resultKey ≡ nothing →
    Store.lookupSaved current (token input) resultKey ≡ just raw →
    X.Interrupted (script input) before current →
    X.Completed (script input) current current (done raw)
  cachedReplay input before current raw absent present cut
    with interruptedDoneOrUnchanged input before current cut
  ... | inj₁ same = ⊥-elim (impossible same)
    where
    impossible : current ≡ before → ⊥
    impossible refl with trans (sym absent) present
    ... | ()
  ... | inj₂ (value , observed) with doneOrigin input before current value (sym observed)
  ... | inj₁ same = ⊥-elim (impossible same)
    where
    impossible : current ≡ before → ⊥
    impossible refl with trans (sym absent) present
    ... | ()
  ... | inj₂ (_ , _ , final) = subst
    (λ answer → X.Completed (script input) current current (done answer))
    (Maybes.just-injective (trans (sym final) present))
    (readOnlyCompletion input current value
      (trans (cong (execute input) (cong proj₁ observed))
        (trans (stable input before) (sym observed))))

-- The same saved final step with metadata observed by the committing statement,
-- rather than supplied in the public request. Admission, address and original
-- reply do not depend on a later clock sample. This is the receipt adapter used
-- by the registered posterior writers; the selected business module fixes its
-- meaning below, and an observation function only exhibits progress.
module Observed (Metadata Diagnostic : Set)
  (key : ℕ → Text) (distinct : ∀ token → ¬ (key token ≡ resultKey))
  (decide : ℕ → Metadata → Store.World → Diagnostic ⊎ (Store.World × Wire.Value))
  (keepsJournal : ∀ token metadata before changed reply → decide token metadata before ≡ inj₂ (changed , reply) →
    Store.World.operations changed ≡ Store.World.operations before)
  (admit : ℕ → Registration → Maybe Diagnostic)
  (available : ℕ → Store.World → Metadata) where

  module Saved = Admitted (ℕ × Metadata) Diagnostic proj₁ (λ input → key (proj₁ input))
    (λ input → distinct (proj₁ input)) (λ input → decide (proj₁ input) (proj₂ input))
    (λ input → keepsJournal (proj₁ input) (proj₂ input)) (λ input → admit (proj₁ input))
  module K = Saved.Kernel

  record OriginalAnswer (token : ℕ) (after : Store.World) (reply : Wire.Value) : Set where
    constructor originalAnswer
    field active : Store.lookupCancellation after token ≡ nothing
          step : Store.lookupSaved after token (key token) ≡ just reply
          final : Σ Wire.Value (λ value → Store.lookupSaved after token resultKey ≡ just value)

  kernelDone : ∀ token metadata before reply →
    proj₂ (K.execute (token , metadata) before) ≡ done reply →
    OriginalAnswer token (proj₁ (K.execute (token , metadata) before)) reply
  kernelDone token metadata before reply completed with Store.lookupCancellation before token in active
  ... | just _ with completed
  ... | ()
  kernelDone token metadata before reply completed | nothing
    with Store.lookupSaved before token (key token) in step | Store.lookupSaved before token resultKey in final
  ... | just saved | just value with completed
  ... | refl = originalAnswer active step (value , final)
  kernelDone token metadata before reply () | nothing | just _ | nothing
  kernelDone token metadata before reply () | nothing | nothing | just _
  kernelDone token metadata before reply completed | nothing | nothing | nothing
    with decide token metadata before in accepted
  ... | inj₁ _ with completed
  ... | ()
  kernelDone token metadata before reply completed | nothing | nothing | nothing | inj₂ (changed , value) with completed
  ... | refl = originalAnswer
    (trans (K.publicationKeepsCancellation (token , metadata) before changed value accepted) active)
    (K.publishedStepReadable (token , metadata) before changed value accepted step)
    (value , K.publishedResultReadable (token , metadata) before changed value accepted final)

  kernelStableDone : ∀ token first second before value →
    proj₂ (K.execute (token , first) before) ≡ done value →
    K.execute (token , second) (proj₁ (K.execute (token , first) before)) ≡ K.execute (token , first) before
  kernelStableDone token first second before value completed = trans
    (K.replay (token , second) _ value (proj₁ (OriginalAnswer.final saved))
      (OriginalAnswer.active saved) (OriginalAnswer.step saved) (proj₂ (OriginalAnswer.final saved)))
    (cong (λ reply → proj₁ (K.execute (token , first) before) , reply) (sym completed))
    where saved = kernelDone token first before value completed

  executesAdmitted : ∀ token metadata before → admit token (registration before) ≡ nothing →
    Saved.execute (token , metadata) before ≡ K.execute (token , metadata) before
  executesAdmitted token metadata before admitted rewrite admitted = refl

  doneStable : ∀ token first second before value →
    proj₂ (Saved.execute (token , first) before) ≡ done value →
    Saved.execute (token , second) (proj₁ (Saved.execute (token , first) before)) ≡ Saved.execute (token , first) before
  doneStable token first second before value completed with admit token (registration before) in admitted
  ... | just _ with completed
  ... | ()
  doneStable token first second before value completed | nothing = trans
    (executesAdmitted token second (proj₁ (K.execute (token , first) before))
      (trans (cong (admit token) (K.registrationUnchanged (token , first) before)) admitted))
    (kernelStableDone token first second before value completed)

  Effect = ℕ
  Reply : Effect → Set
  Reply _ = Metadata × Result Diagnostic
  Atomic : Store.World → (token : Effect) → Reply token → Store.World → Set
  Atomic before token (metadata , reply) after = Saved.Atomic before (token , metadata) reply after
  module X = Recovery.Execution Store.World Effect Reply Atomic
  module E = X.E

  script : ℕ → E.Script (Result Diagnostic)
  script token = E.ask token (λ reply → E.done (proj₂ reply))
  completedObservation : ∀ token before after reply → X.Completed (script token) before after reply →
    Σ Metadata (λ metadata → (after , reply) ≡ Saved.execute (token , metadata) before)
  completedObservation token before after reply
    (X.completed _ (E.replied _ _ (metadata , _) (E.returned _))
      (X.changed _ _ _ _ physical (X.unchanged _))) =
    metadata , Saved.atomicObservation (token , metadata) before after reply physical

  data InterruptOutcome (token : ℕ) (before after : Store.World) : Set where
    unchanged : after ≡ before → InterruptOutcome token before after
    published : ∀ metadata value → (after , done value) ≡ Saved.execute (token , metadata) before →
      InterruptOutcome token before after

  interruptedAtomic : ∀ token before after metadata reply → Atomic before token (metadata , reply) after →
    InterruptOutcome token before after
  interruptedAtomic token before after metadata (done value) physical =
    published metadata value (Saved.atomicObservation (token , metadata) before after (done value) physical)
  interruptedAtomic token before .before metadata (needsInput _) (observed , DB.abortedNone) = unchanged refl
  interruptedAtomic token before .before metadata needsRecovery (observed , DB.abortedNone) = unchanged refl
  interruptedAtomic token before .before metadata (cancelled _) (observed , DB.abortedNone) = unchanged refl

  interruptionState : ∀ token before after → X.Interrupted (script token) before after → InterruptOutcome token before after
  interruptionState token before after (X.atPrefix _ _ _ (E.stopped _) (X.unchanged _)) = unchanged refl
  interruptionState token before after
    (X.atPrefix _ _ _ (E.replied _ _ (metadata , reply) (E.stopped _))
      (X.changed _ _ _ _ physical (X.unchanged _))) = interruptedAtomic token before after metadata reply physical
  interruptionState token before after
    (X.beforeReply _ _ _ _ (metadata , reply) _ (E.stopped _) (X.unchanged _) physical) =
    interruptedAtomic token before after metadata reply physical
  interruptionState token before after (X.beforeReply _ _ _ _ _ _ (E.replied _ _ _ ()) _ _)

  registrationUnchanged : ∀ token metadata before →
    registration (proj₁ (Saved.execute (token , metadata) before)) ≡ registration before
  registrationUnchanged token metadata before with admit token (registration before)
  ... | just _ = refl
  ... | nothing = K.registrationUnchanged (token , metadata) before

  atomicKeepsRegistration : ∀ before token observed after → Atomic before token observed after →
    registration after ≡ registration before
  atomicKeepsRegistration before token (metadata , reply) after physical = trans
    (cong (λ outcome → registration (proj₁ outcome)) (Saved.atomicObservation (token , metadata) before after reply physical))
    (registrationUnchanged token metadata before)

  changesKeepRegistration : ∀ {before events after} → X.Changes before events after → registration after ≡ registration before
  changesKeepRegistration (X.unchanged _) = refl
  changesKeepRegistration (X.changed before token observed middle physical later) =
    trans (changesKeepRegistration later) (atomicKeepsRegistration before token observed middle physical)

  interruptedKeepsRegistration : ∀ token before after → X.Interrupted (script token) before after →
    registration after ≡ registration before
  interruptedKeepsRegistration token before after (X.atPrefix _ _ _ _ physical) = changesKeepRegistration physical
  interruptedKeepsRegistration token before after (X.beforeReply _ effect _ middle observed _ _ previous active) =
    trans (atomicKeepsRegistration middle effect observed after active) (changesKeepRegistration previous)

  atomicKeepsCancellation : ∀ wanted before token observed after → Atomic before token observed after →
    Store.lookupCancellation after wanted ≡ Store.lookupCancellation before wanted
  atomicKeepsCancellation wanted before token (metadata , reply) after physical = trans
    (cong (λ outcome → Store.lookupCancellation (proj₁ outcome) wanted)
      (Saved.atomicObservation (token , metadata) before after reply physical))
    (Saved.cancellationUnchanged wanted (token , metadata) before)

  changesKeepCancellation : ∀ wanted {before events after} → X.Changes before events after →
    Store.lookupCancellation after wanted ≡ Store.lookupCancellation before wanted
  changesKeepCancellation wanted (X.unchanged _) = refl
  changesKeepCancellation wanted (X.changed before token observed middle physical later) = trans
    (changesKeepCancellation wanted later) (atomicKeepsCancellation wanted before token observed middle physical)

  interruptedKeepsCancellation : ∀ wanted token before after → X.Interrupted (script token) before after →
    Store.lookupCancellation after wanted ≡ Store.lookupCancellation before wanted
  interruptedKeepsCancellation wanted token before after (X.atPrefix _ _ _ _ physical) = changesKeepCancellation wanted physical
  interruptedKeepsCancellation wanted token before after (X.beforeReply _ effect _ middle observed _ _ previous physical) = trans
    (atomicKeepsCancellation wanted middle effect observed after physical) (changesKeepCancellation wanted previous)

  progress : ∀ token before → Σ Store.World (λ after → Σ (Result Diagnostic) (λ reply → X.Completed (script token) before after reply))
  progress token before = proj₁ outcome , proj₂ outcome , X.completed
    ((token , metadata , proj₂ outcome) ∷ [])
    (E.replied token (λ reply → E.done (proj₂ reply)) (metadata , proj₂ outcome) (E.returned _))
    (X.changed before token _ _ (refl , Saved.expectedPhysical (token , metadata) before) (X.unchanged _))
    where metadata = available token before
          outcome = Saved.execute (token , metadata) before

  readOnlyCompletion : ∀ token before value →
    Saved.execute (token , available token before) before ≡ (before , done value) →
    X.Completed (script token) before before (done value)
  readOnlyCompletion token before value observed = subst
    (λ outcome → X.Completed (script token) before (proj₁ outcome) (proj₂ outcome))
    observed (proj₂ (proj₂ (progress token before)))

  -- The admitted public prefix had no final answer. If a later actual
  -- readback finds one, this interrupted statement must have published it;
  -- retrying reads that same answer without another business change.
  cachedReplay : ∀ token before current raw →
    Store.lookupSaved before token resultKey ≡ nothing →
    Store.lookupSaved current token resultKey ≡ just raw →
    X.Interrupted (script token) before current →
    X.Completed (script token) current current (done raw)
  cachedReplay token before current raw absent present cut
    with interruptionState token before current cut
  ... | unchanged same = ⊥-elim (impossible same)
    where
    impossible : current ≡ before → ⊥
    impossible refl with trans (sym absent) present
    ... | ()
  ... | published metadata value observed
    with Saved.doneOrigin (token , metadata) before current value (sym observed)
  ... | inj₁ same = ⊥-elim (impossible same)
    where
    impossible : current ≡ before → ⊥
    impossible refl with trans (sym absent) present
    ... | ()
  ... | inj₂ (active , step , final) = subst
    (λ answer → X.Completed (script token) current current (done answer))
    (Maybes.just-injective (trans (sym final) present))
    (readOnlyCompletion token current value
      (Saved.replay (token , available token current) current value value
        (trans (cong (admit token) (interruptedKeepsRegistration token before current cut))
          (Saved.doneIsAdmitted (token , metadata) before current value (sym observed)))
        active step final))

  everyDatabaseReceiptCovered : ∀ token metadata before tag actual →
    DB.Atomic before (proj₁ (Saved.execute (token , metadata) before)) tag actual → X.Interrupted (script token) before actual
  everyDatabaseReceiptCovered token metadata before .DB.committed _ DB.committedAll =
    X.beforeReply [] token _ before (metadata , proj₂ (Saved.execute (token , metadata) before)) _
      (E.stopped _) (X.unchanged before) (refl , Saved.expectedPhysical (token , metadata) before)
  everyDatabaseReceiptCovered token metadata before .DB.aborted _ DB.abortedNone =
    X.atPrefix [] (script token) before (E.stopped _) (X.unchanged before)
  everyDatabaseReceiptCovered token metadata before .DB.acknowledgementLost _ DB.unknownBefore =
    X.atPrefix [] (script token) before (E.stopped _) (X.unchanged before)
  everyDatabaseReceiptCovered token metadata before .DB.acknowledgementLost _ DB.unknownAfter =
    X.beforeReply [] token _ before (metadata , proj₂ (Saved.execute (token , metadata) before)) _
      (E.stopped _) (X.unchanged before) (refl , Saved.expectedPhysical (token , metadata) before)

  module Certified (AtReceipt : ℕ → Metadata → Store.World → Store.World → Result Diagnostic → Set)
    (meaning : ∀ token metadata before → AtReceipt token metadata before
      (proj₁ (Saved.execute (token , metadata) before)) (proj₂ (Saved.execute (token , metadata) before))) where
    Goal : ℕ → Store.World → Store.World → Result Diagnostic → Set
    Goal token before after reply = Σ Metadata (λ metadata → AtReceipt token metadata before after reply)
    fromObservation : ∀ token metadata before after reply → (after , reply) ≡ Saved.execute (token , metadata) before → Goal token before after reply
    fromObservation token metadata before after reply observed = metadata , subst
      (λ outcome → AtReceipt token metadata before (proj₁ outcome) (proj₂ outcome)) (sym observed) (meaning token metadata before)
    converges : ∀ token before interrupted after reply → X.Interrupted (script token) before interrupted →
      X.Completed (script token) interrupted after reply → Goal token before after reply
    converges token before interrupted after reply crash completion
      with interruptionState token before interrupted crash | completedObservation token interrupted after reply completion
    ... | unchanged refl | metadata , observed = fromObservation token metadata before after reply observed
    ... | published first value same | second , observed = fromObservation token first before after reply
      (trans observed (trans (cong (Saved.execute (token , second)) (cong proj₁ same))
        (doneStable token first second before value (sym (cong proj₂ same)))))
    operation : Recovery.RecoverableFor Store.World ℕ (Result Diagnostic) Goal
    operation = record { Effect = Effect; Reply = Reply; script = script; Atomic = Atomic; converges = converges; progress = progress }
