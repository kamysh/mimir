{-# OPTIONS --safe #-}
-- Two actual committed phases on the complete application store. The first
-- phase can remain committed while the final phase asks for a user decision.
module Mimir.RecoverableStoreSequence where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
open import Relation.Nullary using (¬_)
open import Mimir.Text using (Text)
import Mimir.ApplicationStore as Store
import Mimir.DatabaseTransaction as DB
import Mimir.RecoverableStoreStep as Step
import Mimir.Recovery as Recovery
import Mimir.StructuredValue as Wire

-- A prefix answer certifies only its own durable step. It never saves the
-- operation result. Inconsistent final receipts request recovery before work.
module SavedPrefix (Input Diagnostic : Set)
  (token : Input → ℕ) (key nextKey : Input → Text)
  (distinct : ∀ input → ¬ (key input ≡ Step.resultKey))
  (different : ∀ input → ¬ (key input ≡ nextKey input))
  (decide : Input → Store.World → Diagnostic ⊎ (Store.World × Wire.Value))
  (keepsJournal : ∀ input before changed reply → decide input before ≡ inj₂ (changed , reply) →
    Store.World.operations changed ≡ Store.World.operations before)
  (admit : Input → Step.Registration → Maybe Diagnostic) where

  module Base = Step.For Input Diagnostic token key distinct decide keepsJournal
  Reply = Step.Result Diagnostic

  fresh : Input → Store.World → Store.World × Reply
  fresh input before with decide input before
  ... | inj₁ diagnostic = before , Step.needsInput diagnostic
  ... | inj₂ (changed , reply) = Base.firstPublication input changed reply , Step.done reply

  active : Input → Store.World → Store.World × Reply
  active input before with Store.lookupSaved before (token input) (key input)
    | Store.lookupSaved before (token input) (nextKey input)
    | Store.lookupSaved before (token input) Step.resultKey
  ... | just saved | nothing | nothing = before , Step.done saved
  ... | just saved | just _ | just _ = before , Step.done saved
  ... | just _ | nothing | just _ = before , Step.needsRecovery
  ... | just _ | just _ | nothing = before , Step.needsRecovery
  ... | nothing | nothing | nothing = fresh input before
  ... | nothing | nothing | just _ = before , Step.needsRecovery
  ... | nothing | just _ | nothing = before , Step.needsRecovery
  ... | nothing | just _ | just _ = before , Step.needsRecovery

  admitted : Input → Store.World → Store.World × Reply
  admitted input before with Store.lookupCancellation before (token input)
  ... | just cancelled = before , Step.cancelled cancelled
  ... | nothing = active input before

  execute : Input → Store.World → Store.World × Reply
  execute input before with admit input (Step.registration before)
  ... | just diagnostic = before , Step.needsInput diagnostic
  ... | nothing = admitted input before

  keepsRegistration : ∀ input before changed reply → decide input before ≡ inj₂ (changed , reply) →
    Step.registration (Base.firstPublication input changed reply) ≡ Step.registration before
  keepsRegistration input before changed reply accepted = trans
    (Store.savingAnswerPreservesOperationInputs changed (token input) (key input) reply)
    (cong (λ tables → Store.OperationTables.reservations tables , Store.OperationTables.requestKeys tables ,
      Store.OperationTables.bindings tables , Store.OperationTables.plans tables)
      (keepsJournal input before changed reply accepted))

  keepsCancellation : ∀ input before changed reply → decide input before ≡ inj₂ (changed , reply) →
    Store.lookupCancellation (Base.firstPublication input changed reply) (token input) ≡
      Store.lookupCancellation before (token input)
  keepsCancellation input before changed reply accepted = trans
    (Store.savingAnswerPreservesCancellation changed (token input) (key input) reply (token input))
    (cong (λ tables → Store.lookupCancellationRows (token input) (Store.OperationTables.cancellations tables))
      (keepsJournal input before changed reply accepted))

  keepsNext : ∀ input before changed reply → decide input before ≡ inj₂ (changed , reply) →
    Store.lookupSaved (Base.firstPublication input changed reply) (token input) (nextKey input) ≡
      Store.lookupSaved before (token input) (nextKey input)
  keepsNext input before changed reply accepted = trans
    (Store.otherSavedAnswerPreserved changed (token input) (key input) reply (token input) (nextKey input)
      (λ same → different input (sym (proj₂ same))))
    (Base.changedLookup input before changed reply (nextKey input) accepted)

  stable : ∀ input before → execute input (proj₁ (execute input before)) ≡ execute input before
  stable input before with admit input (Step.registration before) in admission
  ... | just diagnostic rewrite admission = refl
  ... | nothing with Store.lookupCancellation before (token input) in cancellation
  ... | just cancelled rewrite admission | cancellation = refl
  ... | nothing with Store.lookupSaved before (token input) (key input) in firstSaved
    | Store.lookupSaved before (token input) (nextKey input) in secondSaved
    | Store.lookupSaved before (token input) Step.resultKey in resultSaved
  ... | just saved | nothing | nothing rewrite admission | cancellation | firstSaved | secondSaved | resultSaved = refl
  ... | just saved | just _ | just _ rewrite admission | cancellation | firstSaved | secondSaved | resultSaved = refl
  ... | just _ | nothing | just _ rewrite admission | cancellation | firstSaved | secondSaved | resultSaved = refl
  ... | just _ | just _ | nothing rewrite admission | cancellation | firstSaved | secondSaved | resultSaved = refl
  ... | nothing | nothing | just _ rewrite admission | cancellation | firstSaved | secondSaved | resultSaved = refl
  ... | nothing | just _ | nothing rewrite admission | cancellation | firstSaved | secondSaved | resultSaved = refl
  ... | nothing | just _ | just _ rewrite admission | cancellation | firstSaved | secondSaved | resultSaved = refl
  ... | nothing | nothing | nothing with decide input before in accepted
  ... | inj₁ diagnostic rewrite admission | cancellation | firstSaved | secondSaved | resultSaved | accepted = refl
  ... | inj₂ (changed , reply)
    rewrite keepsRegistration input before changed reply accepted | admission
      | keepsCancellation input before changed reply accepted | cancellation
      | Base.firstReadable input before changed reply accepted firstSaved
      | keepsNext input before changed reply accepted | secondSaved
      | Base.firstHasNoResult input before changed reply accepted resultSaved = refl

  expectedPhysical : ∀ input before → DB.Atomic before (proj₁ (execute input before))
    (Step.receiptFor (proj₂ (execute input before))) (proj₁ (execute input before))
  expectedPhysical input before with admit input (Step.registration before)
  ... | just _ = DB.abortedNone
  ... | nothing with Store.lookupCancellation before (token input)
  ... | just _ = DB.abortedNone
  ... | nothing with Store.lookupSaved before (token input) (key input)
    | Store.lookupSaved before (token input) (nextKey input) | Store.lookupSaved before (token input) Step.resultKey
  ... | just _ | nothing | nothing = DB.committedAll
  ... | just _ | just _ | just _ = DB.committedAll
  ... | just _ | nothing | just _ = DB.abortedNone
  ... | just _ | just _ | nothing = DB.abortedNone
  ... | nothing | nothing | just _ = DB.abortedNone
  ... | nothing | just _ | nothing = DB.abortedNone
  ... | nothing | just _ | just _ = DB.abortedNone
  ... | nothing | nothing | nothing with decide input before
  ... | inj₁ _ = DB.abortedNone
  ... | inj₂ _ = DB.committedAll

module TwoPhases (Input Diagnostic : Set)
  (first second : Input → Store.World → Store.World × Step.Result Diagnostic)
  (firstStable : ∀ input before → first input (proj₁ (first input before)) ≡ first input before)
  (secondStable : ∀ input before → second input (proj₁ (second input before)) ≡ second input before)
  (firstPhysical : ∀ input before → DB.Atomic before (proj₁ (first input before))
    (Step.receiptFor (proj₂ (first input before))) (proj₁ (first input before)))
  (secondPhysical : ∀ input before → DB.Atomic before (proj₁ (second input before))
    (Step.receiptFor (proj₂ (second input before))) (proj₁ (second input before))) where

  Reply = Step.Result Diagnostic
  module First = Step.AtomicStep Input Diagnostic first firstStable firstPhysical
  module Second = Step.AtomicStep Input Diagnostic second secondStable secondPhysical

  data Effect : Set where
    prefix finish : Input → Effect

  Atomic : Store.World → Effect → Reply → Store.World → Set
  Atomic before (prefix input) = First.Atomic before input
  Atomic before (finish input) = Second.Atomic before input

  module X = Recovery.Execution Store.World Effect (λ _ → Reply) Atomic
  module E = X.E

  tail : Input → Reply → E.Script Reply
  tail input (Step.done _) = E.ask (finish input) E.done
  tail input reply@(Step.needsInput _) = E.done reply
  tail input Step.needsRecovery = E.done Step.needsRecovery
  tail input reply@(Step.cancelled _) = E.done reply

  script : Input → E.Script Reply
  script input = E.ask (prefix input) (tail input)

  remaining : Input → Reply → Store.World → Store.World × Reply
  remaining input (Step.done _) before = second input before
  remaining input reply@(Step.needsInput _) before = before , reply
  remaining input Step.needsRecovery before = before , Step.needsRecovery
  remaining input reply@(Step.cancelled _) before = before , reply

  evaluate : Input → Store.World → Store.World × Reply
  evaluate input before = remaining input (proj₂ proposed) (proj₁ proposed)
    where proposed = first input before

  tailObservation : ∀ input middle previous {events} after reply →
    E.Runs (tail input previous) events reply → X.Changes middle events after →
    (after , reply) ≡ remaining input previous middle
  tailObservation input middle (Step.done _) after reply
    (E.replied _ _ _ (E.returned _))
    (X.changed _ _ _ _ physical (X.unchanged _)) =
    Second.atomicObservation input middle after reply physical
  tailObservation input middle (Step.needsInput diagnostic) .middle .(Step.needsInput diagnostic)
    (E.returned _) (X.unchanged _) = refl
  tailObservation input middle Step.needsRecovery .middle .Step.needsRecovery
    (E.returned _) (X.unchanged _) = refl
  tailObservation input middle (Step.cancelled cancellation) .middle .(Step.cancelled cancellation)
    (E.returned _) (X.unchanged _) = refl

  completedObservation : ∀ input before after reply →
    X.Completed (script input) before after reply → (after , reply) ≡ evaluate input before
  completedObservation input before after reply
    (X.completed _ (E.replied _ _ previous execution)
      (X.changed _ _ _ middle physical rest)) =
    trans (tailObservation input middle previous after reply execution rest)
      (cong (λ pair → remaining input (proj₂ pair) (proj₁ pair))
        (First.atomicObservation input before middle previous physical))

  data Owned (input : Input) : Effect → Set where
    firstOwned : Owned input (prefix input)
    secondOwned : Owned input (finish input)

  data Scoped (input : Input) : E.Script Reply → Set where
    returned : ∀ reply → Scoped input (E.done reply)
    asked : ∀ effect continuation → Owned input effect →
      (∀ reply → Scoped input (continuation reply)) → Scoped input (E.ask effect continuation)

  tailScoped : ∀ input previous → Scoped input (tail input previous)
  tailScoped input (Step.done _) = asked (finish input) E.done secondOwned returned
  tailScoped input (Step.needsInput diagnostic) = returned _
  tailScoped input Step.needsRecovery = returned _
  tailScoped input (Step.cancelled cancellation) = returned _

  scriptScoped : ∀ input → Scoped input (script input)
  scriptScoped input = asked (prefix input) (tail input) firstOwned (tailScoped input)

  prefixScoped : ∀ input program events residual → Scoped input program →
    E.Prefix program events residual →
    All (λ event → Owned input (proj₁ event)) events × Scoped input residual
  prefixScoped input program [] .program scoped (E.stopped _) = [] , scoped
  prefixScoped input .(E.ask effect continuation) .((effect , reply) ∷ events) residual
    (asked effect continuation owner later) (E.replied _ _ reply {events} rest)
    with prefixScoped input (continuation reply) events residual (later reply) rest
  ... | owners , scoped = owner ∷ owners , scoped

  activeOwned : ∀ input effect continuation → Scoped input (E.ask effect continuation) → Owned input effect
  activeOwned input effect continuation (asked .effect .continuation owner later) = owner

  -- Concrete operations must prove these laws for their saved receipts.
  -- They cannot omit a phase or replace its physical database semantics.
  module Invariant
    (firstKeepsOutcome : ∀ input before → evaluate input (proj₁ (first input before)) ≡ evaluate input before)
    (secondKeepsOutcome : ∀ input before → evaluate input (proj₁ (second input before)) ≡ evaluate input before) where

    atomicInvariant : ∀ input effect before after reply → Owned input effect →
      Atomic before effect reply after → evaluate input after ≡ evaluate input before
    atomicInvariant input .(prefix input) before after reply firstOwned physical =
      trans (cong (evaluate input) (cong proj₁ (First.atomicObservation input before after reply physical)))
        (firstKeepsOutcome input before)
    atomicInvariant input .(finish input) before after reply secondOwned physical =
      trans (cong (evaluate input) (cong proj₁ (Second.atomicObservation input before after reply physical)))
        (secondKeepsOutcome input before)

    changesInvariant : ∀ input before events after → All (λ event → Owned input (proj₁ event)) events →
      X.Changes before events after → evaluate input after ≡ evaluate input before
    changesInvariant input before [] .before [] (X.unchanged _) = refl
    changesInvariant input before ((effect , reply) ∷ events) after (owner ∷ owners)
      (X.changed _ _ _ middle physical rest) = trans
        (changesInvariant input middle events after owners rest)
        (atomicInvariant input effect before middle reply owner physical)

    interruptedInvariant : ∀ input initial interrupted →
      X.Interrupted (script input) initial interrupted → evaluate input interrupted ≡ evaluate input initial
    interruptedInvariant input initial interrupted (X.atPrefix events residual .interrupted observedPrefix physical) =
      changesInvariant input initial events interrupted
        (proj₁ (prefixScoped input (script input) events residual (scriptScoped input) observedPrefix)) physical
    interruptedInvariant input initial interrupted
      (X.beforeReply events effect continuation current reply .interrupted observedPrefix physical active)
      with prefixScoped input (script input) events (E.ask effect continuation) (scriptScoped input) observedPrefix
    ... | owners , residual = trans
      (atomicInvariant input effect current interrupted reply (activeOwned input effect continuation residual) active)
      (changesInvariant input initial events current owners physical)

  tailProgress : ∀ input before previous →
    X.Completed (tail input previous) before
      (proj₁ (remaining input previous before)) (proj₂ (remaining input previous before))
  tailProgress input before (Step.done _) = X.completed _
    (E.replied (finish input) E.done _ (E.returned _))
    (X.changed before (finish input) _ _ (refl , secondPhysical input before) (X.unchanged _))
  tailProgress input before (Step.needsInput diagnostic) = X.completed [] (E.returned _) (X.unchanged _)
  tailProgress input before Step.needsRecovery = X.completed [] (E.returned _) (X.unchanged _)
  tailProgress input before (Step.cancelled cancellation) = X.completed [] (E.returned _) (X.unchanged _)

  progress : ∀ input initial → Σ Store.World (λ final → Σ Reply (λ reply →
    X.Completed (script input) initial final reply))
  progress input initial with tailProgress input (proj₁ (first input initial)) (proj₂ (first input initial))
  ... | X.completed events execution physical =
    proj₁ (evaluate input initial) , proj₂ (evaluate input initial) ,
    X.completed ((prefix input , proj₂ (first input initial)) ∷ events)
      (E.replied (prefix input) (tail input) (proj₂ (first input initial)) execution)
      (X.changed initial (prefix input) (proj₂ (first input initial)) (proj₁ (first input initial))
        (refl , firstPhysical input initial) physical)

  -- Both physical boundaries cover commit, abort and either possible state
  -- after acknowledgement loss. A later phase is never treated as one commit
  -- with the already durable prefix.
  firstReceiptCovered : ∀ input before tag actual →
    DB.Atomic before (proj₁ (first input before)) tag actual →
    X.Interrupted (script input) before actual
  firstReceiptCovered input before .DB.committed _ DB.committedAll =
    X.beforeReply [] (prefix input) (tail input) before (proj₂ (first input before)) _
      (E.stopped _) (X.unchanged before) (refl , firstPhysical input before)
  firstReceiptCovered input before .DB.aborted _ DB.abortedNone =
    X.atPrefix [] (script input) before (E.stopped _) (X.unchanged before)
  firstReceiptCovered input before .DB.acknowledgementLost _ DB.unknownBefore =
    X.atPrefix [] (script input) before (E.stopped _) (X.unchanged before)
  firstReceiptCovered input before .DB.acknowledgementLost _ DB.unknownAfter =
    X.beforeReply [] (prefix input) (tail input) before (proj₂ (first input before)) _
      (E.stopped _) (X.unchanged before) (refl , firstPhysical input before)

  firstCommitted : ∀ input before value → proj₂ (first input before) ≡ Step.done value →
    X.Changes before ((prefix input , Step.done value) ∷ []) (proj₁ (first input before))
  firstCommitted input before value observed =
    X.changed before (prefix input) (Step.done value) (proj₁ (first input before))
      (sym observed , subst (λ reply → DB.Atomic before (proj₁ (first input before))
        (Step.receiptFor reply) (proj₁ (first input before))) observed (firstPhysical input before))
      (X.unchanged _)

  afterFirst : ∀ input value → E.Prefix (script input)
    ((prefix input , Step.done value) ∷ []) (E.ask (finish input) E.done)
  afterFirst input value = E.replied (prefix input) (tail input) (Step.done value) (E.stopped _)

  secondReceiptCovered : ∀ input before value tag actual →
    proj₂ (first input before) ≡ Step.done value →
    DB.Atomic (proj₁ (first input before))
      (proj₁ (second input (proj₁ (first input before)))) tag actual →
    X.Interrupted (script input) before actual
  secondReceiptCovered input before value .DB.committed _ observed DB.committedAll =
    X.beforeReply ((prefix input , Step.done value) ∷ []) (finish input) E.done
      (proj₁ (first input before)) (proj₂ (second input (proj₁ (first input before)))) _
      (afterFirst input value) (firstCommitted input before value observed)
      (refl , secondPhysical input (proj₁ (first input before)))
  secondReceiptCovered input before value .DB.aborted _ observed DB.abortedNone =
    X.atPrefix ((prefix input , Step.done value) ∷ []) (E.ask (finish input) E.done) _
      (afterFirst input value) (firstCommitted input before value observed)
  secondReceiptCovered input before value .DB.acknowledgementLost _ observed DB.unknownBefore =
    X.atPrefix ((prefix input , Step.done value) ∷ []) (E.ask (finish input) E.done) _
      (afterFirst input value) (firstCommitted input before value observed)
  secondReceiptCovered input before value .DB.acknowledgementLost _ observed DB.unknownAfter =
    X.beforeReply ((prefix input , Step.done value) ∷ []) (finish input) E.done
      (proj₁ (first input before)) (proj₂ (second input (proj₁ (first input before)))) _
      (afterFirst input value) (firstCommitted input before value observed)
      (refl , secondPhysical input (proj₁ (first input before)))

  module Certified
    (firstKeepsOutcome : ∀ input before → evaluate input (proj₁ (first input before)) ≡ evaluate input before)
    (secondKeepsOutcome : ∀ input before → evaluate input (proj₁ (second input before)) ≡ evaluate input before)
    (Goal : Input → Store.World → Store.World → Reply → Set)
    (meaning : ∀ input before → Goal input before (proj₁ (evaluate input before)) (proj₂ (evaluate input before))) where
    module I = Invariant firstKeepsOutcome secondKeepsOutcome

    fromObservation : ∀ input before after reply → (after , reply) ≡ evaluate input before → Goal input before after reply
    fromObservation input before after reply observed = subst
      (λ result → Goal input before (proj₁ result) (proj₂ result)) (sym observed) (meaning input before)

    converges : ∀ input initial interrupted final reply →
      X.Interrupted (script input) initial interrupted → X.Completed (script input) interrupted final reply →
      Goal input initial final reply
    converges input initial interrupted final reply interruption completion =
      fromObservation input initial final reply
        (trans (completedObservation input interrupted final reply completion)
          (I.interruptedInvariant input initial interrupted interruption))

    operation : Recovery.RecoverableFor Store.World Input Reply Goal
    operation = record
      { Effect = Effect; Reply = λ _ → Reply; script = script; Atomic = Atomic
      ; converges = converges; progress = progress }
