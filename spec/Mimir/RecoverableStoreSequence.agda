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
open import Data.Unit using (⊤; tt)
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

-- Pure semantic bridge for already observed statement metadata. This is not
-- an executor and exposes neither a script nor a Recoverable certificate.
module Evaluation (Input Diagnostic : Set)
  (first second : Input → Store.World → Store.World × Step.Result Diagnostic) where
  Reply = Step.Result Diagnostic
  remaining : Input → Reply → Store.World → Store.World × Reply
  remaining input (Step.done _) before = second input before
  remaining input reply@(Step.needsInput _) before = before , reply
  remaining input Step.needsRecovery before = before , Step.needsRecovery
  remaining input reply@(Step.cancelled _) before = before , reply
  evaluate : Input → Store.World → Store.World × Reply
  evaluate input before = remaining input (proj₂ proposed) (proj₁ proposed)
    where proposed = first input before

-- Each transaction supplies its own physical metadata in its reply. Neither
-- statement time belongs to the public request or to the other transaction.
module ObservedTwoPhases (Input FirstMetadata SecondMetadata Diagnostic : Set)
  (first : FirstMetadata → Input → Store.World → Store.World × Step.Result Diagnostic)
  (second : SecondMetadata → Input → Store.World → Store.World × Step.Result Diagnostic)
  (firstStable : ∀ metadata input before →
    first metadata input (proj₁ (first metadata input before)) ≡ first metadata input before)
  (secondStable : ∀ metadata input before →
    second metadata input (proj₁ (second metadata input before)) ≡ second metadata input before)
  (firstPhysical : ∀ metadata input before → DB.Atomic before (proj₁ (first metadata input before))
    (Step.receiptFor (proj₂ (first metadata input before))) (proj₁ (first metadata input before)))
  (secondPhysical : ∀ metadata input before → DB.Atomic before (proj₁ (second metadata input before))
    (Step.receiptFor (proj₂ (second metadata input before))) (proj₁ (second metadata input before)))
  (firstAvailable : Input → Store.World → FirstMetadata)
  (secondAvailable : Input → Store.World → SecondMetadata) where

  Value = Step.Result Diagnostic
  module First metadata = Step.AtomicStep Input Diagnostic (first metadata)
    (firstStable metadata) (firstPhysical metadata)
  module Second metadata = Step.AtomicStep Input Diagnostic (second metadata)
    (secondStable metadata) (secondPhysical metadata)
  data Effect : Set where prefix finish : Input → Effect
  Reply : Effect → Set
  Reply (prefix _) = FirstMetadata × Value
  Reply (finish _) = SecondMetadata × Value
  Atomic : Store.World → (effect : Effect) → Reply effect → Store.World → Set
  Atomic before (prefix input) (metadata , reply) after = First.Atomic metadata before input reply after
  Atomic before (finish input) (metadata , reply) after = Second.Atomic metadata before input reply after
  module X = Recovery.Execution Store.World Effect Reply Atomic
  module E = X.E
  returnedValue : SecondMetadata × Value → E.Script Value
  returnedValue observed = E.done (proj₂ observed)
  tail : Input → Value → E.Script Value
  tail input (Step.done _) = E.ask (finish input) returnedValue
  tail input value@(Step.needsInput _) = E.done value
  tail input Step.needsRecovery = E.done Step.needsRecovery
  tail input value@(Step.cancelled _) = E.done value
  script : Input → E.Script Value
  script input = E.ask (prefix input) (λ observed → tail input (proj₂ observed))
  remaining : SecondMetadata → Input → Value → Store.World → Store.World × Value
  remaining final input (Step.done _) before = second final input before
  remaining final input reply@(Step.needsInput _) before = before , reply
  remaining final input Step.needsRecovery before = before , Step.needsRecovery
  remaining final input reply@(Step.cancelled _) before = before , reply
  evaluate : FirstMetadata → SecondMetadata → Input → Store.World → Store.World × Value
  evaluate initial final input before = remaining final input (proj₂ proposed) (proj₁ proposed)
    where proposed = first initial input before
  firstKeepsFamily :
    (∀ earlier later input before → first later input (proj₁ (first earlier input before)) ≡ first earlier input before) →
    ∀ earlier later final input before →
    evaluate later final input (proj₁ (first earlier input before)) ≡ evaluate earlier final input before
  firstKeepsFamily cross earlier later final input before =
    cong (λ pair → remaining final input (proj₂ pair) (proj₁ pair)) (cross earlier later input before)

  tailObservation : ∀ input middle previous {events} after reply →
    E.Runs (tail input previous) events reply → X.Changes middle events after →
    Σ SecondMetadata (λ final → (after , reply) ≡ remaining final input previous middle)
  tailObservation input middle (Step.done _) after reply
    (E.replied _ _ (metadata , _) (E.returned _)) (X.changed _ _ _ _ physical (X.unchanged _)) =
    metadata , Second.atomicObservation metadata input middle after reply physical
  tailObservation input middle (Step.needsInput diagnostic) .middle .(Step.needsInput diagnostic)
    (E.returned _) (X.unchanged _) = secondAvailable input middle , refl
  tailObservation input middle Step.needsRecovery .middle .Step.needsRecovery
    (E.returned _) (X.unchanged _) = secondAvailable input middle , refl
  tailObservation input middle (Step.cancelled cancellation) .middle .(Step.cancelled cancellation)
    (E.returned _) (X.unchanged _) = secondAvailable input middle , refl
  completedObservation : ∀ input before after reply → X.Completed (script input) before after reply →
    Σ FirstMetadata (λ initial → Σ SecondMetadata (λ final → (after , reply) ≡ evaluate initial final input before))
  completedObservation input before after reply
    (X.completed _ (E.replied _ _ (metadata , previous) execution) (X.changed _ _ _ middle physical rest))
    with tailObservation input middle previous after reply execution rest
  ... | final , observed = metadata , final , trans observed
    (cong (λ pair → remaining final input (proj₂ pair) (proj₁ pair))
      (First.atomicObservation metadata input before middle previous physical))

  data Owned (input : Input) : Effect → Set where
    firstOwned : Owned input (prefix input)
    secondOwned : Owned input (finish input)
  data Scoped (input : Input) : E.Script Value → Set where
    returned : ∀ reply → Scoped input (E.done reply)
    asked : ∀ effect continuation → Owned input effect →
      (∀ reply → Scoped input (continuation reply)) → Scoped input (E.ask effect continuation)
  tailScoped : ∀ input previous → Scoped input (tail input previous)
  tailScoped input (Step.done _) = asked (finish input) returnedValue secondOwned (λ observed → returned (proj₂ observed))
  tailScoped input (Step.needsInput _) = returned _
  tailScoped input Step.needsRecovery = returned _
  tailScoped input (Step.cancelled _) = returned _
  scriptScoped : ∀ input → Scoped input (script input)
  scriptScoped input = asked (prefix input) _ firstOwned (λ observed → tailScoped input (proj₂ observed))
  prefixScoped : ∀ input program events residual → Scoped input program → E.Prefix program events residual →
    All (λ event → Owned input (proj₁ event)) events × Scoped input residual
  prefixScoped input program [] .program scoped (E.stopped _) = [] , scoped
  prefixScoped input .(E.ask effect continuation) .((effect , reply) ∷ events) residual
    (asked effect continuation owner later) (E.replied _ _ reply {events} rest)
    with prefixScoped input (continuation reply) events residual (later reply) rest
  ... | owners , scoped = (owner ∷ owners) , scoped
  activeOwned : ∀ input effect continuation → Scoped input (E.ask effect continuation) → Owned input effect
  activeOwned input effect continuation (asked .effect .continuation owner later) = owner

  module Certified
    (firstFamilyPreserved : ∀ wantedFirst wantedFinal received input before →
      Σ FirstMetadata (λ originalFirst → Σ SecondMetadata (λ originalFinal →
        evaluate wantedFirst wantedFinal input (proj₁ (first received input before)) ≡ evaluate originalFirst originalFinal input before)))
    (secondKeepsFamily : ∀ initial wanted received input before → Σ SecondMetadata (λ original →
      evaluate initial wanted input (proj₁ (second received input before)) ≡ evaluate initial original input before))
    (Goal : Input → Store.World → Store.World → Value → Set)
    (meaning : ∀ initial final input before → Goal input before
      (proj₁ (evaluate initial final input before)) (proj₂ (evaluate initial final input before))) where
    Invariant : Input → Store.World → Store.World → Set
    Invariant input initial current = ∀ firstWanted finalWanted → Σ FirstMetadata (λ firstOriginal → Σ SecondMetadata (λ finalOriginal →
      evaluate firstWanted finalWanted input current ≡ evaluate firstOriginal finalOriginal input initial))
    atomicInvariant : ∀ input initial before after effect reply → Owned input effect →
      Atomic before effect reply after → Invariant input initial before → Invariant input initial after
    atomicInvariant input initial before after .(prefix input) (metadata , reply) firstOwned physical old firstWanted finalWanted
      with firstFamilyPreserved firstWanted finalWanted metadata input before
    ... | priorFirst , priorFinal , retained with old priorFirst priorFinal
    ... | original , final , same = original , final , trans
      (cong (evaluate firstWanted finalWanted input) (cong proj₁ (First.atomicObservation metadata input before after reply physical)))
      (trans retained same)
    atomicInvariant input initial before after .(finish input) (metadata , reply) secondOwned physical old firstWanted finalWanted
      with secondKeepsFamily firstWanted finalWanted metadata input before
    ... | prior , retained with old firstWanted prior
    ... | original , final , same = original , final , trans
      (cong (evaluate firstWanted finalWanted input) (cong proj₁ (Second.atomicObservation metadata input before after reply physical)))
      (trans retained same)
    changesInvariant : ∀ input initial before events after → All (λ event → Owned input (proj₁ event)) events →
      X.Changes before events after → Invariant input initial before → Invariant input initial after
    changesInvariant input initial before [] .before [] (X.unchanged _) old = old
    changesInvariant input initial before ((effect , reply) ∷ events) after (owner ∷ owners)
      (X.changed _ _ _ middle physical rest) old = changesInvariant input initial middle events after owners rest
        (atomicInvariant input initial before middle effect reply owner physical old)
    interruptedInvariant : ∀ input initial interrupted → X.Interrupted (script input) initial interrupted →
      Invariant input initial interrupted
    interruptedInvariant input initial interrupted (X.atPrefix events residual .interrupted observedPrefix physical) =
      changesInvariant input initial initial events interrupted
        (proj₁ (prefixScoped input (script input) events residual (scriptScoped input) observedPrefix)) physical
        (λ first final → first , final , refl)
    interruptedInvariant input initial interrupted
      (X.beforeReply events effect continuation current reply .interrupted observedPrefix physical active)
      with prefixScoped input (script input) events (E.ask effect continuation) (scriptScoped input) observedPrefix
    ... | owners , residual = atomicInvariant input initial current interrupted effect reply
      (activeOwned input effect continuation residual) active
      (changesInvariant input initial initial events current owners physical (λ first final → first , final , refl))
    converges : ∀ input initial interrupted after reply → X.Interrupted (script input) initial interrupted →
      X.Completed (script input) interrupted after reply → Goal input initial after reply
    converges input initial interrupted after reply crash completion
      with completedObservation input interrupted after reply completion
    ... | first , final , observed with interruptedInvariant input initial interrupted crash first final
    ... | original , originalFinal , same = subst (λ pair → Goal input initial (proj₁ pair) (proj₂ pair))
      (sym (trans observed same)) (meaning original originalFinal input initial)
    tailProgress : ∀ input before previous → Σ SecondMetadata (λ final → X.Completed (tail input previous) before
      (proj₁ (remaining final input previous before)) (proj₂ (remaining final input previous before)))
    tailProgress input before (Step.done _) with secondAvailable input before
    ... | metadata = metadata , X.completed _
      (E.replied (finish input) returnedValue (metadata , _) (E.returned _))
      (X.changed before (finish input) _ _ (refl , secondPhysical metadata input before) (X.unchanged _))
    tailProgress input before (Step.needsInput diagnostic) = secondAvailable input before , X.completed [] (E.returned _) (X.unchanged _)
    tailProgress input before Step.needsRecovery = secondAvailable input before , X.completed [] (E.returned _) (X.unchanged _)
    tailProgress input before (Step.cancelled cancellation) = secondAvailable input before , X.completed [] (E.returned _) (X.unchanged _)
    progress : ∀ input initial → Σ Store.World (λ after → Σ Value (λ reply → X.Completed (script input) initial after reply))
    progress input initial with firstAvailable input initial
    ... | metadata with tailProgress input (proj₁ (first metadata input initial)) (proj₂ (first metadata input initial))
    ... | final , X.completed events execution physical = proj₁ (evaluate metadata final input initial) , proj₂ (evaluate metadata final input initial) ,
      X.completed ((prefix input , (metadata , proj₂ (first metadata input initial))) ∷ events)
        (E.replied (prefix input) _ (metadata , proj₂ (first metadata input initial)) execution)
        (X.changed initial (prefix input) _ _ (refl , firstPhysical metadata input initial) physical)
    operation : Recovery.RecoverableFor Store.World Input Value Goal
    operation = record { Effect = Effect; Reply = Reply; script = script; Atomic = Atomic; progress = progress; converges = converges }

  firstReceiptCovered : ∀ metadata input before tag actual →
    DB.Atomic before (proj₁ (first metadata input before)) tag actual → X.Interrupted (script input) before actual
  firstReceiptCovered metadata input before .DB.committed _ DB.committedAll =
    X.beforeReply [] (prefix input) _ before (metadata , proj₂ (first metadata input before)) _
      (E.stopped _) (X.unchanged before) (refl , firstPhysical metadata input before)
  firstReceiptCovered metadata input before .DB.aborted _ DB.abortedNone = X.atPrefix [] _ before (E.stopped _) (X.unchanged before)
  firstReceiptCovered metadata input before .DB.acknowledgementLost _ DB.unknownBefore = X.atPrefix [] _ before (E.stopped _) (X.unchanged before)
  firstReceiptCovered metadata input before .DB.acknowledgementLost _ DB.unknownAfter =
    X.beforeReply [] (prefix input) _ before (metadata , proj₂ (first metadata input before)) _
      (E.stopped _) (X.unchanged before) (refl , firstPhysical metadata input before)

  firstCommitted : ∀ metadata input before value → proj₂ (first metadata input before) ≡ Step.done value →
    X.Changes before ((prefix input , (metadata , Step.done value)) ∷ []) (proj₁ (first metadata input before))
  firstCommitted metadata input before value observed =
    X.changed before (prefix input) (metadata , Step.done value) _
      (sym observed , subst (λ reply → DB.Atomic before (proj₁ (first metadata input before))
        (Step.receiptFor reply) (proj₁ (first metadata input before))) observed (firstPhysical metadata input before))
      (X.unchanged _)

  afterFirst : ∀ metadata input value → E.Prefix (script input)
    ((prefix input , (metadata , Step.done value)) ∷ []) (E.ask (finish input) returnedValue)
  afterFirst metadata input value = E.replied (prefix input) _ (metadata , Step.done value) (E.stopped _)

  secondReceiptCovered : ∀ initial final input before value tag actual →
    proj₂ (first initial input before) ≡ Step.done value →
    DB.Atomic (proj₁ (first initial input before))
      (proj₁ (second final input (proj₁ (first initial input before)))) tag actual →
    X.Interrupted (script input) before actual
  secondReceiptCovered initial final input before value .DB.committed _ observed DB.committedAll =
    X.beforeReply ((prefix input , (initial , Step.done value)) ∷ []) (finish input) returnedValue _
      (final , proj₂ (second final input (proj₁ (first initial input before)))) _
      (afterFirst initial input value) (firstCommitted initial input before value observed)
      (refl , secondPhysical final input (proj₁ (first initial input before)))
  secondReceiptCovered initial final input before value .DB.aborted _ observed DB.abortedNone =
    X.atPrefix _ (E.ask (finish input) returnedValue) _ (afterFirst initial input value)
      (firstCommitted initial input before value observed)
  secondReceiptCovered initial final input before value .DB.acknowledgementLost _ observed DB.unknownBefore =
    X.atPrefix _ (E.ask (finish input) returnedValue) _ (afterFirst initial input value)
      (firstCommitted initial input before value observed)
  secondReceiptCovered initial final input before value .DB.acknowledgementLost _ observed DB.unknownAfter =
    X.beforeReply ((prefix input , (initial , Step.done value)) ∷ []) (finish input) returnedValue _
      (final , proj₂ (second final input (proj₁ (first initial input before)))) _
      (afterFirst initial input value) (firstCommitted initial input before value observed)
      (refl , secondPhysical final input (proj₁ (first initial input before)))

-- Compatibility for genuinely metadata-free phases. All execution/recovery
-- reasoning is delegated to the observed kernel, not copied into a second one.
module TwoPhases (Input Diagnostic : Set)
  (first second : Input → Store.World → Store.World × Step.Result Diagnostic)
  (firstStable : ∀ input before → first input (proj₁ (first input before)) ≡ first input before)
  (secondStable : ∀ input before → second input (proj₁ (second input before)) ≡ second input before)
  (firstPhysical : ∀ input before → DB.Atomic before (proj₁ (first input before))
    (Step.receiptFor (proj₂ (first input before))) (proj₁ (first input before)))
  (secondPhysical : ∀ input before → DB.Atomic before (proj₁ (second input before))
    (Step.receiptFor (proj₂ (second input before))) (proj₁ (second input before))) where
  module V = Evaluation Input Diagnostic first second
  open V public
  module R = ObservedTwoPhases Input ⊤ ⊤ Diagnostic (λ _ → first) (λ _ → second)
    (λ _ → firstStable) (λ _ → secondStable) (λ _ → firstPhysical) (λ _ → secondPhysical)
    (λ _ _ → tt) (λ _ _ → tt)
  remainingView : ∀ input previous before → R.remaining tt input previous before ≡ remaining input previous before
  remainingView input (Step.done _) before = refl
  remainingView input (Step.needsInput _) before = refl
  remainingView input Step.needsRecovery before = refl
  remainingView input (Step.cancelled _) before = refl
  evaluationView : ∀ input before → R.evaluate tt tt input before ≡ evaluate input before
  evaluationView input before = remainingView input (proj₂ (first input before)) (proj₁ (first input before))
  module Certified
    (firstKeepsOutcome : ∀ input before → evaluate input (proj₁ (first input before)) ≡ evaluate input before)
    (secondKeepsOutcome : ∀ input before → evaluate input (proj₁ (second input before)) ≡ evaluate input before)
    (Goal : Input → Store.World → Store.World → Reply → Set)
    (meaning : ∀ input before → Goal input before (proj₁ (evaluate input before)) (proj₂ (evaluate input before))) where
    firstFamily : ∀ (wantedFirst wantedFinal received : ⊤) input before →
      Σ ⊤ (λ originalFirst → Σ ⊤ (λ originalFinal →
        R.evaluate wantedFirst wantedFinal input (proj₁ (first input before)) ≡ R.evaluate originalFirst originalFinal input before))
    firstFamily tt tt tt input before = tt , tt , trans (evaluationView input (proj₁ (first input before)))
      (trans (firstKeepsOutcome input before) (sym (evaluationView input before)))
    secondFamily : ∀ (initial wanted received : ⊤) input before → Σ ⊤ (λ original →
      R.evaluate initial wanted input (proj₁ (second input before)) ≡ R.evaluate initial original input before)
    secondFamily tt tt tt input before = tt , trans (evaluationView input (proj₁ (second input before)))
      (trans (secondKeepsOutcome input before) (sym (evaluationView input before)))
    observedMeaning : ∀ (initial final : ⊤) input before → Goal input before
      (proj₁ (R.evaluate initial final input before)) (proj₂ (R.evaluate initial final input before))
    observedMeaning tt tt input before = subst (λ pair → Goal input before (proj₁ pair) (proj₂ pair))
      (sym (evaluationView input before)) (meaning input before)
    module C = R.Certified firstFamily secondFamily Goal observedMeaning
    operation = C.operation
