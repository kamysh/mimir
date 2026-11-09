{-# OPTIONS --safe #-}
-- The database's committing reply owns the new pattern's identity and time.
-- Neither is supplied in the public request. Retry reads the original answer.
module Mimir.PatternPublicationRecovery where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.Float.Base using (Float)
open import Data.Integer using (ℤ; +_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.String using (toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Mimir.Text using (Text)
open import Mimir.RecordDecoding using (_>>=_)
import Mimir.ApplicationStore as Store
import Mimir.CandidateGraph as Graph
import Mimir.GraphWrites as Writes
import Mimir.GraphNumerics as Numbers
import Mimir.RecoverableStoreStep as Step
import Mimir.RegisteredStoreAdmission as Admission
import Mimir.StructuredValue as Wire
import Mimir.StandardLibrary as Conversion
import Mimir.PublicEncoding as Encoding
import Mimir.PublicRequest as Public
import Mimir.PublicInput as Input
import Mimir.RecordDecoding as Decode
import Mimir.JsonObjects as Objects
import Mimir.Validation as Validation
import Mimir.Recovery as Recovery
import Mimir.DatabaseTransaction as DB

Metadata = ℕ × ℤ

record Arguments : Set where
  constructor arguments
  field situation approach : Text; success : Float; project : Maybe Text

createdPattern : Arguments → Metadata → Graph.PatternValues
createdPattern args (identity , created) = Graph.patternValues identity
  (Arguments.situation args) (Arguments.approach args) (Arguments.project args)
  created 0 (Arguments.success args)

module Registered (conversion : Conversion.Contract) (format : Encoding.Formatting) where
  module P = Public.Decode conversion
  module Encode = Encoding.Encode format
  descriptor = Admission.descriptor (toList "insert_pattern") (toList "store.insert_pattern")
    (toList "[\"store.insert_pattern\",null]")
  key : ℕ → Text
  key _ = Admission.Descriptor.key descriptor
  distinct : ∀ token → key token ≡ Step.resultKey → ⊥
  distinct token ()

  original : ℕ → Step.Registration → Validation.Fault ⊎ Arguments
  original token registration with Admission.resolve descriptor token registration
  ... | inj₁ fault = inj₁ fault
  ... | inj₂ (_ , binding) with Store.BindingRow.settings binding
  ... | Wire.object [] = Decode.readRecord Objects.forbid Objects.rejectKnownRepeated
    (toList "situation" ∷ toList "approach" ∷ toList "success_rate" ∷ toList "project" ∷ [])
    (λ view → Input.required "situation" Wire.asString view >>= λ situation →
      Input.required "approach" Wire.asString view >>= λ approach →
      Input.required "success_rate" P.unitProbability view >>= λ success →
      Input.present "project" Wire.asString view >>= λ project →
      inj₂ (arguments situation approach success project)) (Store.BindingRow.arguments binding)
  ... | _ = inj₁ (Validation.fault (Validation.key "settings" ∷ []) Validation.unknownField
    "Pattern creation has no per-request settings. Read the original binding and outcome; ask the user to resolve this token before changing its request.")

  Internal = ℕ × Metadata
  admit : Internal → Step.Registration → Maybe Validation.Fault
  admit (token , metadata) registration with original token registration
  ... | inj₁ fault = just fault
  ... | inj₂ _ = nothing

  decide : Internal → Store.World → Validation.Fault ⊎ (Store.World × Wire.Value)
  decide (token , metadata) before with original token (Step.registration before)
  ... | inj₁ fault = inj₁ fault
  ... | inj₂ args = inj₂ (Writes.insertPattern (createdPattern args metadata) before , Encode.patternValue (createdPattern args metadata))

  decidesBound : ∀ token metadata before args → original token (Step.registration before) ≡ inj₂ args →
    decide (token , metadata) before ≡ inj₂
      (Writes.insertPattern (createdPattern args metadata) before , Encode.patternValue (createdPattern args metadata))
  decidesBound token metadata before args bound rewrite bound = refl

  keepsJournal : ∀ input before after reply → decide input before ≡ inj₂ (after , reply) →
    Store.World.operations after ≡ Store.World.operations before
  keepsJournal (token , metadata) before after reply accepted with original token (Step.registration before)
  ... | inj₁ fault with accepted
  ... | ()
  keepsJournal (token , metadata) before ._ ._ refl | inj₂ args = refl

  module Saved = Step.Admitted Internal Validation.Fault proj₁ (λ input → key (proj₁ input))
    (λ input → distinct (proj₁ input)) decide keepsJournal admit
  module K = Saved.Kernel

  -- After any publication, every later database reply replays the same saved
  -- pattern. A second UUID/clock value cannot change the row or its answer.
  crossKernel : ∀ token first second before →
    K.execute (token , second) (proj₁ (K.execute (token , first) before)) ≡ K.execute (token , first) before
  crossKernel token first second before with Store.lookupCancellation before token in active
  ... | just cancelled rewrite active = refl
  ... | nothing with Store.lookupSaved before token (key token) in saved | Store.lookupSaved before token Step.resultKey in result
  ... | just answer | just final = K.replay (token , second) before answer final active saved result
  ... | just _ | nothing rewrite active | saved | result = refl
  ... | nothing | just _ rewrite active | saved | result = refl
  ... | nothing | nothing with original token (Step.registration before) in bound
  ... | inj₁ fault rewrite active | saved | result | bound = refl
  ... | inj₂ args = K.replay (token , second) _ _ _
    (trans (K.publicationKeepsCancellation (token , first) before _ _ (decidesBound token first before args bound)) active)
    (K.publishedStepReadable (token , first) before _ _ (decidesBound token first before args bound) saved)
    (K.publishedResultReadable (token , first) before _ _ (decidesBound token first before args bound) result)

  allowed : ∀ token metadata before args → original token (Step.registration before) ≡ inj₂ args →
    Saved.execute (token , metadata) before ≡ K.execute (token , metadata) before
  allowed token metadata before args accepted rewrite accepted = refl

  crossKnown : ∀ token first second before args → original token (Step.registration before) ≡ inj₂ args →
    Saved.execute (token , second) (proj₁ (Saved.execute (token , first) before)) ≡ Saved.execute (token , first) before
  crossKnown token first second before args bound = trans
    (cong (λ outcome → Saved.execute (token , second) (proj₁ outcome)) (allowed token first before args bound))
    (trans (allowed token second (proj₁ (K.execute (token , first) before)) args
      (trans (cong (original token) (K.registrationUnchanged (token , first) before)) bound))
      (trans (crossKernel token first second before) (sym (allowed token first before args bound))))

  refused : ∀ token metadata before fault → original token (Step.registration before) ≡ inj₁ fault →
    Saved.execute (token , metadata) before ≡ (before , Step.needsInput fault)
  refused token metadata before fault bound rewrite bound = refl

  crossRefused : ∀ token first second before fault → original token (Step.registration before) ≡ inj₁ fault →
    Saved.execute (token , second) (proj₁ (Saved.execute (token , first) before)) ≡ Saved.execute (token , first) before
  crossRefused token first second before fault bound = trans
    (cong (λ outcome → Saved.execute (token , second) (proj₁ outcome)) (refused token first before fault bound))
    (trans (refused token second before fault bound) (sym (refused token first before fault bound)))

  crossStable : ∀ token first second before →
    Saved.execute (token , second) (proj₁ (Saved.execute (token , first) before)) ≡ Saved.execute (token , first) before
  crossStable token first second before = classify (original token (Step.registration before)) refl
    where
    classify : ∀ observed → original token (Step.registration before) ≡ observed →
      Saved.execute (token , second) (proj₁ (Saved.execute (token , first) before)) ≡ Saved.execute (token , first) before
    classify (inj₁ fault) bound = crossRefused token first second before fault bound
    classify (inj₂ args) bound = crossKnown token first second before args bound

  -- A committing physical reply contains the metadata that built this exact
  -- publication. It is an effect reply, not an argument or expected row.
  Effect = ℕ
  Reply : Effect → Set
  Reply _ = Metadata × Saved.Reply
  Atomic : (before : Store.World) → (token : Effect) → Reply token → Store.World → Set
  Atomic before token (metadata , reply) after = Saved.Atomic before (token , metadata) reply after
  module X = Recovery.Execution Store.World Effect Reply Atomic
  module E = X.E

  script : ℕ → E.Script Saved.Reply
  script token = E.ask token (λ reply → E.done (proj₂ reply))

  completedObservation : ∀ token before after reply → X.Completed (script token) before after reply →
    Σ Metadata (λ metadata → (after , reply) ≡ Saved.execute (token , metadata) before)
  completedObservation token before after reply
    (X.completed _ (E.replied _ _ (metadata , .reply) (E.returned _))
      (X.changed _ _ _ _ physical (X.unchanged _))) = metadata , Saved.atomicObservation (token , metadata) before after reply physical

  interruptionState : ∀ token before interrupted → X.Interrupted (script token) before interrupted →
    interrupted ≡ before ⊎ Σ Metadata (λ metadata → interrupted ≡ proj₁ (Saved.execute (token , metadata) before))
  interruptionState token before interrupted (X.atPrefix _ _ _ (E.stopped _) (X.unchanged _)) = inj₁ refl
  interruptionState token before interrupted (X.atPrefix _ _ _ (E.replied _ _ (metadata , reply) (E.stopped _))
    (X.changed _ _ _ _ physical (X.unchanged _))) = inj₂ (metadata , cong proj₁ (Saved.atomicObservation (token , metadata) before interrupted reply physical))
  interruptionState token before interrupted (X.beforeReply _ _ _ _ (metadata , reply) _
    (E.stopped _) (X.unchanged _) physical) = inj₂ (metadata , cong proj₁ (Saved.atomicObservation (token , metadata) before interrupted reply physical))
  interruptionState token before interrupted (X.beforeReply _ _ _ _ _ _ (E.replied _ _ _ ()) changes physical)

  -- Abort and lost acknowledgement cover both physical database outcomes.
  -- This includes a committed pattern whose original answer was not received.
  everyDatabaseReceiptCovered : ∀ token metadata before tag actual →
    DB.Atomic before (proj₁ (Saved.execute (token , metadata) before)) tag actual →
    X.Interrupted (script token) before actual
  everyDatabaseReceiptCovered token metadata before .DB.committed _ DB.committedAll =
    X.beforeReply [] token (λ reply → E.done (proj₂ reply)) before
      (metadata , proj₂ (Saved.execute (token , metadata) before)) _
      (E.stopped _) (X.unchanged before) (refl , Saved.expectedPhysical (token , metadata) before)
  everyDatabaseReceiptCovered token metadata before .DB.aborted _ DB.abortedNone =
    X.atPrefix [] (script token) before (E.stopped _) (X.unchanged before)
  everyDatabaseReceiptCovered token metadata before .DB.acknowledgementLost _ DB.unknownBefore =
    X.atPrefix [] (script token) before (E.stopped _) (X.unchanged before)
  everyDatabaseReceiptCovered token metadata before .DB.acknowledgementLost _ DB.unknownAfter =
    X.beforeReply [] token (λ reply → E.done (proj₂ reply)) before
      (metadata , proj₂ (Saved.execute (token , metadata) before)) _
      (E.stopped _) (X.unchanged before) (refl , Saved.expectedPhysical (token , metadata) before)

  -- A fresh success means exactly one new pattern with the requested fields,
  -- the committing metadata, zero activations and both saved original answers.
  FreshGoal : ℕ → Arguments → Metadata → Store.World → Store.World → Saved.Reply → Set
  FreshGoal token args metadata before after reply =
    after ≡ K.publication (token , metadata) (Writes.insertPattern (createdPattern args metadata) before)
      (Encode.patternValue (createdPattern args metadata)) × reply ≡ Step.done (Encode.patternValue (createdPattern args metadata))

  freshMeaning : ∀ token args metadata before → original token (Step.registration before) ≡ inj₂ args →
    FreshGoal token args metadata before (proj₁ (K.fresh (token , metadata) before)) (proj₂ (K.fresh (token , metadata) before))
  freshMeaning token args metadata before bound rewrite decidesBound token metadata before args bound = refl , refl

  ObservedGoal : ℕ → Metadata → Store.World → Store.World → Saved.Reply → Set
  ObservedGoal token metadata before after reply with original token (Step.registration before)
  ... | inj₁ fault = after ≡ before × reply ≡ Step.needsInput fault
  ... | inj₂ args with Store.lookupCancellation before token
  ... | just cancelled = after ≡ before × reply ≡ Step.cancelled cancelled
  ... | nothing with Store.lookupSaved before token (key token) | Store.lookupSaved before token Step.resultKey
  ... | just saved | just _ = after ≡ before × reply ≡ Step.done saved
  ... | just _ | nothing = after ≡ before × reply ≡ Step.needsRecovery
  ... | nothing | just _ = after ≡ before × reply ≡ Step.needsRecovery
  ... | nothing | nothing = FreshGoal token args metadata before after reply

  meaning : ∀ token metadata before → ObservedGoal token metadata before
    (proj₁ (Saved.execute (token , metadata) before)) (proj₂ (Saved.execute (token , metadata) before))
  meaning token metadata before with original token (Step.registration before) in bound
  ... | inj₁ fault = refl , refl
  ... | inj₂ args with Store.lookupCancellation before token
  ... | just cancelled = refl , refl
  ... | nothing with Store.lookupSaved before token (key token) | Store.lookupSaved before token Step.resultKey
  ... | just saved | just _ = refl , refl
  ... | just _ | nothing = refl , refl
  ... | nothing | just _ = refl , refl
  ... | nothing | nothing = freshMeaning token args metadata before bound

  Goal : ℕ → Store.World → Store.World → Saved.Reply → Set
  Goal token before after reply = Σ Metadata (λ metadata → ObservedGoal token metadata before after reply)

  fromObservation : ∀ token metadata before after reply → (after , reply) ≡ Saved.execute (token , metadata) before →
    Goal token before after reply
  fromObservation token metadata before after reply observed = metadata , subst
    (λ outcome → ObservedGoal token metadata before (proj₁ outcome) (proj₂ outcome)) (sym observed) (meaning token metadata before)

  converges : ∀ token before interrupted after reply → X.Interrupted (script token) before interrupted →
    X.Completed (script token) interrupted after reply → Goal token before after reply
  converges token before interrupted after reply interruption completion
    with interruptionState token before interrupted interruption | completedObservation token interrupted after reply completion
  ... | inj₁ same | metadata , observed = fromObservation token metadata before after reply
    (trans observed (cong (Saved.execute (token , metadata)) same))
  ... | inj₂ (first , same) | second , observed = fromObservation token first before after reply
    (trans observed (trans (cong (Saved.execute (token , second)) same) (crossStable token first second before)))

  progress : ∀ token before → Σ Store.World (λ after → Σ Saved.Reply (λ reply → X.Completed (script token) before after reply))
  progress token before = proj₁ expected , proj₂ expected , X.completed
    ((token , metadata , proj₂ expected) ∷ [])
    (E.replied token (λ reply → E.done (proj₂ reply)) (metadata , proj₂ expected) (E.returned _))
    (X.changed before token _ _ (refl , Saved.expectedPhysical (token , metadata) before) (X.unchanged _))
    where
    -- Existence of a possible external reply proves protocol progress. This
    -- witness is not an application allocator, configured value or UUID law.
    metadata : Metadata
    metadata = 0 , + 0
    expected = Saved.execute (token , metadata) before

  operation : Recovery.RecoverableFor Store.World ℕ Saved.Reply Goal
  operation = record { Effect = Effect; Reply = Reply; script = script; Atomic = Atomic; converges = converges; progress = progress }
