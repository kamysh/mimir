{-# OPTIONS --safe #-}
-- A public write must agree with its token's actual decoded binding. Neither
-- the caller nor a dispatcher entry supplies an agreement flag or an answer.
module Mimir.PublicOperationBinding where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Float.Base using (Float)
open import Agda.Builtin.Float using (primFloatEquality)
open import Data.Integer using (ℤ)
import Data.Integer.Properties as Integer
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Properties as Lists
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe.Properties as Maybes
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.String using (toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Sum.Properties as Sum
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (does; ¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; subst; sym)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.ApplicationStore as Store
import Mimir.Binary64 as Binary
import Mimir.DocumentStore as Documents
import Mimir.GraphMutationProtocol as Mutation
import Mimir.GraphDeletion as Deletion
import Mimir.InferenceProtocol as Inference
import Mimir.IndependentProvenance as Origin
import Mimir.LearningCandidates as Candidates
import Mimir.LearningInput as Input
import Mimir.LearningKeys as Keys
import Mimir.LearningOperations as Learning
import Mimir.PublicRequest as Public
import Mimir.PublicInput as Fields
import Mimir.ReviewSchema as Review
import Mimir.SemanticKey as Key
import Mimir.StandardLibrary as Library
import Mimir.StructuredValue as Wire
import Mimir.ToolCatalog as Tools
import Mimir.ProjectDeletion as Project
import Mimir.Validation as Validation
import Mimir.RecordDecoding as Record
import Mimir.JsonObjects as Objects
import Mimir.RecoverableStoreStep as Step
import Mimir.Recovery as Recovery
import Mimir.Effects as Effects
import Mimir.OperationControls as Controls
import Mimir.DatabaseTransaction as DB
import Mimir.RegisteredStoreAdmission as AdmissionStore
import Data.Fin as Fin
open import Mimir.RecordDecoding using (_>>=_)

sameText : Text → Text → Bool
sameText first second = does (first ≟Text second)
sameNat : ℕ → ℕ → Bool
sameNat first second = does (first ≟ second)
sameInteger : ℤ → ℤ → Bool
sameInteger first second = does (first Integer.≟ second)
sameKey : Key.Key → Key.Key → Bool
sameKey first second = does (Key.equal first second)
sameNumber : Binary.Number → Binary.Number → Bool
sameNumber first second = sameKey (Keys.number first) (Keys.number second)

sameFloat : Float → Float → Bool
sameFloat = primFloatEquality

sameMaybe : ∀ {A : Set} → (A → A → Bool) → Maybe A → Maybe A → Bool
sameMaybe same nothing nothing = true
sameMaybe same (just first) (just second) = same first second
sameMaybe same _ _ = false

sameProvenance : Origin.Provenance → Origin.Provenance → Bool
sameProvenance first second = sameBasis (Origin.Provenance.basis first) (Origin.Provenance.basis second) ∧
  sameText (Origin.Provenance.reference first) (Origin.Provenance.reference second)
  where
  sameBasis : Origin.Basis → Origin.Basis → Bool
  sameBasis Origin.userInstruction Origin.userInstruction = true
  sameBasis Origin.document Origin.document = true
  sameBasis _ _ = false

-- Existing canonical projections retain numeric meaning and exact text.
-- Incoming optional IDs/keys are retained before database allocation; they
-- must not disappear by comparing an already-normalized expected answer.
itemKey : Input.Item → Key.Key
itemKey input = Key.fields
  (Keys.optional Key.natural (Input.Item.identity input) ∷
   Keys.item (Input.canonicalItem 0 input) ∷ [])

assessmentKey : Input.Assessment → Key.Key
assessmentKey input = Key.fields
  (Keys.assessment (Input.Assessment.value input) ∷ Keys.many Key.text (Input.Assessment.itemKeys input) ∷ [])

experienceKey : Input.Experience → Key.Key
experienceKey input = Key.fields
  (Keys.experience (Input.canonicalExperience input []) ∷ Keys.many itemKey (Input.Experience.items input) ∷ [])

reviewKey : Input.Review → Key.Key
reviewKey input = Key.fields
  (Keys.review (Input.canonicalReview input [] []) ∷ Keys.many itemKey (Input.Review.extracted input) ∷
   Keys.many assessmentKey (Input.Review.assessments input) ∷ [])

sameMutation : Mutation.Request → Mutation.Request → Bool
sameMutation (Mutation.belief content probability confidence project memory origin cited)
  (Mutation.belief other otherProbability otherConfidence otherProject otherMemory otherOrigin otherCited) =
  sameText content other ∧ sameFloat probability otherProbability ∧ sameFloat confidence otherConfidence ∧
  sameMaybe sameText project otherProject ∧ sameKey (Keys.memory memory) (Keys.memory otherMemory) ∧
  sameMaybe sameProvenance origin otherOrigin ∧ does (Lists.≡-dec Documents.citationEqual cited otherCited)
sameMutation (Mutation.patternNode situation approach success project)
  (Mutation.patternNode otherSituation otherApproach otherSuccess otherProject) =
  sameText situation otherSituation ∧ sameText approach otherApproach ∧ sameFloat success otherSuccess ∧ sameMaybe sameText project otherProject
sameMutation (Mutation.edge from to relation weight) (Mutation.edge otherFrom otherTo otherRelation otherWeight) =
  sameNat from otherFrom ∧ sameNat to otherTo ∧ sameNat (Review.relationCode relation) (Review.relationCode otherRelation) ∧
  sameNumber weight otherWeight
sameMutation _ _ = false

sameKind : Deletion.Kind → Deletion.Kind → Bool
sameKind Deletion.belief Deletion.belief = true
sameKind Deletion.patternNode Deletion.patternNode = true
sameKind _ _ = false

sameInference : Inference.Request → Inference.Request → Bool
sameInference (Inference.propagate id) (Inference.propagate other) = sameNat id other
sameInference (Inference.intervention id value) (Inference.intervention other actual) = sameNat id other ∧ sameFloat value actual
sameInference (Inference.decay project factor) (Inference.decay otherProject actual) = sameMaybe sameText project otherProject ∧ sameFloat factor actual
sameInference (Inference.contradictions project) (Inference.contradictions actual) = sameMaybe sameText project actual
sameInference (Inference.sweep project threshold grace) (Inference.sweep otherProject actual period) =
  sameMaybe sameText project otherProject ∧ sameFloat threshold actual ∧ sameInteger grace period
sameInference _ _ = false

sameLearning : Learning.Request → Learning.Request → Bool
sameLearning (Learning.recordExperience value revision) (Learning.recordExperience actual expected) =
  sameKey (experienceKey value) (experienceKey actual) ∧ sameInteger revision expected
sameLearning (Learning.reviewExperience value revision) (Learning.reviewExperience actual expected) =
  sameKey (reviewKey value) (reviewKey actual) ∧ sameInteger revision expected
sameLearning _ _ = false

-- This guard is used only for mutable requests. Other operation families
-- cannot agree with a write binding. Read-only dispatch has no write token.
sameArguments : Public.Request → Public.Request → Bool
sameArguments (Public.mutation expected) (Public.mutation actual) = sameMutation expected actual
sameArguments (Public.delete kind id) (Public.delete actualKind actualID) = sameKind kind actualKind ∧ sameNat id actualID
sameArguments (Public.deleteProject project) (Public.deleteProject actual) = sameText project actual
sameArguments (Public.inference expected) (Public.inference actual) = sameInference expected actual
sameArguments (Public.sweepConfigured project threshold) (Public.sweepConfigured actualProject actualThreshold) =
  sameMaybe sameText project actualProject ∧ sameFloat threshold actualThreshold
sameArguments (Public.addEvidence belief chunk weight) (Public.addEvidence actualBelief actualChunk actualWeight) =
  sameNat belief actualBelief ∧ sameNat chunk actualChunk ∧ sameFloat weight actualWeight
sameArguments (Public.removeEvidence belief chunk) (Public.removeEvidence actualBelief actualChunk) =
  sameNat belief actualBelief ∧ sameNat chunk actualChunk
sameArguments (Public.loadDocument path project) (Public.loadDocument actualPath actualProject) =
  sameText path actualPath ∧ sameMaybe sameText project actualProject
sameArguments (Public.clearDocument path) (Public.clearDocument actual) = sameText path actual
sameArguments (Public.learning expected) (Public.learning actual) = sameLearning expected actual
sameArguments _ _ = false

data Source : Set where
  advertised : Tools.Tool → Source
  evidenceRemoval : Source -- existing internal API, not another MCP tool

sourceName : Source → Text
sourceName (advertised tool) = toList (Tools.wireName tool)
sourceName evidenceRemoval = toList "delete_evidence"

missingBinding changedRequest : Validation.Fault
missingBinding = Validation.fault (Validation.key "operation_token" ∷ []) Validation.missingReference
  "This token has no original bound request. Read its reservation and binding; bind the intended original request before execution. Do not invent a token or arguments."
changedRequest = Validation.fault (Validation.key "operation_token" ∷ []) Validation.wrongIdentity
  "The submitted request differs from this token's original operation or arguments. Read the saved binding and outcome with the same token. Ask the user before cancelling unfinished work and reserving corrected work; do not rewrite or automatically cancel the original."

Bindings = List Store.BindingRow
bindings : Store.World → Bindings
bindings state = Store.OperationTables.bindings (Store.World.operations state)

-- This bridge is instantiated with the actual admitted store step. It proves
-- that the binding read by the public guard survives a real interrupted run;
-- it does not ask callers to certify arbitrary graph or planning effects.
module AdmittedStep (Input Diagnostic : Set)
  (token : Input → ℕ) (key : Input → Text)
  (distinct : ∀ input → ¬ (key input ≡ Step.resultKey))
  (decide : Input → Store.World → Diagnostic ⊎ (Store.World × Wire.Value))
  (keepsJournal : ∀ input before changed reply → decide input before ≡ inj₂ (changed , reply) →
    Store.World.operations changed ≡ Store.World.operations before)
  (admit : Input → Step.Registration → Maybe Diagnostic) where
  module Actual = Step.Admitted Input Diagnostic token key distinct decide keepsJournal admit

  registrationUnchanged : ∀ input before →
    Step.registration (proj₁ (Actual.execute input before)) ≡ Step.registration before
  registrationUnchanged input before with admit input (Step.registration before)
  ... | just diagnostic = refl
  ... | nothing = Actual.Kernel.registrationUnchanged input before

  bindingsUnchanged : ∀ input before → bindings (proj₁ (Actual.execute input before)) ≡ bindings before
  bindingsUnchanged input before = cong (λ registration → proj₁ (proj₂ (proj₂ registration)))
    (registrationUnchanged input before)

  interruptedBindings : ∀ input before interrupted →
    Actual.X.Interrupted (Actual.script input) before interrupted → bindings interrupted ≡ bindings before
  interruptedBindings input before interrupted crash with Actual.interruptionState input before interrupted crash
  ... | inj₁ same = cong bindings same
  ... | inj₂ same = trans (cong bindings same) (bindingsUnchanged input before)

  existingBindingSurvives : ∀ input watched before interrupted original →
    Project.Registered.binding watched (bindings before) ≡ just original →
    Actual.X.Interrupted (Actual.script input) before interrupted →
    Project.Registered.binding watched (bindings interrupted) ≡ just original
  existingBindingSurvives input watched before interrupted original present crash =
    trans (cong (Project.Registered.binding watched) (interruptedBindings input before interrupted crash)) present

module Decode (library : Library.Contract) where
  module D = Public.Decode library
  module Scalar = Fields.Numbers library

  readRemoval : Wire.Value → Validation.Fault ⊎ Public.Request
  readRemoval = Record.readRecord Objects.forbid Objects.rejectKnownRepeated
    (toList "belief_id" ∷ toList "chunk_id" ∷ []) λ view →
      Fields.required "belief_id" Scalar.uuid view >>= λ belief →
      Fields.required "chunk_id" Scalar.uuid view >>= λ chunk → inj₂ (Public.removeEvidence belief chunk)

  readStored : Source → Wire.Value → Validation.Fault ⊎ Public.Request
  readStored (advertised Tools.insertBelief) raw@(Wire.object fields)
    with Wire.Object.normalize fields (toList "grounding")
  ... | nothing = D.readBoundTool Tools.insertBelief (Wire.object ((toList "grounding" , Wire.array []) ∷ fields))
  ... | just _ = D.readBoundTool Tools.insertBelief raw
  readStored (advertised tool) raw = D.readBoundTool tool raw
  readStored evidenceRemoval raw = readRemoval raw

  originalRow : Source → Maybe Store.BindingRow → Validation.Fault ⊎ Public.Request
  originalRow source nothing = inj₁ missingBinding
  originalRow source (just bound) with sameText (Store.BindingRow.operation bound) (sourceName source)
  ... | false = inj₁ changedRequest
  ... | true = readStored source (Store.BindingRow.arguments bound)

  admitRow : Source → Public.Request → Maybe Store.BindingRow → Validation.Fault ⊎ ⊤
  admitRow source expected row with originalRow source row
  ... | inj₁ fault = inj₁ fault
  ... | inj₂ actual with sameArguments expected actual
  ... | false = inj₁ changedRequest
  ... | true = inj₂ tt

  admit : Source → Public.Request → ℕ → Bindings → Validation.Fault ⊎ ⊤
  admit source expected token rows = admitRow source expected (Project.Registered.binding token rows)

  acceptedHasBinding : ∀ source expected row → admitRow source expected row ≡ inj₂ tt →
    Σ Store.BindingRow (λ original → row ≡ just original)
  acceptedHasBinding source expected nothing ()
  acceptedHasBinding source expected (just original) accepted = original , refl

  sameBindingKeepsAdmission : ∀ source expected token before after →
    Project.Registered.binding token (bindings after) ≡ Project.Registered.binding token (bindings before) →
    admit source expected token (bindings after) ≡ admit source expected token (bindings before)
  sameBindingKeepsAdmission source expected token before after same = cong (admitRow source expected) same

  -- The comparison reads immutable binding rows, not capture/planning rows:
  -- saving a legitimate captured selection cannot change request admission.
  unchangedBindingsKeepAdmission : ∀ source expected token before after → bindings after ≡ bindings before →
    admit source expected token (bindings after) ≡ admit source expected token (bindings before)
  unchangedBindingsKeepAdmission source expected token before after same = cong (admit source expected token) same

  -- Concrete assembly supplies the existing proved operation, not a catalogue
  -- provided by a client. Its business goal remains fixed by that operation.
  -- The already observed own binding survives the actual scripted run;
  -- first binding of another request and capture/planning may advance.
  module Guarded {Response : Set}
    {BusinessGoal : ℕ → Store.World → Store.World → Response → Set}
    (source : Source) (expected : Public.Request)
    (underlying : Recovery.RecoverableFor Store.World ℕ Response BusinessGoal)
    (preservesBinding : ∀ token before interrupted original →
      Project.Registered.binding token (bindings before) ≡ just original →
      Recovery.RecoverableFor.X.Interrupted underlying (Recovery.RecoverableFor.script underlying token) before interrupted →
      Project.Registered.binding token (bindings interrupted) ≡ just original) where
    module O = Recovery.RecoverableFor underlying

    data Result : Set where
      needsInput : Validation.Fault → Result
      executed : Response → Result

    data Effect : Set where
      readBinding : ℕ → Effect
      perform : O.Effect → Effect
    Reply : Effect → Set
    Reply (readBinding _) = Store.World
    Reply (perform effect) = O.Reply effect
    module E = Effects.Protocol Effect Reply

    lift : O.E.Script Response → E.Script Result
    lift (O.E.done result) = E.done (executed result)
    lift (O.E.ask effect next) = E.ask (perform effect) (λ reply → lift (next reply))

    afterBinding : ℕ → Store.World → E.Script Result
    afterBinding token observed with admit source expected token (bindings observed)
    ... | inj₁ fault = E.done (needsInput fault)
    ... | inj₂ tt = lift (O.script token)

    script : ℕ → E.Script Result
    script token = E.ask (readBinding token) (afterBinding token)

    Atomic : Store.World → (effect : Effect) → Reply effect → Store.World → Set
    Atomic before (readBinding token) observed after = observed ≡ before × after ≡ before
    Atomic before (perform effect) reply after = O.Atomic before effect reply after
    module X = Recovery.Execution Store.World Effect Reply Atomic

    Goal : ℕ → Store.World → Store.World → Result → Set
    Goal token before after (needsInput fault) = after ≡ before × admit source expected token (bindings before) ≡ inj₁ fault
    Goal token before after (executed response) = admit source expected token (bindings before) ≡ inj₂ tt × BusinessGoal token before after response

    liftEvent : O.E.Event → E.Event
    liftEvent (effect , reply) = perform effect , reply

    liftRun : ∀ program events response → O.E.Runs program events response →
      E.Runs (lift program) (map liftEvent events) (executed response)
    liftRun .(O.E.done response) .[] response (O.E.returned _) = E.returned _
    liftRun .(O.E.ask effect next) ._ response (O.E.replied effect next reply later) =
      E.replied _ _ reply (liftRun (next reply) _ response later)

    liftChanges : ∀ {before events after} → O.X.Changes before events after → X.Changes before (map liftEvent events) after
    liftChanges (O.X.unchanged before) = X.unchanged before
    liftChanges (O.X.changed before effect reply middle physical later) =
      X.changed before (perform effect) reply middle physical (liftChanges later)

    -- This is the actual binding read followed by the actual existing body
    -- trace; it neither runs a new write nor supplies an arbitrary receipt.
    liftReadOnlyCompletion : ∀ token before response →
      admit source expected token (bindings before) ≡ inj₂ tt →
      O.X.Completed (O.script token) before before response →
      X.Completed (script token) before before (executed response)
    admittedBranch : ∀ token before → admit source expected token (bindings before) ≡ inj₂ tt →
      afterBinding token before ≡ lift (O.script token)
    admittedBranch token before admitted with admit source expected token (bindings before)
    ... | inj₁ fault with admitted
    ... | ()
    admittedBranch token before admitted | inj₂ tt = refl

    liftReadOnlyCompletion token before response admitted
      (O.X.completed events execution changes) = X.completed
        ((readBinding token , before) ∷ map liftEvent events)
        (E.replied (readBinding token) (afterBinding token) before
          (subst (λ branch → E.Runs branch (map liftEvent events) (executed response))
            (sym (admittedBranch token before admitted))
            (liftRun (O.script token) events response execution)))
        (X.changed before (readBinding token) before before (refl , refl)
          (liftChanges changes))

    eraseCompletion : ∀ program before after result events → E.Runs (lift program) events result →
      X.Changes before events after → Σ Response (λ response → result ≡ executed response × O.X.Completed program before after response)
    eraseCompletion (O.E.done response) before .before ._ .[] (E.returned _) (X.unchanged _) =
      response , refl , O.X.completed [] (O.E.returned _) (O.X.unchanged _)
    eraseCompletion (O.E.ask effect next) before after result ._
      (E.replied .(perform effect) _ reply execution) (X.changed _ _ _ middle physical changes)
      with eraseCompletion (next reply) middle after result _ execution changes
    ... | response , same , O.X.completed events observed stores = response , same , O.X.completed
      ((effect , reply) ∷ events) (O.E.replied effect next reply observed) (O.X.changed before effect reply middle physical stores)

    CompletionMeaning : ℕ → Store.World → Store.World → Result → Set
    CompletionMeaning token before after (needsInput fault) = after ≡ before × admit source expected token (bindings before) ≡ inj₁ fault
    CompletionMeaning token before after (executed response) = admit source expected token (bindings before) ≡ inj₂ tt ×
      O.X.Completed (O.script token) before after response

    branchMeaning : ∀ token before after result events → E.Runs (afterBinding token before) events result →
      X.Changes before events after → CompletionMeaning token before after result
    branchMeaning token before after result events execution physical with admit source expected token (bindings before) in accepted
    ... | inj₁ fault with execution | physical
    ... | E.returned _ | X.unchanged _ = refl , accepted
    branchMeaning token before after result events execution physical | inj₂ tt
      with eraseCompletion (O.script token) before after result events execution physical
    ... | response , refl , sourceRun = accepted , sourceRun

    completionMeaning : ∀ token before after result → X.Completed (script token) before after result → CompletionMeaning token before after result
    completionMeaning token before after result
      (X.completed _ (E.replied _ _ .before execution) (X.changed _ _ _ .before (refl , refl) physical)) =
      branchMeaning token before after result _ execution physical

    SourceRecovery : Set
    SourceRecovery = ∀ token before interrupted after response → O.X.Interrupted (O.script token) before interrupted →
      O.X.Completed (O.script token) interrupted after response → BusinessGoal token before after response

    SourceProgress : Set
    SourceProgress = ∀ token before → Σ Store.World (λ after → Σ Response (λ response → O.X.Completed (O.script token) before after response))

    completedMeetsGoalWith : SourceRecovery → ∀ token before after result → X.Completed (script token) before after result → Goal token before after result
    completedMeetsGoalWith recovers token before after (needsInput fault) completion = completionMeaning token before after (needsInput fault) completion
    completedMeetsGoalWith recovers token before after (executed response) completion with completionMeaning token before after (executed response) completion
    ... | admitted , sourceCompletion = admitted , recovers token before before after response
      (O.X.atPrefix [] (O.script token) before (O.E.stopped _) (O.X.unchanged before)) sourceCompletion

    completedMeetsGoal = completedMeetsGoalWith O.converges

    record OriginalPrefix (program : O.E.Script Response) (before after : Store.World) (residual : E.Script Result) : Set where
      constructor originalPrefix
      field
        events : List O.E.Event
        remaining : O.E.Script Response
        reached : O.E.Prefix program events remaining
        physical : O.X.Changes before events after
        projection : residual ≡ lift remaining

    erasePrefix : ∀ program before after residual events → E.Prefix (lift program) events residual →
      X.Changes before events after → OriginalPrefix program before after residual
    erasePrefix program before .before .(lift program) .[] (E.stopped _) (X.unchanged _) =
      originalPrefix [] program (O.E.stopped _) (O.X.unchanged _) refl
    erasePrefix (O.E.ask effect next) before after residual ._
      (E.replied .(perform effect) _ reply prefix) (X.changed _ _ _ middle physical changes)
      with erasePrefix (next reply) middle after residual _ prefix changes
    ... | originalPrefix events remaining reached stores same = originalPrefix
      ((effect , reply) ∷ events) remaining (O.E.replied effect next reply reached)
      (O.X.changed before effect reply middle physical stores) same

    eraseActive : ∀ program before current after effect next reply events →
      E.Prefix (lift program) events (E.ask effect next) → X.Changes before events current →
      Atomic current effect reply after → O.X.Interrupted program before after
    eraseActive program before current after effect next reply events prefix physical active
      with erasePrefix program before current (E.ask effect next) events prefix physical
    ... | originalPrefix sourceEvents (O.E.done response) reached stores ()
    ... | originalPrefix sourceEvents (O.E.ask sourceEffect sourceNext) reached stores refl =
      O.X.beforeReply sourceEvents sourceEffect sourceNext current reply after reached stores active

    donePrefixUnchanged : ∀ (result : Result) events residual before after → E.Prefix (E.done result) events residual →
      X.Changes before events after → after ≡ before
    donePrefixUnchanged result .[] .(E.done result) before .before (E.stopped _) (X.unchanged _) = refl

    doneCannotAsk : ∀ (result : Result) events effect next → E.Prefix (E.done result) events (E.ask effect next) → ⊥
    doneCannotAsk result events effect next ()

    -- Stop before admission is a read-only interruption. Once admitted, erase
    -- only that read and retain every actual underlying effect and receipt.
    InterruptionMeaning : ℕ → Store.World → Store.World → Set
    InterruptionMeaning token before interrupted = interrupted ≡ before ⊎
      (admit source expected token (bindings before) ≡ inj₂ tt × O.X.Interrupted (O.script token) before interrupted)

    interruptionMeaning : ∀ token before interrupted → X.Interrupted (script token) before interrupted →
      InterruptionMeaning token before interrupted
    interruptionMeaning token before .before (X.atPrefix .[] .(script token) .before (E.stopped _) (X.unchanged _)) = inj₁ refl
    interruptionMeaning token before interrupted
      (X.atPrefix _ residual .interrupted (E.replied _ _ .before {events} prefix)
        (X.changed _ _ _ .before (refl , refl) physical))
      with admit source expected token (bindings before) in admitted
    ... | inj₁ fault = inj₁ (donePrefixUnchanged _ events residual before interrupted prefix physical)
    ... | inj₂ tt with erasePrefix (O.script token) before interrupted residual events prefix physical
    ... | originalPrefix sourceEvents remaining reached stores same = inj₂ (refl ,
      O.X.atPrefix sourceEvents remaining interrupted reached stores)
    interruptionMeaning token before interrupted
      (X.beforeReply .[] .(readBinding token) .(afterBinding token) .before reply .interrupted
        (E.stopped _) (X.unchanged _) active) = inj₁ (proj₂ active)
    interruptionMeaning token before interrupted
      (X.beforeReply _ effect next current reply .interrupted (E.replied _ _ .before {events} prefix)
        (X.changed _ _ _ .before (refl , refl) physical) active)
      with admit source expected token (bindings before) in admitted
    ... | inj₁ fault = ⊥-elim (doneCannotAsk _ events effect next prefix)
    ... | inj₂ tt = inj₂ (refl , eraseActive (O.script token) before current interrupted effect next reply events prefix physical active)

    interruptedKeepsObservation : ∀ {Observation : Set} (observe : Store.World → Observation) →
      (∀ token before after → O.X.Interrupted (O.script token) before after → observe after ≡ observe before) →
      ∀ token before after → X.Interrupted (script token) before after → observe after ≡ observe before
    interruptedKeepsObservation observe keeps token before after cut with interruptionMeaning token before after cut
    ... | inj₁ unchanged = cong observe unchanged
    ... | inj₂ (admitted , sourceCut) = keeps token before after sourceCut

    -- A final answer that appeared during this interrupted call cannot have
    -- come from rejecting its binding: that branch never changes the World.
    completedInterruption : ∀ token before current raw →
      Store.lookupSaved before token Step.resultKey ≡ nothing →
      Store.lookupSaved current token Step.resultKey ≡ just raw →
      X.Interrupted (script token) before current →
      admit source expected token (bindings before) ≡ inj₂ tt ×
        O.X.Interrupted (O.script token) before current
    completedInterruption token before current raw absent present cut
      with interruptionMeaning token before current cut
    ... | inj₂ active = active
    ... | inj₁ same = ⊥-elim (impossible same)
      where
      impossible : current ≡ before → ⊥
      impossible refl with trans (sym absent) present
      ... | ()

    admittedRetry : ∀ token before interrupted → admit source expected token (bindings before) ≡ inj₂ tt →
      O.X.Interrupted (O.script token) before interrupted → admit source expected token (bindings interrupted) ≡ inj₂ tt
    admittedRetry token before interrupted admitted cut with
      acceptedHasBinding source expected (Project.Registered.binding token (bindings before)) admitted
    ... | original , saved = trans (cong (admitRow source expected)
      (trans (preservesBinding token before interrupted original saved cut) (sym saved))) admitted

    convergesWith : SourceRecovery → ∀ token before interrupted after result → X.Interrupted (script token) before interrupted →
      X.Completed (script token) interrupted after result → Goal token before after result
    convergesWith recovers token before interrupted after result cut completion with interruptionMeaning token before interrupted cut
    ... | inj₁ same = subst (λ initial → Goal token initial after result) same (completedMeetsGoalWith recovers token interrupted after result completion)
    convergesWith recovers token before interrupted after (needsInput fault) cut completion | inj₂ (admitted , sourceCut)
      with completionMeaning token interrupted after (needsInput fault) completion
    ... | unchanged , refused with trans (sym (admittedRetry token before interrupted admitted sourceCut)) refused
    ... | ()
    convergesWith recovers token before interrupted after (executed response) cut completion | inj₂ (admitted , sourceCut)
      with completionMeaning token interrupted after (executed response) completion
    ... | retryAdmitted , sourceCompletion = admitted , recovers token before interrupted after response sourceCut sourceCompletion

    branchProgressWith : SourceProgress → ∀ token before → Σ Store.World (λ after → Σ Result (λ result → X.Completed (afterBinding token before) before after result))
    branchProgressWith progresses token before with admit source expected token (bindings before)
    ... | inj₁ fault = before , needsInput fault , X.completed [] (E.returned _) (X.unchanged _)
    ... | inj₂ tt with progresses token before
    ... | after , response , O.X.completed events execution physical = after , executed response , X.completed
      (map liftEvent events) (liftRun _ events response execution) (liftChanges physical)

    progressWith : SourceProgress → ∀ token before → Σ Store.World (λ after → Σ Result (λ result → X.Completed (script token) before after result))
    progressWith progresses token before with branchProgressWith progresses token before
    ... | after , result , X.completed events execution physical = after , result , X.completed
      ((readBinding token , before) ∷ events) (E.replied _ _ before execution)
      (X.changed before _ before before (refl , refl) physical)

    -- Behavioral types stay fixed; alternative proofs of those SAME scripts,
    -- effects and business goal enter only here, never as reply parameters.
    operationWith : SourceRecovery → SourceProgress → Recovery.RecoverableFor Store.World ℕ Result Goal
    operationWith recovers progresses = record
      { Effect = Effect; Reply = Reply; script = script; Atomic = Atomic
      ; converges = convergesWith recovers; progress = progressWith progresses }
    converges = convergesWith O.converges
    progress = progressWith O.progress
    operation : Recovery.RecoverableFor Store.World ℕ Result Goal
    operation = operationWith O.converges O.progress

-- Native execute_registered_write creates this metadata before its concrete
-- writer runs. The input is the actual public object, never an expected plan,
-- reconstructed argument object, success flag or caller-selected goal.
module Creating (library : Library.Contract) (postgres : Controls.PostgreSQL) where
  module D = Public.Decode library
  module P = Controls.Plan
  module Read = Controls.Readback library postgres

  record Request : Set where
    constructor submittedWrite
    field tool : Tools.Tool; submitted : Wire.Value

  writerToken : ∀ tool → Tools.kind tool ≡ Tools.businessWrite → Public.TokenFor tool → ℕ
  writerToken tool known token with Tools.kind tool
  ... | Tools.businessWrite = token
  writerToken tool () token | Tools.readOnly
  writerToken tool () token | Tools.operationControl

  record Call : Set where
    constructor admittedWrite
    field tool : Tools.Tool
          submitted : Wire.Value
          writer : Tools.kind tool ≡ Tools.businessWrite
          invocation : D.Invocation tool submitted
    token : ℕ
    token = writerToken tool writer (D.Invocation.operationToken invocation)
    arguments : Wire.Value
    arguments = D.Invocation.arguments invocation
    request : Public.Request
    request = D.Invocation.request invocation
    name : Text
    name = toList (Tools.wireName tool)

  wrongWriter : Validation.Fault
  wrongWriter = Validation.fault [] Validation.wrongIdentity
    "Use the advertised read-only or operation-control entry for this tool. Only an admitted business write creates a binding and plan. No business data changed."

  decode : Request → Validation.Fault ⊎ Call
  decode (submittedWrite tool raw) with Tools.kind tool in kind
  ... | Tools.readOnly = inj₁ wrongWriter
  ... | Tools.operationControl = inj₁ wrongWriter
  ... | Tools.businessWrite with D.readInvocation tool raw
  ... | inj₁ fault = inj₁ fault
  ... | inj₂ observedCall = inj₂ (admittedWrite tool raw kind observedCall)

  -- This project value comes from the actual admitted object, rather than
  -- a second parse, a default project or reconstructed request arguments.
  decodedProject : ∀ fields requested → D.decode Tools.deleteProject fields ≡ inj₂ requested →
    Σ Text (λ project → requested ≡ Public.deleteProject project)
  decodedProject fields requested accepted with Record.bindSuccess
    (Fields.required "project" Wire.asString fields) (λ project → inj₂ (Public.deleteProject project)) requested accepted
  ... | project , observed , same = project , sym (Sum.inj₂-injective same)

  admittedProject : ∀ fields requested → D.admittedFields Tools.deleteProject fields ≡ inj₂ requested →
    Σ Text (λ project → requested ≡ Public.deleteProject project)
  admittedProject fields requested accepted = Record.afterSuccess (D.suppliedTypes fields)
    (λ _ → D.decode Tools.deleteProject fields) requested
    (λ _ _ decoded → decodedProject fields requested decoded) accepted

  readProject : ∀ raw requested → D.readTool Tools.deleteProject raw ≡ inj₂ requested →
    Σ Text (λ project → requested ≡ Public.deleteProject project)
  readProject (Wire.object fields) requested accepted
    with Wire.Object.checkUnknowns Objects.forbid (Public.acceptedFields Tools.deleteProject) fields
  ... | Validation.rejected detail invalid with accepted
  ... | ()
  readProject (Wire.object fields) requested accepted | Validation.accepted known =
    admittedProject (Wire.Object.normalize fields) requested accepted
  readProject (Wire.string _) requested ()
  readProject (Wire.signed _) requested ()
  readProject (Wire.unsigned _) requested ()
  readProject (Wire.floating _) requested ()
  readProject (Wire.boolean _) requested ()
  readProject Wire.null requested ()
  readProject (Wire.array _) requested ()

  -- The SQL predicate compares the operation name as text, and independently
  -- compares arguments and settings as jsonb (where 1 and 1.0 are equal).
  -- The supplied object still removes only operation_token.
  matches : Call → Wire.Value → Store.BindingRow → Bool
  matches call settings original = does (Store.BindingRow.operation original ≟Text Call.name call) ∧
    Controls.PostgreSQL.jsonbEqual postgres (Store.BindingRow.arguments original) (Call.arguments call) ∧
    Controls.PostgreSQL.jsonbEqual postgres (Store.BindingRow.settings original) settings

  matchingOperation : ∀ call settings original → matches call settings original ≡ true →
    Store.BindingRow.operation original ≡ Call.name call
  matchingOperation call settings original matched with Store.BindingRow.operation original ≟Text Call.name call
  ... | yes same = same
  ... | no different with matched
  ... | ()

  matchesOriginalSettings : ∀ call earlierSettings original → matches call earlierSettings original ≡ true →
    matches call (Store.BindingRow.settings original) original ≡ true
  matchesOriginalSettings call earlierSettings original matched
    with Store.BindingRow.operation original ≟Text Call.name call
  ... | no _ with matched
  ... | ()
  matchesOriginalSettings call earlierSettings original matched | yes _
    with Controls.PostgreSQL.jsonbEqual postgres (Store.BindingRow.arguments original) (Call.arguments call)
  ... | false with matched
  ... | ()
  matchesOriginalSettings call earlierSettings original matched | yes _ | true
    rewrite Controls.PostgreSQL.jsonbReflexive postgres (Store.BindingRow.settings original) = refl

  tables = Store.World.operations
  binding : ℕ → Store.World → Maybe Store.BindingRow
  binding token before = Project.Registered.binding token (Store.OperationTables.bindings (tables before))
  plan : ℕ → Store.World → Maybe Wire.Value
  plan token before = Project.Registered.plan token (Store.OperationTables.plans (tables before))

  protected : Store.World → Store.World
  protected before = record before { operations = record (tables before) { bindings = []; plans = [] } }

  putBinding : Store.BindingRow → Store.World → Store.World
  putBinding row before = record before { operations = record (tables before)
    { bindings = row ∷ Store.OperationTables.bindings (tables before) } }
  putPlan : ℕ → Wire.Value → Store.World → Store.World
  putPlan token raw before = record before { operations = record (tables before)
    { plans = Store.planRow token raw ∷ Store.OperationTables.plans (tables before) } }

  newBinding : Call → Wire.Value → ℤ → Store.BindingRow
  newBinding call settings observedTime = Store.bindingRow (Call.token call) (Call.name call)
    (Call.arguments call) settings observedTime

  data BindingResult : Set where
    bound changed : Store.BindingRow → BindingResult
    unknown : BindingResult
    cancelled : Store.CancellationRow → BindingResult

  bind : Call → Wire.Value → ℤ → Store.World → Store.World × BindingResult
  bind call settings observedTime before with Controls.reservation (Call.token call) before
  ... | nothing = before , unknown
  ... | just _ with Store.lookupCancellation before (Call.token call)
  ... | just receipt = before , cancelled receipt
  ... | nothing with binding (Call.token call) before
  ... | nothing = putBinding (newBinding call settings observedTime) before , bound (newBinding call settings observedTime)
  ... | just original with matches call settings original
  ... | false = before , changed original
  ... | true = before , bound original

  bindingPreservesBusiness : ∀ call settings observedTime before →
    protected (proj₁ (bind call settings observedTime before)) ≡ protected before
  bindingPreservesBusiness call settings observedTime before with Controls.reservation (Call.token call) before
  ... | nothing = refl
  ... | just _ with Store.lookupCancellation before (Call.token call)
  ... | just _ = refl
  ... | nothing with binding (Call.token call) before
  ... | nothing = refl
  ... | just original with matches call settings original
  ... | false = refl
  ... | true = refl

  -- Only the original declared belief keys repeat. Other advertised writers
  -- have fixed registered boundaries. Document/sweep service methods perform
  -- the same fixed-plan writes before their captured business work.
  reviewSteps : List Candidates.Candidate → List P.Step
  reviewSteps [] = []
  reviewSteps (Candidates.patternCandidate _ _ _ ∷ rest) = reviewSteps rest
  reviewSteps (Candidates.belief key _ _ _ ∷ rest) =
    P.canonicalStep library (toList "store.reserve_belief_preparation") (just key) ∷ reviewSteps rest

  selected : Public.Request → List P.Step
  selected (Public.learning (Learning.reviewExperience input expected)) = reviewSteps (Input.Review.candidates input)
  selected _ = []

  badPlan : Validation.Fault
  badPlan = Validation.fault (Validation.key "operation_token" ∷ []) Validation.wrongIdentity
    "Read the original binding, registered plan and saved answers. Resolve incompatible or incomplete metadata with the user; do not replace the token, invent a plan or repeat confirmed work."

  computedPlan : Call → Validation.Fault ⊎ P.Saved
  computedPlan call with P.lookup (Call.name call) P.registered
  ... | nothing = inj₁ badPlan
  ... | just shape with P.rebuild library shape (selected (Call.request call))
  ... | nothing = inj₁ badPlan
  ... | just steps with P.executable library (P.saved (Call.name call) shape steps nothing)
  ... | false = inj₁ badPlan
  ... | true = inj₂ (P.saved (Call.name call) shape steps nothing)

  -- A receipt from serialization of the server-computed plan. This is the
  -- external Serde boundary, not a client plan or normalization theorem.
  data PlanEncoding (call : Call) : Set where
    encoded : ∀ planned → computedPlan call ≡ inj₂ planned →
      (raw : Wire.Value) → P.decode raw ≡ inj₂ planned → PlanEncoding call
    encodingFailed : Validation.Fault → PlanEncoding call

  data PlanResult : Set where
    planned : Store.BindingRow → P.Saved → Wire.Value → PlanResult
    planRefused : Validation.Fault → PlanResult
    planCancelled : Store.CancellationRow → PlanResult
    planUnknown : PlanResult

  -- External canonical-address codec evidence for the actual returned plan.
  -- Native build/load uses canonical serde JSON-array step IDs. This is
  -- neither a business goal nor a claim about an arbitrary formatter.
  PlanValidation : PlanResult → Set
  PlanValidation (planned original model raw) = P.executable library model ≡ true ×
    Controls.Addressing (P.Saved.steps model) ×
    All (λ boundary → P.Step.id boundary ≢ Step.resultKey) (P.Saved.steps model)
  PlanValidation _ = ⊤

  existingPlan : Store.BindingRow → Wire.Value → PlanResult
  existingPlan original raw with P.decode raw
  ... | inj₁ fault = planRefused fault
  ... | inj₂ stored with P.textEqual (Store.BindingRow.operation original) (P.Saved.operation stored)
  ... | false = planRefused badPlan
  ... | true with P.executable library stored
  ... | false = planRefused badPlan
  ... | true = planned original stored raw

  saveNewPlan : (call : Call) → Store.BindingRow → PlanEncoding call → Store.World → Store.World × PlanResult
  saveNewPlan call original (encodingFailed fault) before = before , planRefused fault
  saveNewPlan call original (encoded model computed raw decoded) before = putPlan (Call.token call) raw before , planned original model raw

  prepare : (call : Call) → Wire.Value → PlanEncoding call → Store.World → Store.World × PlanResult
  prepare call settings encodedPlan before with binding (Call.token call) before
  ... | nothing = before , planUnknown
  ... | just original with matches call settings original
  ... | false = before , planRefused changedRequest
  ... | true with Store.lookupCancellation before (Call.token call)
  ... | just receipt = before , planCancelled receipt
  ... | nothing with plan (Call.token call) before
  ... | just raw = before , existingPlan original raw
  ... | nothing with Read.savedRows (Call.token call) before
  ... | _ ∷ _ = before , planRefused badPlan
  ... | [] = saveNewPlan call original encodedPlan before

  planPreservesBusiness : ∀ call settings encodedPlan before →
    protected (proj₁ (prepare call settings encodedPlan before)) ≡ protected before
  planPreservesBusiness call settings encodedPlan before with binding (Call.token call) before
  ... | nothing = refl
  ... | just original with matches call settings original
  ... | false = refl
  ... | true with Store.lookupCancellation before (Call.token call)
  ... | just _ = refl
  ... | nothing with plan (Call.token call) before
  ... | just _ = refl
  ... | nothing with Read.savedRows (Call.token call) before
  ... | _ ∷ _ = refl
  ... | [] with encodedPlan
  ... | encodingFailed _ = refl
  ... | encoded model computed raw decoded = refl

  data BindingsGrew (call : Call) (original : Bindings) : Bindings → Set where
    sameBindings : BindingsGrew call original original
    firstBinding : ∀ settings observedTime current →
      Project.Registered.binding (Call.token call) current ≡ nothing →
      BindingsGrew call original current →
      BindingsGrew call original (newBinding call settings observedTime ∷ current)

  data PlansGrew (call : Call) (original : List Store.PlanRow) : List Store.PlanRow → Set where
    samePlans : PlansGrew call original original
    firstPlan : ∀ model raw current → computedPlan call ≡ inj₂ model → P.decode raw ≡ inj₂ model →
      Project.Registered.plan (Call.token call) current ≡ nothing →
      PlansGrew call original current → PlansGrew call original (Store.planRow (Call.token call) raw ∷ current)

  bindGrows : ∀ call settings observedTime before →
    BindingsGrew call (bindings before) (bindings (proj₁ (bind call settings observedTime before)))
  bindGrows call settings observedTime before with Controls.reservation (Call.token call) before
  ... | nothing = sameBindings
  ... | just _ with Store.lookupCancellation before (Call.token call)
  ... | just _ = sameBindings
  ... | nothing with binding (Call.token call) before in found
  ... | nothing = firstBinding settings observedTime _ found sameBindings
  ... | just original with matches call settings original
  ... | false = sameBindings
  ... | true = sameBindings

  bindKeepsPlans : ∀ call settings observedTime before →
    Store.OperationTables.plans (tables (proj₁ (bind call settings observedTime before))) ≡ Store.OperationTables.plans (tables before)
  bindKeepsPlans call settings observedTime before with Controls.reservation (Call.token call) before
  ... | nothing = refl
  ... | just _ with Store.lookupCancellation before (Call.token call)
  ... | just _ = refl
  ... | nothing with binding (Call.token call) before
  ... | nothing = refl
  ... | just original with matches call settings original
  ... | false = refl
  ... | true = refl

  planKeepsBindings : ∀ call settings encodedPlan before →
    bindings (proj₁ (prepare call settings encodedPlan before)) ≡ bindings before
  planKeepsBindings call settings encodedPlan before with binding (Call.token call) before
  ... | nothing = refl
  ... | just original with matches call settings original
  ... | false = refl
  ... | true with Store.lookupCancellation before (Call.token call)
  ... | just _ = refl
  ... | nothing with plan (Call.token call) before
  ... | just _ = refl
  ... | nothing with Read.savedRows (Call.token call) before
  ... | _ ∷ _ = refl
  ... | [] with encodedPlan
  ... | encodingFailed _ = refl
  ... | encoded model computed raw decoded = refl

  planGrows : ∀ call settings encodedPlan before → PlansGrew call
    (Store.OperationTables.plans (tables before)) (Store.OperationTables.plans (tables (proj₁ (prepare call settings encodedPlan before))))
  planGrows call settings encodedPlan before with binding (Call.token call) before
  ... | nothing = samePlans
  ... | just original with matches call settings original
  ... | false = samePlans
  ... | true with Store.lookupCancellation before (Call.token call)
  ... | just _ = samePlans
  ... | nothing with plan (Call.token call) before in found
  ... | just _ = samePlans
  ... | nothing with Read.savedRows (Call.token call) before
  ... | _ ∷ _ = samePlans
  ... | [] with encodedPlan
  ... | encodingFailed _ = samePlans
  ... | encoded model computed raw decoded = firstPlan model raw _ computed decoded found samePlans

  record Frame (call : Call) (before after : Store.World) : Set where
    field business : protected after ≡ protected before
          bindingExtension : BindingsGrew call (bindings before) (bindings after)
          planExtension : PlansGrew call (Store.OperationTables.plans (tables before)) (Store.OperationTables.plans (tables after))

  identityFrame : ∀ call before → Frame call before before
  identityFrame call before = record { business = refl; bindingExtension = sameBindings; planExtension = samePlans }

  extendBindings : ∀ call first middle final → BindingsGrew call first middle → BindingsGrew call middle final → BindingsGrew call first final
  extendBindings call first middle .middle earlier sameBindings = earlier
  extendBindings call first middle _ earlier (firstBinding settings observedTime current absent later) =
    firstBinding settings observedTime current absent (extendBindings call first middle current earlier later)

  extendPlans : ∀ call first middle final → PlansGrew call first middle → PlansGrew call middle final → PlansGrew call first final
  extendPlans call first middle .middle earlier samePlans = earlier
  extendPlans call first middle _ earlier (firstPlan model raw current computed decoded absent later) =
    firstPlan model raw current computed decoded absent (extendPlans call first middle current earlier later)

  composeFrame : ∀ call first middle final → Frame call first middle → Frame call middle final → Frame call first final
  composeFrame call first middle final earlier later = record
    { business = trans (Frame.business later) (Frame.business earlier)
    ; bindingExtension = extendBindings call _ _ _ (Frame.bindingExtension earlier) (Frame.bindingExtension later)
    ; planExtension = extendPlans call _ _ _ (Frame.planExtension earlier) (Frame.planExtension later) }

  bindFrame : ∀ call settings observedTime before → Frame call before (proj₁ (bind call settings observedTime before))
  bindFrame call settings observedTime before = record
    { business = bindingPreservesBusiness call settings observedTime before
    ; bindingExtension = bindGrows call settings observedTime before
    ; planExtension = subst (PlansGrew call (Store.OperationTables.plans (tables before)))
        (sym (bindKeepsPlans call settings observedTime before)) samePlans }

  planFrame : ∀ call settings encodedPlan before → Frame call before (proj₁ (prepare call settings encodedPlan before))
  planFrame call settings encodedPlan before = record
    { business = planPreservesBusiness call settings encodedPlan before
    ; bindingExtension = subst (BindingsGrew call (bindings before))
        (sym (planKeepsBindings call settings encodedPlan before)) sameBindings
    ; planExtension = planGrows call settings encodedPlan before }

  data Settings : Set where
    configured : Wire.Value → Settings
    unavailable : Validation.Fault → Settings

  record Context : Set where
    constructor preparedWrite
    field call : Call
          original : Store.BindingRow
          model : P.Saved
          raw : Wire.Value

  data Result : Set where
    needsInput : Validation.Fault → Result
    returned : Read.Result → Result
    ready : Context → Result

  data Effect : Set where
    readOriginal : Call → Effect
    currentSettings : Call → Effect
    bindOriginal : Call → Wire.Value → Effect
    readResult : Call → Effect
    publishPlan : Call → Wire.Value → Effect

  Reply : Effect → Set
  Reply (readOriginal _) = Store.World
  Reply (currentSettings _) = Settings
  Reply (bindOriginal _ _) = ℤ × BindingResult
  Reply (readResult _) = Store.World
  Reply (publishPlan call _) = PlanEncoding call × Σ PlanResult PlanValidation

  bindingReceipt : BindingResult → DB.Receipt
  bindingReceipt (bound _) = DB.committed
  bindingReceipt (changed _) = DB.committed
  bindingReceipt unknown = DB.aborted
  bindingReceipt (cancelled _) = DB.aborted
  planReceipt : PlanResult → DB.Receipt
  planReceipt (planned _ _ _) = DB.committed
  planReceipt _ = DB.aborted

  Atomic : Store.World → (effect : Effect) → Reply effect → Store.World → Set
  Atomic before (readOriginal _) observed after = observed ≡ before × after ≡ before
  Atomic before (currentSettings _) observed after = after ≡ before
  Atomic before (bindOriginal call settings) (observedTime , reply) after =
    reply ≡ proj₂ (bind call settings observedTime before) ×
    DB.Atomic before (proj₁ (bind call settings observedTime before)) (bindingReceipt reply) after
  Atomic before (readResult _) observed after = observed ≡ before × after ≡ before
  Atomic before (publishPlan call settings) (encodedPlan , reply , validated) after =
    reply ≡ proj₂ (prepare call settings encodedPlan before) ×
    DB.Atomic before (proj₁ (prepare call settings encodedPlan before)) (planReceipt reply) after

  module X = Recovery.Execution Store.World Effect Reply Atomic
  module E = X.E

  afterPlan : Call → PlanResult → E.Script Result
  afterPlan call (planned original model raw) = E.done (ready (preparedWrite call original model raw))
  afterPlan call (planRefused fault) = E.done (needsInput fault)
  afterPlan call (planCancelled receipt) = E.ask (readResult call)
    (λ observed → E.done (returned (Read.answer (Call.token call) observed)))
  afterPlan call planUnknown = E.ask (readResult call)
    (λ observed → E.done (returned (Read.answer (Call.token call) observed)))

  createPlan : Call → Wire.Value → E.Script Result
  createPlan call settings = E.ask (publishPlan call settings) (λ observed → afterPlan call (proj₁ (proj₂ observed)))

  changedPolicy : Validation.Fault
  changedPolicy = Validation.fault (Validation.key "retirement" ∷ []) Validation.wrongIdentity
    "The configured retention policy differs from the original sweep. Read its original binding and ask the user whether to restore that policy or explicitly cancel the unfinished action. Do not choose a new retention period or replace its plan."

  afterPolicy : Call → Wire.Value → Settings → E.Script Result
  afterPolicy call settings (unavailable fault) = E.done (needsInput fault)
  afterPolicy call settings (configured current) with Controls.PostgreSQL.jsonbEqual postgres settings current
  ... | false = E.done (needsInput changedPolicy)
  ... | true = createPlan call settings

  needsPolicy : Tools.Tool → Bool
  needsPolicy Tools.sweepExpiredDefeated = true
  needsPolicy _ = false

  beforePlan : Call → Wire.Value → E.Script Result
  beforePlan call settings with needsPolicy (Call.tool call)
  ... | true = E.ask (currentSettings call) (afterPolicy call settings)
  ... | false = createPlan call settings

  resume : Call → Wire.Value → Read.Result → E.Script Result
  resume call settings (Read.awaitingPlan _) = beforePlan call settings
  resume call settings (Read.awaitingCompletion _) = beforePlan call settings
  resume call settings (Read.pending _ _ _) = beforePlan call settings
  resume call settings completedOutcome = E.done (returned completedOutcome)

  readOutcome : Call → Wire.Value → E.Script Result
  readOutcome call settings = E.ask (readResult call) (λ observed → resume call settings (Read.answer (Call.token call) observed))

  afterBinding : Call → Wire.Value → ℤ × BindingResult → E.Script Result
  afterBinding call settings (observedTime , bound _) = readOutcome call settings
  afterBinding call settings (observedTime , changed _) = E.done (needsInput changedRequest)
  afterBinding call settings (observedTime , unknown) = E.ask (readResult call) (λ observed → E.done (returned (Read.answer (Call.token call) observed)))
  afterBinding call settings (observedTime , cancelled _) = E.ask (readResult call) (λ observed → E.done (returned (Read.answer (Call.token call) observed)))

  bindRequest : Call → Wire.Value → E.Script Result
  bindRequest call settings = E.ask (bindOriginal call settings) (afterBinding call settings)

  afterSettings : Call → Settings → E.Script Result
  afterSettings call (unavailable fault) = E.done (needsInput fault)
  afterSettings call (configured settings) with Public.freshLearningAdmission (Call.request call)
  ... | inj₁ fault = E.done (needsInput fault)
  ... | inj₂ tt = bindRequest call settings

  unbound : Call → Store.World → Read.Result → E.Script Result
  unbound call observed Read.reserved = E.ask (currentSettings call) (afterSettings call)
  unbound call observed outcome = E.done (returned outcome)

  afterOriginal : Call → Store.World → E.Script Result
  afterOriginal call observed with binding (Call.token call) observed
  ... | just original = bindRequest call (Store.BindingRow.settings original)
  ... | nothing = unbound call observed (Read.answer (Call.token call) observed)

  start : Call → E.Script Result
  start call = E.ask (readOriginal call) (afterOriginal call)

  script : Request → E.Script Result
  script requested with decode requested
  ... | inj₁ fault = E.done (needsInput fault)
  ... | inj₂ call = start call

  effectCall : Effect → Call
  effectCall (readOriginal call) = call
  effectCall (currentSettings call) = call
  effectCall (bindOriginal call _) = call
  effectCall (readResult call) = call
  effectCall (publishPlan call _) = call

  atomicFrame : ∀ before effect reply after → Atomic before effect reply after → Frame (effectCall effect) before after
  atomicFrame before (readOriginal call) observed after (same , unchanged) =
    subst (Frame call before) (sym unchanged) (identityFrame call before)
  atomicFrame before (currentSettings call) observed after unchanged =
    subst (Frame call before) (sym unchanged) (identityFrame call before)
  atomicFrame before (readResult call) observed after (same , unchanged) =
    subst (Frame call before) (sym unchanged) (identityFrame call before)
  atomicFrame before (bindOriginal call settings) (observedTime , reply) after (same , publication) =
    DB.invariantPreserved (Frame call before) publication (identityFrame call before) (bindFrame call settings observedTime before)
  atomicFrame before (publishPlan call settings) (encodedPlan , reply , validated) after (same , publication) =
    DB.invariantPreserved (Frame call before) publication (identityFrame call before) (planFrame call settings encodedPlan before)

  data Scoped (call : Call) : E.Script Result → Set where
    finished : ∀ result → Scoped call (E.done result)
    asked : ∀ effect next → effectCall effect ≡ call →
      (∀ observed → Scoped call (next observed)) → Scoped call (E.ask effect next)

  afterPlanScoped : ∀ call reply → Scoped call (afterPlan call reply)
  afterPlanScoped call (planned original model raw) = finished _
  afterPlanScoped call (planRefused fault) = finished _
  afterPlanScoped call (planCancelled receipt) = asked _ _ refl (λ _ → finished _)
  afterPlanScoped call planUnknown = asked _ _ refl (λ _ → finished _)

  createPlanScoped : ∀ call settings → Scoped call (createPlan call settings)
  createPlanScoped call settings = asked _ _ refl (λ observed → afterPlanScoped call (proj₁ (proj₂ observed)))

  afterPolicyScoped : ∀ call settings observed → Scoped call (afterPolicy call settings observed)
  afterPolicyScoped call settings (unavailable fault) = finished _
  afterPolicyScoped call settings (configured current) with Controls.PostgreSQL.jsonbEqual postgres settings current
  ... | false = finished _
  ... | true = createPlanScoped call settings

  beforePlanScoped : ∀ call settings → Scoped call (beforePlan call settings)
  beforePlanScoped call settings with needsPolicy (Call.tool call)
  ... | true = asked _ _ refl (afterPolicyScoped call settings)
  ... | false = createPlanScoped call settings

  resumeScoped : ∀ call settings result → Scoped call (resume call settings result)
  resumeScoped call settings (Read.awaitingPlan _) = beforePlanScoped call settings
  resumeScoped call settings (Read.awaitingCompletion _) = beforePlanScoped call settings
  resumeScoped call settings (Read.pending _ _ _) = beforePlanScoped call settings
  resumeScoped call settings Read.unknownToken = finished _
  resumeScoped call settings Read.reserved = finished _
  resumeScoped call settings (Read.completed _ _) = finished _
  resumeScoped call settings (Read.needsRecovery _) = finished _
  resumeScoped call settings (Read.inconsistent _ _) = finished _
  resumeScoped call settings (Read.cancelled _ _ _) = finished _

  readOutcomeScoped : ∀ call settings → Scoped call (readOutcome call settings)
  readOutcomeScoped call settings = asked _ _ refl (λ observed → resumeScoped call settings (Read.answer (Call.token call) observed))

  afterBindingScoped : ∀ call settings observed → Scoped call (afterBinding call settings observed)
  afterBindingScoped call settings (observedTime , bound _) = readOutcomeScoped call settings
  afterBindingScoped call settings (observedTime , changed _) = finished _
  afterBindingScoped call settings (observedTime , unknown) = asked _ _ refl (λ observed → finished _)
  afterBindingScoped call settings (observedTime , cancelled _) = asked _ _ refl (λ observed → finished _)

  bindRequestScoped : ∀ call settings → Scoped call (bindRequest call settings)
  bindRequestScoped call settings = asked _ _ refl (afterBindingScoped call settings)

  afterSettingsScoped : ∀ call observed → Scoped call (afterSettings call observed)
  afterSettingsScoped call (unavailable fault) = finished _
  afterSettingsScoped call (configured settings) with Public.freshLearningAdmission (Call.request call)
  ... | inj₁ fault = finished _
  ... | inj₂ tt = bindRequestScoped call settings

  unboundScoped : ∀ call before outcome → Scoped call (unbound call before outcome)
  unboundScoped call before Read.reserved = asked _ _ refl (afterSettingsScoped call)
  unboundScoped call before Read.unknownToken = finished _
  unboundScoped call before (Read.awaitingPlan _) = finished _
  unboundScoped call before (Read.awaitingCompletion _) = finished _
  unboundScoped call before (Read.pending _ _ _) = finished _
  unboundScoped call before (Read.completed _ _) = finished _
  unboundScoped call before (Read.needsRecovery _) = finished _
  unboundScoped call before (Read.inconsistent _ _) = finished _
  unboundScoped call before (Read.cancelled _ _ _) = finished _

  afterOriginalScoped : ∀ call before → Scoped call (afterOriginal call before)
  afterOriginalScoped call before with binding (Call.token call) before
  ... | just original = bindRequestScoped call (Store.BindingRow.settings original)
  ... | nothing = unboundScoped call before (Read.answer (Call.token call) before)

  startScoped : ∀ call → Scoped call (start call)
  startScoped call = asked _ _ refl (afterOriginalScoped call)

  prefixFrame : ∀ call (program : E.Script Result) → Scoped call program →
    ∀ before events residual after → E.Prefix program events residual → X.Changes before events after →
    Frame call before after × Scoped call residual
  prefixFrame call program owned before [] .program .before (E.stopped _) (X.unchanged _) = identityFrame call before , owned
  prefixFrame call (E.ask effect next) (asked .effect .next same later) before _ residual after
    (E.replied .effect .next observed prefix) (X.changed _ _ _ middle physical changes)
    with prefixFrame call (next observed) (later observed) middle _ residual after prefix changes
  ... | restFrame , residualScoped = composeFrame call before middle after
    (subst (λ owner → Frame owner before middle) same (atomicFrame before effect observed middle physical)) restFrame , residualScoped

  interruptedStartFrame : ∀ call before interrupted → X.Interrupted (start call) before interrupted → Frame call before interrupted
  interruptedStartFrame call before interrupted (X.atPrefix events residual .interrupted prefix changes) =
    proj₁ (prefixFrame call (start call) (startScoped call) before events residual interrupted prefix changes)
  interruptedStartFrame call before interrupted
    (X.beforeReply events effect next current observed .interrupted prefix changes physical)
    with prefixFrame call (start call) (startScoped call) before events (E.ask effect next) current prefix changes
  ... | earlier , asked .effect .next same later = composeFrame call before current interrupted earlier
    (subst (λ owner → Frame owner current interrupted) same (atomicFrame current effect observed interrupted physical))

  completedStartFrame : ∀ call before after reply → X.Completed (start call) before after reply → Frame call before after
  completedStartFrame call before after reply completedRun = interruptedStartFrame call before after
    (X.completedRunMayLoseFinalReply (start call) before after reply completedRun)

  computedExecutable : ∀ call model → computedPlan call ≡ inj₂ model → P.executable library model ≡ true
  computedExecutable call model accepted with P.lookup (Call.name call) P.registered
  ... | nothing with accepted
  ... | ()
  computedExecutable call model accepted | just shape with P.rebuild library shape (selected (Call.request call))
  ... | nothing with accepted
  ... | ()
  computedExecutable call model accepted | just shape | just steps with P.executable library (P.saved (Call.name call) shape steps nothing) in valid
  ... | false with accepted
  ... | ()
  computedExecutable call model accepted | just shape | just steps | true with accepted
  ... | refl = valid

  computedOperation : ∀ call model → computedPlan call ≡ inj₂ model → P.Saved.operation model ≡ Call.name call
  computedOperation call model accepted with P.lookup (Call.name call) P.registered
  ... | nothing with accepted
  ... | ()
  computedOperation call model accepted | just shape with P.rebuild library shape (selected (Call.request call))
  ... | nothing with accepted
  ... | ()
  computedOperation call model accepted | just shape | just steps with P.executable library (P.saved (Call.name call) shape steps nothing)
  ... | false with accepted
  ... | ()
  computedOperation call model accepted | just shape | just steps | true with accepted
  ... | refl = refl

  sameOperation : ∀ name → P.textEqual name name ≡ true
  sameOperation name with name ≟Text name
  ... | yes _ = refl
  ... | no different = ⊥-elim (different refl)

  headPlan : ∀ call raw before → plan (Call.token call) (putPlan (Call.token call) raw before) ≡ just raw
  headPlan call raw before with Call.token call ≟ Call.token call
  ... | yes _ = refl
  ... | no different = ⊥-elim (different refl)

  record ReadyMeaning (call : Call) (after : Store.World) (context : Context) : Set where
    field actualCall : Context.call context ≡ call
          boundRequest : binding (Call.token call) after ≡ just (Context.original context)
          originalArguments : Σ Wire.Value (λ settings → matches call settings (Context.original context) ≡ true)
          savedPlan : plan (Call.token call) after ≡ just (Context.raw context)
          decodedPlan : P.decode (Context.raw context) ≡ inj₂ (Context.model context)
          planOperationMatches : P.textEqual (Store.BindingRow.operation (Context.original context))
            (P.Saved.operation (Context.model context)) ≡ true
          executable : P.executable library (Context.model context) ≡ true
          uncancelled : Store.lookupCancellation after (Call.token call) ≡ nothing
          addresses : Controls.Addressing (P.Saved.steps (Context.model context))
          separateResult : All (λ boundary → P.Step.id boundary ≢ Step.resultKey) (P.Saved.steps (Context.model context))

  readyOperation : ∀ call after context → ReadyMeaning call after context →
    Store.BindingRow.operation (Context.original context) ≡ Call.name call
  readyOperation call after context meaning = matchingOperation call
    (proj₁ (ReadyMeaning.originalArguments meaning)) (Context.original context)
    (proj₂ (ReadyMeaning.originalArguments meaning))

  -- Resumption is different from inspecting a completed saved answer. The
  -- body's recovery proof starts only where no final answer has been saved.
  Resumable : Read.Result → Set
  Resumable (Read.awaitingPlan _) = ⊤
  Resumable (Read.awaitingCompletion _) = ⊤
  Resumable (Read.pending _ _ _) = ⊤
  Resumable _ = ⊥

  afterPrefixResumable : ∀ original model receipts remaining saved →
    Resumable (Read.afterPrefix original model receipts remaining saved) → saved ≡ nothing
  afterPrefixResumable original model receipts [] (just saved) ()
  afterPrefixResumable original model receipts (_ ∷ _) (just saved) ()
  afterPrefixResumable original model receipts remaining nothing possible = refl

  afterPlanResumable : ∀ original model rows → Resumable (Read.afterPlan original model rows) →
    Read.find Step.resultKey rows ≡ nothing
  afterPlanResumable original model rows possible with P.textEqual (Store.BindingRow.operation original) (P.Saved.operation model)
  ... | false with possible
  ... | ()
  afterPlanResumable original model rows possible | true with P.valid library model
  ... | false with possible
  ... | ()
  afterPlanResumable original model rows possible | true | true with Read.prefix (P.Saved.steps model) rows
  ... | receipts , remaining with Data.List.length (Data.List.filterᵇ Read.notFinal rows) ≟ Data.List.length receipts
  ... | no _ with possible
  ... | ()
  afterPlanResumable original model rows possible | true | true | receipts , remaining | yes _ =
    afterPrefixResumable original model receipts remaining (Read.find Step.resultKey rows) possible

  emptySavedRowsAbsent : ∀ token before → Read.savedRows token before ≡ [] →
    Store.lookupSaved before token Step.resultKey ≡ nothing
  emptySavedRowsAbsent token before emptyRows = trans
    (sym (Read.findReply token Step.resultKey (Store.OperationTables.savedReplies (Store.World.operations before))))
    (cong (λ rows → Read.replyValue (Read.find Step.resultKey rows)) emptyRows)

  inspectResumableAbsent : ∀ token original before → Resumable (Read.inspectBound token original before) →
    Store.lookupSaved before token Step.resultKey ≡ nothing
  inspectResumableAbsent token original before possible with Store.lookupCancellation before token
  ... | just _ with possible
  ... | ()
  inspectResumableAbsent token original before possible | nothing with plan token before
  ... | nothing with Read.savedRows token before in rows
  ... | [] = emptySavedRowsAbsent token before rows
  ... | _ ∷ _ with possible
  ... | ()
  inspectResumableAbsent token original before possible | nothing | just raw with P.decode raw
  ... | inj₁ _ with possible
  ... | ()
  inspectResumableAbsent token original before possible | nothing | just raw | inj₂ model = trans
    (sym (Read.findReply token Step.resultKey (Store.OperationTables.savedReplies (Store.World.operations before))))
    (cong Read.replyValue (afterPlanResumable original model (Read.savedRows token before) possible))

  resumableAbsent : ∀ token before → Resumable (Read.answer token before) →
    Store.lookupSaved before token Step.resultKey ≡ nothing
  resumableAbsent token before possible with binding token before
  ... | just original = inspectResumableAbsent token original before possible
  ... | nothing with Store.lookupCancellation before token
  ... | just _ with possible
  ... | ()
  resumableAbsent token before possible | nothing | nothing with Controls.reservation token before
  ... | just _ with possible
  ... | ()
  resumableAbsent token before possible | nothing | nothing | nothing with possible
  ... | ()

  prefixKeepsAnswer : ∀ call before after token key → Frame call before after →
    Store.lookupSaved after token key ≡ Store.lookupSaved before token key
  prefixKeepsAnswer call before after token key framed =
    cong (λ state → Store.lookupSaved state token key) (Frame.business framed)

  AbsentWhenReady : Call → Store.World → Result → Set
  AbsentWhenReady call after (ready _) = Store.lookupSaved after (Call.token call) Step.resultKey ≡ nothing
  AbsentWhenReady call after _ = ⊤

  readbackReadyAbsent : ∀ call before after result →
    X.Completed (E.ask (readResult call) (λ observed → E.done (returned (Read.answer (Call.token call) observed)))) before after result →
    AbsentWhenReady call after result
  readbackReadyAbsent call before .before .(returned (Read.answer (Call.token call) before))
    (X.completed _ (E.replied _ _ .before (E.returned _))
      (X.changed _ _ _ .before (refl , refl) (X.unchanged _))) = tt

  afterPlanReadyAbsent : ∀ call planResult before after result →
    Store.lookupSaved before (Call.token call) Step.resultKey ≡ nothing →
    X.Completed (afterPlan call planResult) before after result → AbsentWhenReady call after result
  afterPlanReadyAbsent call (planned original model raw) before .before .(ready (preparedWrite call original model raw)) absent
    (X.completed [] (E.returned _) (X.unchanged _)) = absent
  afterPlanReadyAbsent call (planRefused fault) before .before .(needsInput fault) absent
    (X.completed [] (E.returned _) (X.unchanged _)) = tt
  afterPlanReadyAbsent call (planCancelled receipt) before after result absent completion = readbackReadyAbsent call before after result completion
  afterPlanReadyAbsent call planUnknown before after result absent completion = readbackReadyAbsent call before after result completion

  createPlanReadyAbsent : ∀ call settings before after result →
    Store.lookupSaved before (Call.token call) Step.resultKey ≡ nothing →
    X.Completed (createPlan call settings) before after result → AbsentWhenReady call after result
  createPlanReadyAbsent call settings before after result absent
    (X.completed _ (E.replied _ _ (encoding , planResult , validated) execution) (X.changed _ _ _ middle physical changes)) =
    afterPlanReadyAbsent call planResult middle after result
      (trans (prefixKeepsAnswer call before middle (Call.token call) Step.resultKey
        (atomicFrame before (publishPlan call settings) (encoding , planResult , validated) middle physical)) absent)
      (X.completed _ execution changes)

  afterPolicyReadyAbsent : ∀ call settings observed before after result →
    Store.lookupSaved before (Call.token call) Step.resultKey ≡ nothing →
    X.Completed (afterPolicy call settings observed) before after result → AbsentWhenReady call after result
  afterPolicyReadyAbsent call settings (unavailable fault) before .before .(needsInput fault) absent
    (X.completed [] (E.returned _) (X.unchanged _)) = tt
  afterPolicyReadyAbsent call settings (configured current) before after result absent completion
    with Controls.PostgreSQL.jsonbEqual postgres settings current
  ... | true = createPlanReadyAbsent call settings before after result absent completion
  ... | false with completion
  ... | X.completed [] (E.returned _) (X.unchanged _) = tt

  beforePlanReadyAbsent : ∀ call settings before after result →
    Store.lookupSaved before (Call.token call) Step.resultKey ≡ nothing →
    X.Completed (beforePlan call settings) before after result → AbsentWhenReady call after result
  beforePlanReadyAbsent call settings before after result absent completion with needsPolicy (Call.tool call)
  ... | false = createPlanReadyAbsent call settings before after result absent completion
  ... | true with completion
  ... | X.completed _ (E.replied _ _ observed execution) (X.changed _ _ _ .before refl changes) =
    afterPolicyReadyAbsent call settings observed before after result absent (X.completed _ execution changes)

  resumeReadyAbsent : ∀ call settings outcome before after result → Read.answer (Call.token call) before ≡ outcome →
    X.Completed (resume call settings outcome) before after result → AbsentWhenReady call after result
  resumeReadyAbsent call settings (Read.awaitingPlan original) before after result observed completion =
    beforePlanReadyAbsent call settings before after result
      (resumableAbsent (Call.token call) before (subst Resumable (sym observed) tt)) completion
  resumeReadyAbsent call settings (Read.awaitingCompletion original) before after result observed completion =
    beforePlanReadyAbsent call settings before after result
      (resumableAbsent (Call.token call) before (subst Resumable (sym observed) tt)) completion
  resumeReadyAbsent call settings (Read.pending original nextStep replies) before after result observed completion =
    beforePlanReadyAbsent call settings before after result
      (resumableAbsent (Call.token call) before (subst Resumable (sym observed) tt)) completion
  resumeReadyAbsent call settings Read.unknownToken before .before .(returned Read.unknownToken) observed
    (X.completed [] (E.returned _) (X.unchanged _)) = tt
  resumeReadyAbsent call settings Read.reserved before .before .(returned Read.reserved) observed
    (X.completed [] (E.returned _) (X.unchanged _)) = tt
  resumeReadyAbsent call settings (Read.completed original value) before .before .(returned (Read.completed original value)) observed
    (X.completed [] (E.returned _) (X.unchanged _)) = tt
  resumeReadyAbsent call settings (Read.cancelled receipt original replies) before .before .(returned (Read.cancelled receipt original replies)) observed
    (X.completed [] (E.returned _) (X.unchanged _)) = tt
  resumeReadyAbsent call settings (Read.needsRecovery original) before .before .(returned (Read.needsRecovery original)) observed
    (X.completed [] (E.returned _) (X.unchanged _)) = tt
  resumeReadyAbsent call settings (Read.inconsistent original problem) before .before .(returned (Read.inconsistent original problem)) observed
    (X.completed [] (E.returned _) (X.unchanged _)) = tt

  readOutcomeReadyAbsent : ∀ call settings before after result →
    X.Completed (readOutcome call settings) before after result → AbsentWhenReady call after result
  readOutcomeReadyAbsent call settings before after result
    (X.completed _ (E.replied _ _ .before execution) (X.changed _ _ _ .before (refl , refl) changes)) =
    resumeReadyAbsent call settings (Read.answer (Call.token call) before) before after result refl (X.completed _ execution changes)

  afterBindingReadyAbsent : ∀ call settings observed before after result →
    X.Completed (afterBinding call settings observed) before after result → AbsentWhenReady call after result
  afterBindingReadyAbsent call settings (time , bound original) before after result completion = readOutcomeReadyAbsent call settings before after result completion
  afterBindingReadyAbsent call settings (time , unknown) before after result completion = readbackReadyAbsent call before after result completion
  afterBindingReadyAbsent call settings (time , cancelled receipt) before after result completion = readbackReadyAbsent call before after result completion
  afterBindingReadyAbsent call settings (time , changed original) before .before .(needsInput changedRequest)
    (X.completed [] (E.returned _) (X.unchanged _)) = tt

  bindRequestReadyAbsent : ∀ call settings before after result →
    X.Completed (bindRequest call settings) before after result → AbsentWhenReady call after result
  bindRequestReadyAbsent call settings before after result
    (X.completed _ (E.replied _ _ observed execution) (X.changed _ _ _ middle physical changes)) =
    afterBindingReadyAbsent call settings observed middle after result (X.completed _ execution changes)

  afterSettingsReadyAbsent : ∀ call observed before after result →
    X.Completed (afterSettings call observed) before after result → AbsentWhenReady call after result
  afterSettingsReadyAbsent call (configured settings) before after result completion with Public.freshLearningAdmission (Call.request call)
  ... | inj₁ fault with completion
  ... | X.completed [] (E.returned _) (X.unchanged _) = tt
  afterSettingsReadyAbsent call (configured settings) before after result completion | inj₂ tt =
    bindRequestReadyAbsent call settings before after result completion
  afterSettingsReadyAbsent call (unavailable fault) before .before .(needsInput fault)
    (X.completed [] (E.returned _) (X.unchanged _)) = tt

  unboundReadyAbsent : ∀ call outcome observed before after result →
    X.Completed (unbound call observed outcome) before after result → AbsentWhenReady call after result
  unboundReadyAbsent call Read.reserved observed before after result
    (X.completed _ (E.replied _ _ settings execution) (X.changed _ _ _ .before refl changes)) =
    afterSettingsReadyAbsent call settings before after result (X.completed _ execution changes)
  unboundReadyAbsent call Read.unknownToken observed before .before .(returned Read.unknownToken) (X.completed [] (E.returned _) (X.unchanged _)) = tt
  unboundReadyAbsent call (Read.awaitingPlan original) observed before .before .(returned (Read.awaitingPlan original)) (X.completed [] (E.returned _) (X.unchanged _)) = tt
  unboundReadyAbsent call (Read.awaitingCompletion original) observed before .before .(returned (Read.awaitingCompletion original)) (X.completed [] (E.returned _) (X.unchanged _)) = tt
  unboundReadyAbsent call (Read.pending original nextStep replies) observed before .before .(returned (Read.pending original nextStep replies)) (X.completed [] (E.returned _) (X.unchanged _)) = tt
  unboundReadyAbsent call (Read.completed original value) observed before .before .(returned (Read.completed original value)) (X.completed [] (E.returned _) (X.unchanged _)) = tt
  unboundReadyAbsent call (Read.cancelled receipt original replies) observed before .before .(returned (Read.cancelled receipt original replies)) (X.completed [] (E.returned _) (X.unchanged _)) = tt
  unboundReadyAbsent call (Read.needsRecovery original) observed before .before .(returned (Read.needsRecovery original)) (X.completed [] (E.returned _) (X.unchanged _)) = tt
  unboundReadyAbsent call (Read.inconsistent original problem) observed before .before .(returned (Read.inconsistent original problem)) (X.completed [] (E.returned _) (X.unchanged _)) = tt

  afterOriginalReadyAbsent : ∀ call observed before after result →
    X.Completed (afterOriginal call observed) before after result → AbsentWhenReady call after result
  afterOriginalReadyAbsent call observed before after result completion with binding (Call.token call) observed
  ... | just original = bindRequestReadyAbsent call (Store.BindingRow.settings original) before after result completion
  ... | nothing = unboundReadyAbsent call (Read.answer (Call.token call) observed) observed before after result completion

  startReadyAbsent : ∀ call before after context →
    X.Completed (start call) before after (ready context) →
    Store.lookupSaved after (Call.token call) Step.resultKey ≡ nothing
  startReadyAbsent call before after context
    (X.completed _ (E.replied _ _ .before execution) (X.changed _ _ _ .before (refl , refl) changes)) =
    afterOriginalReadyAbsent call before before after (ready context) (X.completed _ execution changes)

  completedReadyResultAbsent : ∀ requested call before after context → decode requested ≡ inj₂ call →
    X.Completed (script requested) before after (ready context) →
    Store.lookupSaved after (Call.token call) Step.resultKey ≡ nothing
  completedReadyResultAbsent requested call before after context decoded completion rewrite decoded =
    startReadyAbsent call before after context completion

  data ReplyMeaning (call : Call) (after : Store.World) : Result → Set where
    dialogue : ∀ fault → ReplyMeaning call after (needsInput fault)
    originalReadback : ∀ outcome → Read.answer (Call.token call) after ≡ outcome → ReplyMeaning call after (returned outcome)
    originalPlan : ∀ context → ReadyMeaning call after context → ReplyMeaning call after (ready context)

  Goal : Request → Store.World → Store.World → Result → Set
  Goal requested before after reply with decode requested
  ... | inj₁ fault = after ≡ before × reply ≡ needsInput fault
  ... | inj₂ call = Frame call before after × ReplyMeaning call after reply

  existingReady : ∀ call settings before original raw returnedOriginal returnedModel returnedRaw →
    binding (Call.token call) before ≡ just original → matches call settings original ≡ true →
    plan (Call.token call) before ≡ just raw →
    Store.lookupCancellation before (Call.token call) ≡ nothing →
    existingPlan original raw ≡ planned returnedOriginal returnedModel returnedRaw →
    PlanValidation (planned returnedOriginal returnedModel returnedRaw) →
    ReadyMeaning call before (preparedWrite call returnedOriginal returnedModel returnedRaw)
  existingReady call settings before original raw returnedOriginal returnedModel returnedRaw known matched stored active accepted validated
    with P.decode raw in decoded
  ... | inj₁ _ with accepted
  ... | ()
  existingReady call settings before original raw returnedOriginal returnedModel returnedRaw known matched stored active accepted validated | inj₂ model
    with P.textEqual (Store.BindingRow.operation original) (P.Saved.operation model) in sameName
  ... | false with accepted
  ... | ()
  existingReady call settings before original raw returnedOriginal returnedModel returnedRaw known matched stored active accepted validated | inj₂ model | true
    with P.executable library model in valid
  ... | false with accepted
  ... | ()
  existingReady call settings before original raw returnedOriginal returnedModel returnedRaw known matched stored active accepted validated | inj₂ model | true | true
    with accepted
  ... | refl = record
    { actualCall = refl; boundRequest = known; originalArguments = settings , matched
    ; savedPlan = stored; decodedPlan = decoded; planOperationMatches = sameName; executable = valid; uncancelled = active
    ; addresses = proj₁ (proj₂ validated); separateResult = proj₂ (proj₂ validated) }

  newPlanReady : ∀ call settings original encoding before after returnedOriginal returnedModel returnedRaw →
    binding (Call.token call) before ≡ just original → matches call settings original ≡ true →
    Store.lookupCancellation before (Call.token call) ≡ nothing →
    (after , planned returnedOriginal returnedModel returnedRaw) ≡ saveNewPlan call original encoding before →
    PlanValidation (planned returnedOriginal returnedModel returnedRaw) →
    ReadyMeaning call after (preparedWrite call returnedOriginal returnedModel returnedRaw)
  newPlanReady call settings original (encodingFailed fault) before after returnedOriginal returnedModel returnedRaw known matched active () validated
  newPlanReady call settings original (encoded model computed raw decoded) before after returnedOriginal returnedModel returnedRaw known matched active accepted validated
    with accepted
  ... | refl = record
    { actualCall = refl; boundRequest = known; originalArguments = settings , matched
    ; savedPlan = headPlan call raw before; decodedPlan = decoded
    ; planOperationMatches = trans (cong (λ name → P.textEqual name (P.Saved.operation model)) (matchingOperation call settings original matched))
        (trans (cong (P.textEqual (Call.name call)) (computedOperation call model computed)) (sameOperation (Call.name call)))
    ; executable = computedExecutable call model computed; uncancelled = active
    ; addresses = proj₁ (proj₂ validated); separateResult = proj₂ (proj₂ validated) }

  prepareReady : ∀ call settings encoding before after original model raw →
    (after , planned original model raw) ≡ prepare call settings encoding before →
    PlanValidation (planned original model raw) →
    ReadyMeaning call after (preparedWrite call original model raw)
  prepareReady call settings encoding before after original model raw accepted validated
    with binding (Call.token call) before in known
  ... | nothing with accepted
  ... | ()
  prepareReady call settings encoding before after original model raw accepted validated | just boundRow
    with matches call settings boundRow in matched
  ... | false with accepted
  ... | ()
  prepareReady call settings encoding before after original model raw accepted validated | just boundRow | true
    with Store.lookupCancellation before (Call.token call) in active
  ... | just _ with accepted
  ... | ()
  prepareReady call settings encoding before after original model raw accepted validated | just boundRow | true | nothing
    with plan (Call.token call) before in stored
  ... | just old = subst (λ state → ReadyMeaning call state (preparedWrite call original model raw))
    (sym (cong proj₁ accepted))
    (existingReady call settings before boundRow old original model raw known matched stored active (sym (cong proj₂ accepted)) validated)
  prepareReady call settings encoding before after original model raw accepted validated | just boundRow | true | nothing | nothing
    with Read.savedRows (Call.token call) before
  ... | _ ∷ _ with accepted
  ... | ()
  prepareReady call settings encoding before after original model raw accepted validated | just boundRow | true | nothing | nothing | [] =
    newPlanReady call settings boundRow encoding before after original model raw known matched active accepted validated

  prepareAtomicReady : ∀ call settings encoding reply (validated : PlanValidation reply) before after →
    Atomic before (publishPlan call settings) (encoding , reply , validated) after →
    ∀ original model raw → reply ≡ planned original model raw →
    ReadyMeaning call after (preparedWrite call original model raw)
  prepareAtomicReady call settings encoding .(planned original model raw) validated before ._ (accepted , DB.committedAll)
    original model raw refl = prepareReady call settings encoding before _ original model raw
      (cong (λ result → proj₁ (prepare call settings encoding before) , result) accepted) validated

  readbackCompletion : ∀ call before after reply →
    X.Completed (E.ask (readResult call) (λ observed → E.done (returned (Read.answer (Call.token call) observed)))) before after reply →
    ReplyMeaning call after reply
  readbackCompletion call before .before .(returned (Read.answer (Call.token call) before))
    (X.completed _ (E.replied _ _ .before (E.returned _))
      (X.changed _ _ _ .before (refl , refl) (X.unchanged _))) = originalReadback _ refl

  afterPlanMeaning : ∀ call planResult before after reply →
    (∀ original model raw → planResult ≡ planned original model raw → ReadyMeaning call before (preparedWrite call original model raw)) →
    X.Completed (afterPlan call planResult) before after reply → ReplyMeaning call after reply
  afterPlanMeaning call (planned original model raw) before .before .(ready (preparedWrite call original model raw)) facts
    (X.completed [] (E.returned _) (X.unchanged _)) = originalPlan _ (facts original model raw refl)
  afterPlanMeaning call (planRefused fault) before .before .(needsInput fault) facts
    (X.completed [] (E.returned _) (X.unchanged _)) = dialogue fault
  afterPlanMeaning call (planCancelled receipt) before after reply facts completion = readbackCompletion call before after reply completion
  afterPlanMeaning call planUnknown before after reply facts completion = readbackCompletion call before after reply completion

  createPlanMeaning : ∀ call settings before after reply → X.Completed (createPlan call settings) before after reply → ReplyMeaning call after reply
  createPlanMeaning call settings before after reply
    (X.completed _ (E.replied _ _ (encoding , result , validated) execution) (X.changed _ _ _ middle physical changes)) =
    afterPlanMeaning call result middle after reply
      (prepareAtomicReady call settings encoding result validated before middle physical) (X.completed _ execution changes)

  afterPolicyMeaning : ∀ call settings observed before after reply →
    X.Completed (afterPolicy call settings observed) before after reply → ReplyMeaning call after reply
  afterPolicyMeaning call settings (unavailable fault) before .before .(needsInput fault)
    (X.completed [] (E.returned _) (X.unchanged _)) = dialogue fault
  afterPolicyMeaning call settings (configured current) before after reply completion with Controls.PostgreSQL.jsonbEqual postgres settings current
  ... | true = createPlanMeaning call settings before after reply completion
  ... | false with completion
  ... | X.completed [] (E.returned _) (X.unchanged _) = dialogue changedPolicy

  beforePlanMeaning : ∀ call settings before after reply →
    X.Completed (beforePlan call settings) before after reply → ReplyMeaning call after reply
  beforePlanMeaning call settings before after reply completion with needsPolicy (Call.tool call)
  ... | false = createPlanMeaning call settings before after reply completion
  ... | true with completion
  ... | X.completed _ (E.replied _ _ observed execution) (X.changed _ _ _ .before refl changes) =
    afterPolicyMeaning call settings observed before after reply (X.completed _ execution changes)

  resumeMeaning : ∀ call settings before after reply →
    X.Completed (resume call settings (Read.answer (Call.token call) before)) before after reply → ReplyMeaning call after reply
  resumeMeaning call settings before after reply completion with Read.answer (Call.token call) before in observed
  ... | Read.awaitingPlan _ = beforePlanMeaning call settings before after reply completion
  ... | Read.awaitingCompletion _ = beforePlanMeaning call settings before after reply completion
  ... | Read.pending _ _ _ = beforePlanMeaning call settings before after reply completion
  ... | Read.unknownToken with completion
  ... | X.completed [] (E.returned _) (X.unchanged _) = originalReadback _ observed
  resumeMeaning call settings before after reply completion | Read.reserved with completion
  ... | X.completed [] (E.returned _) (X.unchanged _) = originalReadback _ observed
  resumeMeaning call settings before after reply completion | Read.completed _ _ with completion
  ... | X.completed [] (E.returned _) (X.unchanged _) = originalReadback _ observed
  resumeMeaning call settings before after reply completion | Read.cancelled _ _ _ with completion
  ... | X.completed [] (E.returned _) (X.unchanged _) = originalReadback _ observed
  resumeMeaning call settings before after reply completion | Read.needsRecovery _ with completion
  ... | X.completed [] (E.returned _) (X.unchanged _) = originalReadback _ observed
  resumeMeaning call settings before after reply completion | Read.inconsistent _ _ with completion
  ... | X.completed [] (E.returned _) (X.unchanged _) = originalReadback _ observed

  readOutcomeMeaning : ∀ call settings before after reply → X.Completed (readOutcome call settings) before after reply → ReplyMeaning call after reply
  readOutcomeMeaning call settings before after reply
    (X.completed _ (E.replied _ _ .before execution) (X.changed _ _ _ .before (refl , refl) changes)) =
    resumeMeaning call settings before after reply (X.completed _ execution changes)

  afterBindingMeaning : ∀ call settings observed before after reply →
    X.Completed (afterBinding call settings observed) before after reply → ReplyMeaning call after reply
  afterBindingMeaning call settings (observedTime , bound _) before after reply completion = readOutcomeMeaning call settings before after reply completion
  afterBindingMeaning call settings (observedTime , unknown) before after reply completion = readbackCompletion call before after reply completion
  afterBindingMeaning call settings (observedTime , cancelled _) before after reply completion = readbackCompletion call before after reply completion
  afterBindingMeaning call settings (observedTime , changed _) before .before .(needsInput changedRequest)
    (X.completed [] (E.returned _) (X.unchanged _)) = dialogue changedRequest

  bindRequestMeaning : ∀ call settings before after reply → X.Completed (bindRequest call settings) before after reply → ReplyMeaning call after reply
  bindRequestMeaning call settings before after reply
    (X.completed _ (E.replied _ _ observed execution) (X.changed _ _ _ middle physical changes)) =
    afterBindingMeaning call settings observed middle after reply (X.completed _ execution changes)

  afterSettingsMeaning : ∀ call observed before after reply →
    X.Completed (afterSettings call observed) before after reply → ReplyMeaning call after reply
  afterSettingsMeaning call (configured settings) before after reply completion with Public.freshLearningAdmission (Call.request call)
  ... | inj₁ fault with completion
  ... | X.completed [] (E.returned _) (X.unchanged _) = dialogue fault
  afterSettingsMeaning call (configured settings) before after reply completion | inj₂ tt =
    bindRequestMeaning call settings before after reply completion
  afterSettingsMeaning call (unavailable fault) before .before .(needsInput fault)
    (X.completed [] (E.returned _) (X.unchanged _)) = dialogue fault

  unboundMeaning : ∀ call before after reply →
    X.Completed (unbound call before (Read.answer (Call.token call) before)) before after reply → ReplyMeaning call after reply
  unboundMeaning call before after reply completion with Read.answer (Call.token call) before in observed
  ... | Read.reserved with completion
  ... | X.completed _ (E.replied _ _ settings execution) (X.changed _ _ _ .before refl changes) =
    afterSettingsMeaning call settings before after reply (X.completed _ execution changes)
  unboundMeaning call before after reply completion | Read.unknownToken with completion
  ... | X.completed [] (E.returned _) (X.unchanged _) = originalReadback _ observed
  unboundMeaning call before after reply completion | Read.awaitingPlan _ with completion
  ... | X.completed [] (E.returned _) (X.unchanged _) = originalReadback _ observed
  unboundMeaning call before after reply completion | Read.awaitingCompletion _ with completion
  ... | X.completed [] (E.returned _) (X.unchanged _) = originalReadback _ observed
  unboundMeaning call before after reply completion | Read.pending _ _ _ with completion
  ... | X.completed [] (E.returned _) (X.unchanged _) = originalReadback _ observed
  unboundMeaning call before after reply completion | Read.completed _ _ with completion
  ... | X.completed [] (E.returned _) (X.unchanged _) = originalReadback _ observed
  unboundMeaning call before after reply completion | Read.cancelled _ _ _ with completion
  ... | X.completed [] (E.returned _) (X.unchanged _) = originalReadback _ observed
  unboundMeaning call before after reply completion | Read.needsRecovery _ with completion
  ... | X.completed [] (E.returned _) (X.unchanged _) = originalReadback _ observed
  unboundMeaning call before after reply completion | Read.inconsistent _ _ with completion
  ... | X.completed [] (E.returned _) (X.unchanged _) = originalReadback _ observed

  afterOriginalMeaning : ∀ call before after reply →
    X.Completed (afterOriginal call before) before after reply → ReplyMeaning call after reply
  afterOriginalMeaning call before after reply completion with binding (Call.token call) before
  ... | just original = bindRequestMeaning call (Store.BindingRow.settings original) before after reply completion
  ... | nothing = unboundMeaning call before after reply completion

  completedMeaning : ∀ call before after reply → X.Completed (start call) before after reply → ReplyMeaning call after reply
  completedMeaning call before after reply
    (X.completed _ (E.replied _ _ .before execution) (X.changed _ _ _ .before (refl , refl) changes)) =
    afterOriginalMeaning call before after reply (X.completed _ execution changes)

  doneInterruptedSameWorld : ∀ (result : Result) before after → X.Interrupted (E.done result) before after → after ≡ before
  doneInterruptedSameWorld result before .before (X.atPrefix [] _ _ (E.stopped _) (X.unchanged _)) = refl
  doneInterruptedSameWorld result before after (X.beforeReply _ _ _ _ _ _ () _ _)

  completedGoal : ∀ requested before after reply → X.Completed (script requested) before after reply → Goal requested before after reply
  completedGoal requested before after reply completion with decode requested
  ... | inj₁ fault with completion
  ... | X.completed [] (E.returned _) (X.unchanged _) = refl , refl
  completedGoal requested before after reply completion | inj₂ call =
    completedStartFrame call before after reply completion , completedMeaning call before after reply completion

  converges : ∀ requested before interrupted after reply → X.Interrupted (script requested) before interrupted →
    X.Completed (script requested) interrupted after reply → Goal requested before after reply
  converges requested before interrupted after reply interruption completion with decode requested
  ... | inj₁ fault with completion
  ... | X.completed [] (E.returned _) (X.unchanged _) =
    doneInterruptedSameWorld (needsInput fault) before interrupted interruption , refl
  converges requested before interrupted after reply interruption completion | inj₂ call =
    composeFrame call before interrupted after (interruptedStartFrame call before interrupted interruption)
      (completedStartFrame call interrupted after reply completion) , completedMeaning call interrupted after reply completion

  bindingSamePhysical : ∀ (before : Store.World) reply → DB.Atomic before before (bindingReceipt reply) before
  bindingSamePhysical before (bound _) = DB.committedAll
  bindingSamePhysical before (changed _) = DB.committedAll
  bindingSamePhysical before unknown = DB.abortedNone
  bindingSamePhysical before (cancelled _) = DB.abortedNone
  planSamePhysical : ∀ (before : Store.World) reply → DB.Atomic before before (planReceipt reply) before
  planSamePhysical before (planned _ _ _) = DB.committedAll
  planSamePhysical before (planRefused _) = DB.abortedNone
  planSamePhysical before (planCancelled _) = DB.abortedNone
  planSamePhysical before planUnknown = DB.abortedNone

  bindPhysical : ∀ call settings observedTime before → DB.Atomic before
    (proj₁ (bind call settings observedTime before)) (bindingReceipt (proj₂ (bind call settings observedTime before)))
    (proj₁ (bind call settings observedTime before))
  bindPhysical call settings observedTime before with Controls.reservation (Call.token call) before
  ... | nothing = DB.abortedNone
  ... | just _ with Store.lookupCancellation before (Call.token call)
  ... | just _ = DB.abortedNone
  ... | nothing with binding (Call.token call) before
  ... | nothing = DB.committedAll
  ... | just original with matches call settings original
  ... | false = DB.committedAll
  ... | true = DB.committedAll

  preparePhysical : ∀ call settings encoding before → DB.Atomic before
    (proj₁ (prepare call settings encoding before)) (planReceipt (proj₂ (prepare call settings encoding before)))
    (proj₁ (prepare call settings encoding before))
  preparePhysical call settings encoding before with binding (Call.token call) before
  ... | nothing = DB.abortedNone
  ... | just original with matches call settings original
  ... | false = DB.abortedNone
  ... | true with Store.lookupCancellation before (Call.token call)
  ... | just _ = DB.abortedNone
  ... | nothing with plan (Call.token call) before
  ... | just raw = planSamePhysical before (existingPlan original raw)
  ... | nothing with Read.savedRows (Call.token call) before
  ... | _ ∷ _ = DB.abortedNone
  ... | [] with encoding
  ... | encodingFailed _ = DB.abortedNone
  ... | encoded model computed raw decoded = DB.committedAll

  -- These are only witnesses of available host/PG/library replies. They do
  -- not choose a goal, World, script, plan or client request. Atomic above
  -- accepts every actual reply, including different observations on retry.
  record Environment : Set where
    field settings : Call → Store.World → Settings
          bindingTime : Call → Store.World → ℤ
          encodePlan : ∀ call → Store.World → PlanEncoding call
          -- Actual host codec/build guarantees for this returned model,
          -- including a current executable plan read from existing metadata.
          validatePlan : ∀ call settings encoding before →
            PlanValidation (proj₂ (prepare call settings encoding before))

  doneProgress : ∀ result before → Σ Store.World (λ after → Σ Result (λ reply → X.Completed (E.done result) before after reply))
  doneProgress result before = before , result , X.completed [] (E.returned _) (X.unchanged _)

  readbackProgress : ∀ call before → Σ Store.World (λ after → Σ Result (λ reply →
    X.Completed (E.ask (readResult call) (λ observed → E.done (returned (Read.answer (Call.token call) observed)))) before after reply))
  readbackProgress call before = before , returned (Read.answer (Call.token call) before) , X.completed
    ((readResult call , before) ∷ []) (E.replied _ _ before (E.returned _))
    (X.changed before _ before before (refl , refl) (X.unchanged before))

  afterPlanProgress : ∀ call result before → Σ Store.World (λ after → Σ Result (λ reply → X.Completed (afterPlan call result) before after reply))
  afterPlanProgress call (planned original model raw) before = doneProgress _ before
  afterPlanProgress call (planRefused fault) before = doneProgress _ before
  afterPlanProgress call (planCancelled receipt) before = readbackProgress call before
  afterPlanProgress call planUnknown before = readbackProgress call before

  createPlanProgress : Environment → ∀ call settings before → Σ Store.World (λ after → Σ Result
    (λ reply → X.Completed (createPlan call settings) before after reply))
  createPlanProgress environment call settings before
    with afterPlanProgress call
      (proj₂ (prepare call settings (Environment.encodePlan environment call before) before))
      (proj₁ (prepare call settings (Environment.encodePlan environment call before) before))
  ... | after , reply , X.completed events execution changes = after , reply , X.completed
    ((publishPlan call settings , encoding , proj₂ expected , validated) ∷ events) (E.replied _ _ _ execution)
    (X.changed before _ _ _ (refl , preparePhysical call settings encoding before) changes)
    where encoding = Environment.encodePlan environment call before
          expected = prepare call settings encoding before
          validated = Environment.validatePlan environment call settings encoding before

  afterPolicyProgress : Environment → ∀ call settings observed before → Σ Store.World (λ after → Σ Result
    (λ reply → X.Completed (afterPolicy call settings observed) before after reply))
  afterPolicyProgress environment call settings (unavailable fault) before = doneProgress _ before
  afterPolicyProgress environment call settings (configured current) before with Controls.PostgreSQL.jsonbEqual postgres settings current
  ... | false = doneProgress _ before
  ... | true = createPlanProgress environment call settings before

  beforePlanProgress : Environment → ∀ call settings before → Σ Store.World (λ after → Σ Result
    (λ reply → X.Completed (beforePlan call settings) before after reply))
  beforePlanProgress environment call settings before with needsPolicy (Call.tool call)
  ... | false = createPlanProgress environment call settings before
  ... | true with afterPolicyProgress environment call settings (Environment.settings environment call before) before
  ... | after , reply , X.completed events execution changes = after , reply , X.completed
    ((currentSettings call , Environment.settings environment call before) ∷ events) (E.replied _ _ _ execution)
    (X.changed before _ _ before refl changes)

  resumeProgress : Environment → ∀ call settings outcome before → Σ Store.World (λ after → Σ Result
    (λ reply → X.Completed (resume call settings outcome) before after reply))
  resumeProgress environment call settings (Read.awaitingPlan _) before = beforePlanProgress environment call settings before
  resumeProgress environment call settings (Read.awaitingCompletion _) before = beforePlanProgress environment call settings before
  resumeProgress environment call settings (Read.pending _ _ _) before = beforePlanProgress environment call settings before
  resumeProgress environment call settings Read.unknownToken before = doneProgress _ before
  resumeProgress environment call settings Read.reserved before = doneProgress _ before
  resumeProgress environment call settings (Read.completed _ _) before = doneProgress _ before
  resumeProgress environment call settings (Read.cancelled _ _ _) before = doneProgress _ before
  resumeProgress environment call settings (Read.needsRecovery _) before = doneProgress _ before
  resumeProgress environment call settings (Read.inconsistent _ _) before = doneProgress _ before

  readOutcomeProgress : Environment → ∀ call settings before → Σ Store.World (λ after → Σ Result
    (λ reply → X.Completed (readOutcome call settings) before after reply))
  readOutcomeProgress environment call settings before with resumeProgress environment call settings (Read.answer (Call.token call) before) before
  ... | after , reply , X.completed events execution changes = after , reply , X.completed
    ((readResult call , before) ∷ events) (E.replied _ _ before execution)
    (X.changed before _ before before (refl , refl) changes)

  afterBindingProgress : Environment → ∀ call settings observed before → Σ Store.World (λ after → Σ Result
    (λ reply → X.Completed (afterBinding call settings observed) before after reply))
  afterBindingProgress environment call settings (observedTime , bound _) before = readOutcomeProgress environment call settings before
  afterBindingProgress environment call settings (observedTime , unknown) before = readbackProgress call before
  afterBindingProgress environment call settings (observedTime , cancelled _) before = readbackProgress call before
  afterBindingProgress environment call settings (observedTime , changed _) before = doneProgress _ before

  bindRequestProgress : Environment → ∀ call settings before → Σ Store.World (λ after → Σ Result
    (λ reply → X.Completed (bindRequest call settings) before after reply))
  bindRequestProgress environment call settings before
    with afterBindingProgress environment call settings
      (Environment.bindingTime environment call before , proj₂ (bind call settings (Environment.bindingTime environment call before) before))
      (proj₁ (bind call settings (Environment.bindingTime environment call before) before))
  ... | after , reply , X.completed events execution changes = after , reply , X.completed
    ((bindOriginal call settings , observedTime , proj₂ expected) ∷ events) (E.replied _ _ _ execution)
    (X.changed before _ _ _ (refl , bindPhysical call settings observedTime before) changes)
    where observedTime = Environment.bindingTime environment call before
          expected = bind call settings observedTime before

  afterSettingsProgress : Environment → ∀ call observed before → Σ Store.World (λ after → Σ Result
    (λ reply → X.Completed (afterSettings call observed) before after reply))
  afterSettingsProgress environment call (unavailable fault) before = doneProgress _ before
  afterSettingsProgress environment call (configured settings) before with Public.freshLearningAdmission (Call.request call)
  ... | inj₁ fault = doneProgress _ before
  ... | inj₂ tt = bindRequestProgress environment call settings before

  unboundProgress : Environment → ∀ call before outcome → Σ Store.World (λ after → Σ Result
    (λ reply → X.Completed (unbound call before outcome) before after reply))
  unboundProgress environment call before Read.reserved with afterSettingsProgress environment call (Environment.settings environment call before) before
  ... | after , reply , X.completed events execution changes = after , reply , X.completed
    ((currentSettings call , Environment.settings environment call before) ∷ events) (E.replied _ _ _ execution)
    (X.changed before _ _ before refl changes)
  unboundProgress environment call before Read.unknownToken = doneProgress _ before
  unboundProgress environment call before (Read.awaitingPlan _) = doneProgress _ before
  unboundProgress environment call before (Read.awaitingCompletion _) = doneProgress _ before
  unboundProgress environment call before (Read.pending _ _ _) = doneProgress _ before
  unboundProgress environment call before (Read.completed _ _) = doneProgress _ before
  unboundProgress environment call before (Read.cancelled _ _ _) = doneProgress _ before
  unboundProgress environment call before (Read.needsRecovery _) = doneProgress _ before
  unboundProgress environment call before (Read.inconsistent _ _) = doneProgress _ before

  afterOriginalProgress : Environment → ∀ call before → Σ Store.World (λ after → Σ Result
    (λ reply → X.Completed (afterOriginal call before) before after reply))
  afterOriginalProgress environment call before with binding (Call.token call) before
  ... | just original = bindRequestProgress environment call (Store.BindingRow.settings original) before
  ... | nothing = unboundProgress environment call before (Read.answer (Call.token call) before)

  startProgress : Environment → ∀ call before → Σ Store.World (λ after → Σ Result
    (λ reply → X.Completed (start call) before after reply))
  startProgress environment call before with afterOriginalProgress environment call before
  ... | after , reply , X.completed events execution changes = after , reply , X.completed
    ((readOriginal call , before) ∷ events) (E.replied _ _ before execution)
    (X.changed before _ before before (refl , refl) changes)

  progress : Environment → ∀ requested before → Σ Store.World (λ after → Σ Result
    (λ reply → X.Completed (script requested) before after reply))
  progress environment requested before with decode requested
  ... | inj₁ fault = doneProgress _ before
  ... | inj₂ call = startProgress environment call before

  operation : Environment → Recovery.RecoverableFor Store.World Request Result Goal
  operation environment = record
    { Effect = Effect; Reply = Reply; script = script; Atomic = Atomic
    ; converges = converges; progress = progress environment }

  bindingPresentStopsGrowth : ∀ call first final original →
    Project.Registered.binding (Call.token call) first ≡ just original → BindingsGrew call first final → final ≡ first
  bindingPresentStopsGrowth call first .first original known sameBindings = refl
  bindingPresentStopsGrowth call first _ original known (firstBinding settings observedTime current absent earlier)
    with bindingPresentStopsGrowth call first current original known earlier
  ... | refl with trans (sym absent) known
  ... | ()

  planPresentStopsGrowth : ∀ call first final raw →
    Project.Registered.plan (Call.token call) first ≡ just raw → PlansGrew call first final → final ≡ first
  planPresentStopsGrowth call first .first raw known samePlans = refl
  planPresentStopsGrowth call first _ raw known (firstPlan model value current computed decoded absent earlier)
    with planPresentStopsGrowth call first current raw known earlier
  ... | refl with trans (sym absent) known
  ... | ()

  restore : Store.World → Bindings → List Store.PlanRow → Store.World
  restore current originalBindings originalPlans = record current
    { operations = record (tables current) { bindings = originalBindings; plans = originalPlans } }

  restoreProtected : ∀ current → restore (protected current) (bindings current) (Store.OperationTables.plans (tables current)) ≡ current
  restoreProtected current = refl

  existingFrameUnchanged : ∀ call before after original raw →
    binding (Call.token call) before ≡ just original → plan (Call.token call) before ≡ just raw →
    Frame call before after → after ≡ before
  existingFrameUnchanged call before after original raw knownBinding knownPlan frame = trans
    (sym (restoreProtected after))
    (trans (cong (λ state → restore state (bindings after) (Store.OperationTables.plans (tables after))) (Frame.business frame))
    (trans (cong (λ rows → restore (protected before) rows (Store.OperationTables.plans (tables after))) bindingsUnchanged)
    (trans (cong (restore (protected before) (bindings before)) plansUnchanged) (restoreProtected before))))
    where
    bindingsUnchanged = bindingPresentStopsGrowth call (bindings before) (bindings after) original knownBinding (Frame.bindingExtension frame)
    plansUnchanged = planPresentStopsGrowth call (Store.OperationTables.plans (tables before)) (Store.OperationTables.plans (tables after))
      raw knownPlan (Frame.planExtension frame)

  completedExistingUnchanged : ∀ call before after result original raw →
    binding (Call.token call) before ≡ just original → plan (Call.token call) before ≡ just raw →
    X.Completed (start call) before after result → after ≡ before
  completedExistingUnchanged call before after result original raw knownBinding knownPlan completion =
    existingFrameUnchanged call before after original raw knownBinding knownPlan (completedStartFrame call before after result completion)

  transportReady : ∀ call before after context →
    binding (Call.token call) after ≡ binding (Call.token call) before →
    plan (Call.token call) after ≡ plan (Call.token call) before →
    Store.lookupCancellation after (Call.token call) ≡ Store.lookupCancellation before (Call.token call) →
    ReadyMeaning call before context → ReadyMeaning call after context
  transportReady call before after context sameBinding samePlan sameCancellation earlier = record
    { actualCall = ReadyMeaning.actualCall earlier
    ; boundRequest = trans sameBinding (ReadyMeaning.boundRequest earlier)
    ; originalArguments = ReadyMeaning.originalArguments earlier
    ; savedPlan = trans samePlan (ReadyMeaning.savedPlan earlier)
    ; decodedPlan = ReadyMeaning.decodedPlan earlier; planOperationMatches = ReadyMeaning.planOperationMatches earlier
    ; executable = ReadyMeaning.executable earlier
    ; uncancelled = trans sameCancellation (ReadyMeaning.uncancelled earlier)
    ; addresses = ReadyMeaning.addresses earlier; separateResult = ReadyMeaning.separateResult earlier }

  contextSame : ∀ first second → Context.call first ≡ Context.call second →
    Context.original first ≡ Context.original second → Context.model first ≡ Context.model second →
    Context.raw first ≡ Context.raw second → first ≡ second
  contextSame (preparedWrite call original model raw) (preparedWrite .call .original .model .raw) refl refl refl refl = refl

  readyContextUnique : ∀ call current first second → ReadyMeaning call current first → ReadyMeaning call current second → first ≡ second
  readyContextUnique call current first second earlier later = contextSame first second
    (trans (ReadyMeaning.actualCall earlier) (sym (ReadyMeaning.actualCall later)))
    (Maybes.just-injective (trans (sym (ReadyMeaning.boundRequest earlier)) (ReadyMeaning.boundRequest later)))
    (Sum.inj₂-injective (trans (sym (ReadyMeaning.decodedPlan earlier))
      (trans (cong P.decode sameRaw) (ReadyMeaning.decodedPlan later)))) sameRaw
    where sameRaw = Maybes.just-injective (trans (sym (ReadyMeaning.savedPlan earlier)) (ReadyMeaning.savedPlan later))

  decodedScript : ∀ requested call → decode requested ≡ inj₂ call → script requested ≡ start call
  decodedScript requested call decoded rewrite decoded = refl

  completedReady : ∀ requested before after context → X.Completed (script requested) before after (ready context) →
    Σ Call (λ call → decode requested ≡ inj₂ call × ReadyMeaning call after context)
  completedReady requested before after context completion with decode requested in decoded
  ... | inj₁ _ with completion
  ... | X.completed [] () _
  completedReady requested before after context completion | inj₂ call
    with completedMeaning call before after (ready context) completion
  ... | originalPlan .context facts = call , refl , facts

  completedDecodedExistingUnchanged : ∀ requested call before after result original raw → decode requested ≡ inj₂ call →
    binding (Call.token call) before ≡ just original → plan (Call.token call) before ≡ just raw →
    X.Completed (script requested) before after result → after ≡ before
  completedDecodedExistingUnchanged requested call before after result original raw decoded knownBinding knownPlan completion =
    completedExistingUnchanged call before after result original raw knownBinding knownPlan
      (subst (λ program → X.Completed program before after result) (decodedScript requested call decoded) completion)

  readyRetrySameContext : ∀ requested call before after first second → decode requested ≡ inj₂ call →
    ReadyMeaning call before first → X.Completed (script requested) before after (ready second) → after ≡ before × second ≡ first
  readyRetrySameContext requested call before after first second decoded earlier completion
    with completedMeaning call before after (ready second)
      (subst (λ program → X.Completed program before after (ready second)) (decodedScript requested call decoded) completion)
  ... | originalPlan .second later = sameWorld , sym (readyContextUnique call before first second earlier
    (subst (λ state → ReadyMeaning call state second) sameWorld later))
    where sameWorld = completedDecodedExistingUnchanged requested call before after (ready second)
            (Context.original first) (Context.raw first) decoded (ReadyMeaning.boundRequest earlier) (ReadyMeaning.savedPlan earlier) completion


  -- Reservation presence is read from the actual successful bind receipt.
  -- No global foreign-key invariant on arbitrary modeled Worlds is assumed.
  Reserved : Call → Store.World → Set
  Reserved call current = Σ Store.ReservationRow (λ row → Controls.reservation (Call.token call) current ≡ just row)

  boundReserved : ∀ call settings observedTime before original →
    bound original ≡ proj₂ (bind call settings observedTime before) → Reserved call before
  boundReserved call settings observedTime before original accepted
    with Controls.reservation (Call.token call) before in present
  ... | nothing with accepted
  ... | ()
  boundReserved call settings observedTime before original accepted | just row = row , refl

  changesKeepReservation : ∀ token before events after → X.Changes before events after →
    Controls.reservation token after ≡ Controls.reservation token before
  changesKeepReservation token before [] .before (X.unchanged _) = refl
  changesKeepReservation token before ((effect , reply) ∷ events) after
    (X.changed .before .effect .reply middle physical later) = trans
      (changesKeepReservation token middle events after later)
      (cong (Controls.reservation token) (Frame.business (atomicFrame before effect reply middle physical)))

  bindRequestReadyReserved : ∀ call settings before after context →
    X.Completed (bindRequest call settings) before after (ready context) → Reserved call after
  bindRequestReadyReserved call settings before after context
    (X.completed events (E.replied _ _ (observedTime , bound original) execution)
      changes@(X.changed _ _ _ middle (accepted , physical) later))
    with boundReserved call settings observedTime before original accepted
  ... | row , present = row , trans (changesKeepReservation (Call.token call) before events after changes) present
  bindRequestReadyReserved call settings before after context
    (X.completed events (E.replied _ _ (observedTime , changed original) ()) changes)
  bindRequestReadyReserved call settings before after context
    (X.completed events (E.replied _ _ (observedTime , unknown) (E.replied _ _ _ ())) changes)
  bindRequestReadyReserved call settings before after context
    (X.completed events (E.replied _ _ (observedTime , cancelled receipt) (E.replied _ _ _ ())) changes)

  afterSettingsReadyReserved : ∀ call observed before after context →
    X.Completed (afterSettings call observed) before after (ready context) → Reserved call after
  afterSettingsReadyReserved call (unavailable fault) before after context (X.completed [] () changes)
  afterSettingsReadyReserved call (configured settings) before after context completion
    with Public.freshLearningAdmission (Call.request call)
  ... | inj₁ fault with completion
  ... | X.completed [] () changes
  afterSettingsReadyReserved call (configured settings) before after context completion | inj₂ tt =
    bindRequestReadyReserved call settings before after context completion

  unboundReadyReserved : ∀ call observed outcome before after context →
    X.Completed (unbound call observed outcome) before after (ready context) → Reserved call after
  unboundReadyReserved call observed Read.reserved before after context
    (X.completed _ (E.replied _ _ settings execution) (X.changed _ _ _ middle physical later)) =
    afterSettingsReadyReserved call settings middle after context (X.completed _ execution later)
  unboundReadyReserved call observed Read.unknownToken before after context (X.completed [] () changes)
  unboundReadyReserved call observed (Read.awaitingPlan _) before after context (X.completed [] () changes)
  unboundReadyReserved call observed (Read.awaitingCompletion _) before after context (X.completed [] () changes)
  unboundReadyReserved call observed (Read.pending _ _ _) before after context (X.completed [] () changes)
  unboundReadyReserved call observed (Read.completed _ _) before after context (X.completed [] () changes)
  unboundReadyReserved call observed (Read.cancelled _ _ _) before after context (X.completed [] () changes)
  unboundReadyReserved call observed (Read.needsRecovery _) before after context (X.completed [] () changes)
  unboundReadyReserved call observed (Read.inconsistent _ _) before after context (X.completed [] () changes)

  afterOriginalReadyReserved : ∀ call observed before after context →
    X.Completed (afterOriginal call observed) before after (ready context) → Reserved call after
  afterOriginalReadyReserved call observed before after context completion with binding (Call.token call) observed
  ... | just original = bindRequestReadyReserved call (Store.BindingRow.settings original) before after context completion
  ... | nothing = unboundReadyReserved call observed (Read.answer (Call.token call) observed) before after context completion

  startReadyReserved : ∀ call before after context → X.Completed (start call) before after (ready context) → Reserved call after
  startReadyReserved call before after context
    (X.completed _ (E.replied _ _ .before execution) (X.changed _ _ _ .before (refl , refl) later)) =
    afterOriginalReadyReserved call before before after context (X.completed _ execution later)

  completedReadyReservation : ∀ requested call before after context → decode requested ≡ inj₂ call →
    X.Completed (script requested) before after (ready context) → Reserved call after
  completedReadyReservation requested call before after context decoded completion rewrite decoded =
    startReadyReserved call before after context completion


  existingPlanKnown : ∀ call current scope → ReadyMeaning call current scope →
    existingPlan (Context.original scope) (Context.raw scope) ≡
      planned (Context.original scope) (Context.model scope) (Context.raw scope)
  existingPlanKnown call current scope known rewrite ReadyMeaning.decodedPlan known |
    ReadyMeaning.planOperationMatches known | ReadyMeaning.executable known = refl

  prepareKnown : ∀ call current scope encoding → ReadyMeaning call current scope →
    prepare call (Store.BindingRow.settings (Context.original scope)) encoding current ≡
      (current , planned (Context.original scope) (Context.model scope) (Context.raw scope))
  prepareKnown call current scope encoding known rewrite ReadyMeaning.boundRequest known |
    matchesOriginalSettings call (proj₁ (ReadyMeaning.originalArguments known)) (Context.original scope)
      (proj₂ (ReadyMeaning.originalArguments known)) |
    ReadyMeaning.uncancelled known | ReadyMeaning.savedPlan known | existingPlanKnown call current scope known = refl

  bindKnown : ∀ call current scope observedTime → Reserved call current → ReadyMeaning call current scope →
    bind call (Store.BindingRow.settings (Context.original scope)) observedTime current ≡
      (current , bound (Context.original scope))
  bindKnown call current scope observedTime (row , present) known rewrite present |
    ReadyMeaning.uncancelled known | ReadyMeaning.boundRequest known |
    matchesOriginalSettings call (proj₁ (ReadyMeaning.originalArguments known)) (Context.original scope)
      (proj₂ (ReadyMeaning.originalArguments known)) = refl


  PendingReadback : ℕ → Store.World → Set
  PendingReadback token current = Σ Store.BindingRow (λ original → Σ P.Step (λ next →
    Σ (List Store.SavedReplyRow) (λ saved → Read.answer token current ≡ Read.pending original next saved)))

  admittedAfterReadback : ∀ operation token current original found matched observed scope →
    Read.answer token current ≡ observed →
    Read.afterReadback operation token current original found matched observed ≡ Read.admitted scope →
    PendingReadback token current
  admittedAfterReadback operation token current original found matched (Read.pending binding next saved) scope known accepted =
    binding , next , saved , known
  admittedAfterReadback operation token current original found matched (Read.completed _ _) scope known ()
  admittedAfterReadback operation token current original found matched (Read.cancelled _ _ _) scope known ()
  admittedAfterReadback operation token current original found matched (Read.inconsistent _ _) scope known ()
  admittedAfterReadback operation token current original found matched (Read.needsRecovery _) scope known ()
  admittedAfterReadback operation token current original found matched (Read.awaitingPlan _) scope known ()
  admittedAfterReadback operation token current original found matched (Read.awaitingCompletion _) scope known ()
  admittedAfterReadback operation token current original found matched Read.unknownToken scope known ()
  admittedAfterReadback operation token current original found matched Read.reserved scope known ()

  admittedAfterMatch : ∀ operation token current original found matched same scope →
    Read.afterMatch operation token current original found matched same ≡ Read.admitted scope →
    PendingReadback token current
  admittedAfterMatch operation token current original found false same scope ()
  admittedAfterMatch operation token current original found true same scope accepted =
    admittedAfterReadback operation token current original found same (Read.answer token current) scope refl accepted

  admittedAfterLookup : ∀ operation token current observed found scope →
    Read.afterBindingLookup operation token current observed found ≡ Read.admitted scope → PendingReadback token current
  admittedAfterLookup operation token current nothing found scope ()
  admittedAfterLookup operation token current (just original) found scope accepted =
    admittedAfterMatch operation token current original found
      (P.textEqual (Store.BindingRow.operation original) operation) refl scope accepted

  admittedHasPending : ∀ operation token current scope → Read.admission operation token current ≡ Read.admitted scope →
    PendingReadback token current
  admittedHasPending operation token current scope = admittedAfterLookup operation token current
    (binding token current) refl scope


  committedWorld : ∀ {before proposed after : Store.World} → DB.Atomic before proposed DB.committed after → after ≡ proposed
  committedWorld DB.committedAll = refl

  bindKnownObservation : ∀ call current scope observedTime reply after →
    Reserved call current → ReadyMeaning call current scope →
    Atomic current (bindOriginal call (Store.BindingRow.settings (Context.original scope))) (observedTime , reply) after →
    after ≡ current × reply ≡ bound (Context.original scope)
  bindKnownObservation call current scope observedTime reply after reserved known (observed , physical) =
    trans (committedWorld committed) (cong proj₁ expected) , sameReply
    where
    expected = bindKnown call current scope observedTime reserved known
    sameReply = trans observed (cong proj₂ expected)
    committed = subst (λ tag → DB.Atomic current
      (proj₁ (bind call (Store.BindingRow.settings (Context.original scope)) observedTime current)) tag after)
      (cong bindingReceipt sameReply) physical

  prepareKnownObservation : ∀ call current scope encoding reply validated after → ReadyMeaning call current scope →
    Atomic current (publishPlan call (Store.BindingRow.settings (Context.original scope))) (encoding , reply , validated) after →
    after ≡ current × reply ≡ planned (Context.original scope) (Context.model scope) (Context.raw scope)
  prepareKnownObservation call current scope encoding reply validated after known (observed , physical) =
    trans (committedWorld committed) (cong proj₁ expected) , sameReply
    where
    expected = prepareKnown call current scope encoding known
    sameReply = trans observed (cong proj₂ expected)
    committed = subst (λ tag → DB.Atomic current
      (proj₁ (prepare call (Store.BindingRow.settings (Context.original scope)) encoding current)) tag after)
      (cong planReceipt sameReply) physical

  createPlanKnownCompletion : ∀ call current scope after result → ReadyMeaning call current scope →
    X.Completed (createPlan call (Store.BindingRow.settings (Context.original scope))) current after result →
    after ≡ current × result ≡ ready (preparedWrite call (Context.original scope) (Context.model scope) (Context.raw scope))
  createPlanKnownCompletion call current scope after result known
    (X.completed _ (E.replied _ _ (encoding , reply , validated) execution) (X.changed _ _ _ middle physical later))
    with prepareKnownObservation call current scope encoding reply validated middle known physical
  ... | refl , refl with execution | later
  ... | E.returned _ | X.unchanged _ = refl , refl


  contextForPending : ∀ call current scope → Reserved call current → ReadyMeaning call current scope →
    PendingReadback (Call.token call) current →
    Σ (Read.ExecutionContext (Call.name call) (Call.token call) current) (λ actual →
      Read.admission (Call.name call) (Call.token call) current ≡ Read.admitted actual)
  contextForPending call current scope (reserved , reservedAt) known (returnedBinding , next , saved , observed) =
    Read.admissionFromPending (Call.name call) (Call.token call) current context next saved exactPending
    where
    atPlan : Read.afterPlan (Context.original scope) (Context.model scope) (Read.savedRows (Call.token call) current) ≡
      Read.pending returnedBinding next saved
    atPlan = trans (sym (Read.answerForKnownPlan (Call.token call) current (Context.original scope) (Context.raw scope)
      (Context.model scope) (ReadyMeaning.boundRequest known) (ReadyMeaning.uncancelled known)
      (ReadyMeaning.savedPlan known) (ReadyMeaning.decodedPlan known))) observed
    exactBinding = Read.planPendingBinding (Context.original scope) (Context.model scope)
      (Read.savedRows (Call.token call) current) returnedBinding next saved atPlan
    exactPending : Read.answer (Call.token call) current ≡ Read.pending (Context.original scope) next saved
    exactPending = trans observed (cong (λ row → Read.pending row next saved) exactBinding)
    context : Read.ExecutionContext (Call.name call) (Call.token call) current
    context = record
      { reservationRow = reserved; originalReservation = reservedAt
      ; bindingRow = Context.original scope; originalBinding = ReadyMeaning.boundRequest known
      ; requestedOperation = trans (cong (λ name → P.textEqual name (Call.name call)) (readyOperation call current scope known))
          (sameOperation (Call.name call))
      ; rawPlan = Context.raw scope; originalPlan = ReadyMeaning.savedPlan known
      ; plan = Context.model scope; decoded = ReadyMeaning.decodedPlan known
      ; matchingOperation = ReadyMeaning.planOperationMatches known; executable = ReadyMeaning.executable known
      ; addresses = ReadyMeaning.addresses known; separateResult = ReadyMeaning.separateResult known
      ; journal = Read.afterPlanJournal (Call.token call) current (Context.original scope) (Context.model scope)
          returnedBinding next saved (ReadyMeaning.addresses known) atPlan }


  operationTextEqual : ∀ first second → P.textEqual first second ≡ true → first ≡ second
  operationTextEqual first second known with first ≟Text second
  ... | yes same = same
  ... | no different with known
  ... | ()

  readyNonempty : ∀ call current scope → ReadyMeaning call current scope → P.Saved.steps (Context.model scope) ≢ []
  readyNonempty call current scope known = P.publicWriterStepsNonempty library (Call.tool call) (Context.model scope)
    (Call.writer call) (trans (sym (operationTextEqual _ _ (ReadyMeaning.planOperationMatches known)))
      (readyOperation call current scope known)) (ReadyMeaning.executable known)

  PendingValue : Read.Result → Set
  PendingValue observed = Σ Store.BindingRow (λ original → Σ P.Step (λ next →
    Σ (List Store.SavedReplyRow) (λ saved → observed ≡ Read.pending original next saved)))

  afterPrefixPendingValue : ∀ original model receipts remaining result → P.Saved.steps model ≢ [] →
    Resumable (Read.afterPrefix original model receipts remaining result) →
    PendingValue (Read.afterPrefix original model receipts remaining result)
  afterPrefixPendingValue original model receipts [] (just result) nonempty ()
  afterPrefixPendingValue original model receipts (_ ∷ _) (just result) nonempty ()
  afterPrefixPendingValue original model receipts (next ∷ rest) nothing nonempty possible = original , next , receipts , refl
  afterPrefixPendingValue original model receipts [] nothing nonempty possible with P.Saved.steps model in steps
  ... | [] = ⊥-elim (nonempty refl)
  ... | _ ∷ _ = ⊥-elim possible

  afterPlanPendingValue : ∀ original model rows → P.Saved.steps model ≢ [] → Resumable (Read.afterPlan original model rows) →
    PendingValue (Read.afterPlan original model rows)
  afterPlanPendingValue original model rows nonempty possible
    with P.textEqual (Store.BindingRow.operation original) (P.Saved.operation model)
  ... | false = ⊥-elim possible
  ... | true with P.valid library model
  ... | false = ⊥-elim possible
  ... | true with Read.prefix (P.Saved.steps model) rows
  ... | receipts , remaining with Data.List.length (Data.List.filterᵇ Read.notFinal rows) ≟ Data.List.length receipts
  ... | no _ = ⊥-elim possible
  ... | yes _ = afterPrefixPendingValue original model receipts remaining (Read.find Step.resultKey rows) nonempty possible

  preparedResumablePending : ∀ call current scope → ReadyMeaning call current scope → Resumable (Read.answer (Call.token call) current) →
    PendingReadback (Call.token call) current
  preparedResumablePending call current scope known possible = fromPlan
    (afterPlanPendingValue (Context.original scope) (Context.model scope) (Read.savedRows (Call.token call) current)
      (readyNonempty call current scope known) (subst Resumable planObserved possible))
    where
    planObserved = Read.answerForKnownPlan (Call.token call) current (Context.original scope) (Context.raw scope)
      (Context.model scope) (ReadyMeaning.boundRequest known) (ReadyMeaning.uncancelled known)
      (ReadyMeaning.savedPlan known) (ReadyMeaning.decodedPlan known)
    fromPlan : PendingValue (Read.afterPlan (Context.original scope) (Context.model scope) (Read.savedRows (Call.token call) current)) →
      PendingReadback (Call.token call) current
    fromPlan (original , next , saved , actual) = original , next , saved , trans planObserved actual

  preparedEmptyPending : ∀ call current scope → ReadyMeaning call current scope → Read.savedRows (Call.token call) current ≡ [] →
    PendingReadback (Call.token call) current
  preparedEmptyPending call current scope known emptyRows with P.Saved.steps (Context.model scope) in steps
  ... | [] = ⊥-elim (readyNonempty call current scope known steps)
  ... | next ∷ rest = Context.original scope , next , [] , trans planObserved pendingPlan
    where
    planObserved = Read.answerForKnownPlan (Call.token call) current (Context.original scope) (Context.raw scope)
      (Context.model scope) (ReadyMeaning.boundRequest known) (ReadyMeaning.uncancelled known)
      (ReadyMeaning.savedPlan known) (ReadyMeaning.decodedPlan known)
    pendingPlan : Read.afterPlan (Context.original scope) (Context.model scope) (Read.savedRows (Call.token call) current) ≡
      Read.pending (Context.original scope) next []
    pendingPlan rewrite emptyRows | ReadyMeaning.planOperationMatches known |
      P.currentPlanRemainsReadable library (Context.model scope) (ReadyMeaning.executable known) | steps = refl

  prefixKeepsRows : ∀ call before after token → Frame call before after → Read.savedRows token after ≡ Read.savedRows token before
  prefixKeepsRows call before after token frame = cong (Read.savedRows token) (Frame.business frame)
