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
import Data.List.Properties as Lists
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.String using (toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (does; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; subst; sym)
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
sourceName evidenceRemoval = toList "remove_evidence"

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
