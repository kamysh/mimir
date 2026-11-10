{-# OPTIONS --safe #-}
-- One atomic sweep removes its complete admitted set and dependent rows.
-- Selection, affected-survivor equations and the original answer belong to
-- that same publication; an uncommitted read cannot fix a later retry's set.
module Mimir.SweepRecovery where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Float.Base using (Float; _≤ᵇ_)
open import Data.Integer using (ℤ; +_)
open import Data.List using (List; []; _∷_; map; concatMap; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤?_)
open import Relation.Nullary using (does)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String using (toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; sym; trans)
open import Mimir.Text using (Text)
import Data.List.Relation.Binary.Permutation.Propositional as Perm
import Mimir.ApplicationStore as Store
import Mimir.BeliefDeletionRecovery as Deletion
import Mimir.GraphDeletion as Delete
import Mimir.GraphNumerics as Numeric
import Mimir.GraphRecords as Records
import Mimir.InferenceStorageBinding as Inference
import Mimir.PosteriorComputation as P
import Mimir.PublicEncoding as Encoding
import Mimir.RetrievalRanking as Ranking
import Mimir.StorageSemantics as Storage
import Mimir.StructuredValue as Wire
import Mimir.Validation as Validation
import Mimir.StandardLibrary as Library
import Mimir.ConfigurationSchema as Configuration
import Mimir.PublicRequest as Public
import Mimir.PublicInput as Input
import Mimir.RecordDecoding as Decode
import Mimir.JsonObjects as Objects
import Mimir.RegisteredStoreAdmission as Admission
import Mimir.RecoverableStoreStep as Step
import Mimir.Recovery as Recovery
import Mimir.DatabaseTransaction as DB
import Mimir.OperationControls as Controls
import Mimir.InferenceProtocol as Service
import Mimir.McpErrors as Errors
open import Mimir.RecordDecoding using (_>>=_)

-- The stored request supplies scope/threshold; grace comes only from the
-- original user-configured policy. It is never a per-call agent override.
record Request : Set where
  constructor request
  field project : Maybe Text; threshold : Float; grace : ℤ

selected : Request → ℤ → Store.World → Maybe (List ℕ)
selected requested observed before with Storage.defeats (Request.project requested) before
... | nothing = nothing
... | just edges = just (Ranking.sort (λ first second → does (first ≤? second))
  (Numeric.expiredTargets observed (Request.grace requested) (Request.threshold requested)
  (Records.listBeliefs (Request.project requested) nothing (Store.beliefs before)) edges
  (map Numeric.Defeat.target edges)))

erased : List ℕ → Store.World → Store.World
erased identities before = Store.removeBeliefVectors identities (Store.removeNodes identities true before)

affected : List ℕ → Store.World → List ℕ
affected identities before = Ranking.unique (concatMap (λ identity → Delete.children identity before) identities)

module Business (format : Encoding.Formatting) (databaseSum : List Float → Float) (calculator : P.Calculator) where
  module D = Deletion.Business databaseSum calculator
  module N = Inference.NumericalOutcome databaseSum
  module Encode = Encoding.Encode format
  open D using (Diagnostic; requestFault; preparation; rejectedReport; repeated)
  Outcome = D.Outcome

  answer : List ℕ → Wire.Value
  answer identities = Encoding.object
    (("deleted" , Wire.unsigned (length identities)) ∷ ("selected" , Wire.array (map Encode.uuid identities)) ∷ [])

  invalidThreshold missingClock : Validation.Fault
  invalidThreshold = Validation.fault (Validation.key "prob_threshold" ∷ []) Validation.invalidNumber
    "Supply a finite probability between zero and one. No target or vector was deleted."
  missingClock = Validation.fault [] Validation.missingEvidence
    "A defeated target has no valid recorded first-defeat date or legacy-expired marker. Read its retirement metadata and open the user dialog; do not invent a date or delete it."

  module Selected (publicationTime : ℤ) (identities : List ℕ) (preparedContext : N.Context) where
    open N.Context preparedContext
    module A = P.Assess seed external edges targets
    module C = N.Cycle preparedContext edges

    DiagnosticGoal : Diagnostic → Set
    DiagnosticGoal (rejectedReport report) = A.check report ≡ A.rejected
    DiagnosticGoal (repeated final visited) = C.Repeated final visited
    DiagnosticGoal _ = ⊥

    Goal : Store.World → Outcome → Set
    Goal before (inj₁ diagnostic) = DiagnosticGoal diagnostic
    Goal before (inj₂ (after , reply)) = Σ (List (ℕ × Float)) (λ numericalReply →
      N.Completed publicationTime preparedContext before after numericalReply × reply ≡ answer identities)

    report : P.CalculationReport
    report = calculator seed external edges targets

    checked : ∀ before → Σ Outcome (Goal before)
    checked before with A.check report in assessed
    ... | A.rejected = inj₁ (rejectedReport report) , assessed
    ... | A.accepted counts valid shape complete =
      inj₂ (N.proposed publicationTime preparedContext before counts , answer identities) ,
      Numeric.project (N.writes preparedContext counts) ,
      (edges , Perm.↭-refl , counts , valid , shape , complete , refl , refl) , refl
    ... | A.repeated final visited seen incomplete runs = inj₁ (repeated final visited) , seen , incomplete , runs

    journalUnchanged : ∀ before after reply → Goal before (inj₂ (after , reply)) →
      Store.World.operations after ≡ Store.World.operations before
    journalUnchanged before after reply
      (numericalReply , (incoming , permutation , counts , valid , shape , complete , framed , answered) , selectedAnswer)
      rewrite framed with readOnly
    ... | true = refl
    ... | false = refl

  -- The entire initial eligible set is chosen before any deletion. Survivor
  -- recomputation uses the world with ALL of those identities already erased.
  Goal : Request → ℤ → ℤ → Store.World → Outcome → Set
  Goal requested observed publicationTime before outcome with Numeric.probability (Request.threshold requested)
  ... | false = outcome ≡ inj₁ (requestFault invalidThreshold)
  ... | true with selected requested observed before
  ... | nothing = outcome ≡ inj₁ (requestFault missingClock)
  ... | just [] with outcome
  ... | inj₁ _ = ⊥
  ... | inj₂ (after , reply) = after ≡ before × reply ≡ answer []
  Goal requested observed publicationTime before outcome | true | just identities@(_ ∷ _)
    with N.prepare (N.recompute (affected identities before)) (erased identities before)
  ... | inj₁ issue = outcome ≡ inj₁ (preparation issue)
  ... | inj₂ preparedContext = Selected.Goal publicationTime identities preparedContext (erased identities before) outcome

  checked : ∀ requested observed publicationTime before → Σ Outcome (Goal requested observed publicationTime before)
  checked requested observed publicationTime before with Numeric.probability (Request.threshold requested)
  ... | false = inj₁ (requestFault invalidThreshold) , refl
  ... | true with selected requested observed before
  ... | nothing = inj₁ (requestFault missingClock) , refl
  ... | just [] = inj₂ (before , answer []) , refl , refl
  ... | just identities@(_ ∷ _) with N.prepare (N.recompute (affected identities before)) (erased identities before)
  ... | inj₁ issue = inj₁ (preparation issue) , refl
  ... | inj₂ preparedContext = Selected.checked publicationTime identities preparedContext (erased identities before)

  keepsJournal : ∀ requested observed publicationTime before after reply →
    proj₁ (checked requested observed publicationTime before) ≡ inj₂ (after , reply) →
    Store.World.operations after ≡ Store.World.operations before
  keepsJournal requested observed publicationTime before after reply accepted
    with Numeric.probability (Request.threshold requested)
  ... | false with accepted
  ... | ()
  keepsJournal requested observed publicationTime before after reply accepted | true
    with selected requested observed before
  ... | nothing with accepted
  ... | ()
  keepsJournal requested observed publicationTime before after reply accepted | true | just [] with accepted
  ... | refl = refl
  keepsJournal requested observed publicationTime before after reply accepted | true | just identities@(_ ∷ _)
    with N.prepare (N.recompute (affected identities before)) (erased identities before)
  ... | inj₁ issue with accepted
  ... | ()
  keepsJournal requested observed publicationTime before after reply accepted | true | just identities@(_ ∷ _) | inj₂ preparedContext =
    Selected.journalUnchanged publicationTime identities preparedContext (erased identities before) after reply
      (subst (Selected.Goal publicationTime identities preparedContext (erased identities before)) accepted
        (proj₂ (Selected.checked publicationTime identities preparedContext (erased identities before))))

  -- Successful raw-service replies owe the same complete business condition
  -- as the registered publication. No per-target receipt or partial count can
  -- construct one. The visible service result is only length identities.
  data ServiceReceipt (requested : Request) :
    Service.Reply (Service.sweepPublication (Request.project requested)
      (Request.threshold requested) (Request.grace requested)) → Set where
    published : ∀ selectedAt publishedAt before after identities →
      selected requested selectedAt before ≡ just identities →
      Goal requested selectedAt publishedAt before (inj₂ (after , answer identities)) →
      DB.Atomic before after DB.committed after → ServiceReceipt requested (inj₂ (inj₂ identities))
    refused : ∀ selectedAt publishedAt before diagnostic
      (correction : Errors.AgentCorrection.Certified Store.World before before) →
      Goal requested selectedAt publishedAt before (inj₁ diagnostic) →
      ServiceReceipt requested (inj₂ (inj₁ (Errors.AgentCorrection.Certified.report correction)))

-- These are observations of the actual host configuration and PostgreSQL
-- statements. They are effect replies, never extra caller fields. A failed
-- uncommitted attempt may observe repaired configuration on its next try.
record Metadata : Set where
  constructor physicalMetadata
  field policy : Maybe Wire.Value; selectedAt publishedAt : ℤ

module Registered (library : Library.Contract) (format : Encoding.Formatting)
  (databaseSum : List Float → Float) (calculator : P.Calculator)
  (observe : ℕ → Store.World → Metadata) where
  module B = Business format databaseSum calculator
  module D = Deletion.Business databaseSum calculator
  module DecodePublic = Public.Decode library
  module Retention = Configuration.Retirement library
  descriptor = Admission.descriptor (toList "sweep_expired_defeated") (toList "store.delete_belief")
    (toList "[\"store.delete_belief\",null]")
  key : ℕ → Text
  key _ = Admission.Descriptor.key descriptor
  distinct : ∀ token → key token ≡ Step.resultKey → ⊥
  distinct token ()

  record Bound : Set where
    constructor boundRequest
    field scope : Maybe Text; threshold : Float; settings : Wire.Value

  original : ℕ → Step.Registration → Validation.Fault ⊎ Bound
  original token registration = Admission.resolve descriptor token registration >>= λ resolved →
    let binding = proj₂ resolved in
    Decode.readRecord Objects.forbid Objects.rejectKnownRepeated
      (toList "prob_threshold" ∷ toList "project" ∷ [])
      (λ fields → Input.defaulted "prob_threshold" 0.3 DecodePublic.unitProbability fields >>= λ threshold →
        Input.optional "project" Wire.asString fields >>= λ scope →
        inj₂ (boundRequest scope threshold (Store.BindingRow.settings binding)))
      (Store.BindingRow.arguments binding)

  record Policy : Set where
    constructor policy
    field hours : Float; grace : ℤ

  table : Wire.Value → Validation.Fault ⊎ Policy
  table raw = Decode.readRecord Objects.forbid Objects.rejectKnownRepeated
    (toList "grace_hours" ∷ [])
    (λ fields → Input.required "grace_hours" DecodePublic.float fields >>= λ hours →
      Input.required "grace_hours" Retention.duration fields >>= λ grace → inj₂ (policy hours grace)) raw

  configured : Maybe Wire.Value → Validation.Fault ⊎ Policy
  configured nothing = inj₁ (Validation.fault [] Validation.missingField
    "This unfinished sweep needs the user's original retirement.grace_hours. Open the user dialog; no period is guessed and nothing is selected or deleted.")
  configured (just raw) = table raw

  storedPolicy : Wire.Value → Validation.Fault ⊎ Policy
  storedPolicy = Decode.readRecord Objects.forbid Objects.rejectKnownRepeated
    (toList "retirement" ∷ []) (Input.required "retirement" table)

  changedPolicy : Validation.Fault
  changedPolicy = Validation.fault (Validation.key "retirement" ∷ Validation.key "grace_hours" ∷ [])
    Validation.staleRevision
    "The current user-owned retention policy differs from this unfinished sweep's original policy. Open the user dialog to restore it or explicitly cancel unfinished work. Do not choose a period, rewrite its binding, override it per call or cancel automatically. Nothing was selected or deleted."

  samePolicy : Policy → Policy → Bool
  samePolicy first second = (Policy.hours first ≤ᵇ Policy.hours second) ∧ (Policy.hours second ≤ᵇ Policy.hours first)

  requested : Bound → Policy → Request
  requested binding chosen = request (Bound.scope binding) (Bound.threshold binding) (Policy.grace chosen)

  -- This is the business meaning, before saved-answer publication. Diagnostics
  -- retain the complete initial World; success removes the whole selected set
  -- and satisfies every affected survivor's posterior equation.
  DecisionGoal : Bound → Metadata → Store.World → B.Outcome → Set
  DecisionGoal binding metadata before outcome with storedPolicy (Bound.settings binding)
  ... | inj₁ fault = outcome ≡ inj₁ (D.requestFault fault)
  ... | inj₂ chosen with configured (Metadata.policy metadata)
  ... | inj₁ fault = outcome ≡ inj₁ (D.requestFault fault)
  ... | inj₂ current with samePolicy chosen current
  ... | false = outcome ≡ inj₁ (D.requestFault changedPolicy)
  ... | true = B.Goal (requested binding chosen) (Metadata.selectedAt metadata) (Metadata.publishedAt metadata) before outcome

  checkedDecision : ∀ binding metadata before → Σ B.Outcome (DecisionGoal binding metadata before)
  checkedDecision binding metadata before with storedPolicy (Bound.settings binding)
  ... | inj₁ fault = inj₁ (D.requestFault fault) , refl
  ... | inj₂ chosen with configured (Metadata.policy metadata)
  ... | inj₁ fault = inj₁ (D.requestFault fault) , refl
  ... | inj₂ current with samePolicy chosen current
  ... | false = inj₁ (D.requestFault changedPolicy) , refl
  ... | true = B.checked (requested binding chosen) (Metadata.selectedAt metadata) (Metadata.publishedAt metadata) before

  missingPolicyPauses : ∀ binding metadata before chosen →
    storedPolicy (Bound.settings binding) ≡ inj₂ chosen → Metadata.policy metadata ≡ nothing →
    proj₁ (checkedDecision binding metadata before) ≡ inj₁ (D.requestFault
      (Validation.fault [] Validation.missingField
        "This unfinished sweep needs the user's original retirement.grace_hours. Open the user dialog; no period is guessed and nothing is selected or deleted."))
  missingPolicyPauses binding metadata before chosen stored missing rewrite stored | missing = refl

  changedPolicyPauses : ∀ binding metadata before chosen current →
    storedPolicy (Bound.settings binding) ≡ inj₂ chosen → configured (Metadata.policy metadata) ≡ inj₂ current →
    samePolicy chosen current ≡ false →
    proj₁ (checkedDecision binding metadata before) ≡ inj₁ (D.requestFault changedPolicy)
  changedPolicyPauses binding metadata before chosen current stored configuredCurrent changed
    rewrite stored | configuredCurrent | changed = refl

  decisionKeepsJournal : ∀ binding metadata before after reply →
    proj₁ (checkedDecision binding metadata before) ≡ inj₂ (after , reply) →
    Store.World.operations after ≡ Store.World.operations before
  decisionKeepsJournal binding metadata before after reply accepted with storedPolicy (Bound.settings binding)
  ... | inj₁ fault with accepted
  ... | ()
  decisionKeepsJournal binding metadata before after reply accepted | inj₂ chosen with configured (Metadata.policy metadata)
  ... | inj₁ fault with accepted
  ... | ()
  decisionKeepsJournal binding metadata before after reply accepted | inj₂ chosen | inj₂ current with samePolicy chosen current
  ... | false with accepted
  ... | ()
  decisionKeepsJournal binding metadata before after reply accepted | inj₂ chosen | inj₂ current | true =
    B.keepsJournal (requested binding chosen) (Metadata.selectedAt metadata) (Metadata.publishedAt metadata) before after reply accepted

  Internal = ℕ × Metadata
  admit : Internal → Step.Registration → Maybe D.Diagnostic
  admit (token , _) registration with original token registration
  ... | inj₁ fault = just (D.requestFault fault)
  ... | inj₂ _ = nothing

  decide : Internal → Store.World → B.Outcome
  decide (token , metadata) before with original token (Step.registration before)
  ... | inj₁ fault = inj₁ (D.requestFault fault)
  ... | inj₂ binding = proj₁ (checkedDecision binding metadata before)

  decidesBound : ∀ token metadata before binding → original token (Step.registration before) ≡ inj₂ binding →
    decide (token , metadata) before ≡ proj₁ (checkedDecision binding metadata before)
  decidesBound token metadata before binding accepted rewrite accepted = refl

  keepsJournal : ∀ input before after reply → decide input before ≡ inj₂ (after , reply) →
    Store.World.operations after ≡ Store.World.operations before
  keepsJournal (token , metadata) before after reply accepted with original token (Step.registration before)
  ... | inj₁ fault with accepted
  ... | ()
  keepsJournal (token , metadata) before after reply accepted | inj₂ binding =
    decisionKeepsJournal binding metadata before after reply accepted

  module Saved = Step.Admitted Internal D.Diagnostic proj₁ (λ input → key (proj₁ input))
    (λ input → distinct (proj₁ input)) decide keepsJournal admit
  module K = Saved.Kernel

  allowed : ∀ token metadata before binding → original token (Step.registration before) ≡ inj₂ binding →
    Saved.execute (token , metadata) before ≡ K.execute (token , metadata) before
  allowed token metadata before binding accepted rewrite accepted = refl

  -- An attempt either commits its complete answer, or changes no state. In
  -- the latter case retry may use a different actual clock/config observation.
  Publication : ℕ → Metadata → Store.World → Set
  Publication token metadata before = Σ Store.World (λ changed → Σ Wire.Value (λ reply →
    admit (token , metadata) (Step.registration before) ≡ nothing ×
    Store.lookupCancellation before token ≡ nothing ×
    Store.lookupSaved before token (key token) ≡ nothing ×
    Store.lookupSaved before token Step.resultKey ≡ nothing ×
    decide (token , metadata) before ≡ inj₂ (changed , reply)))

  classification : ∀ token metadata before →
    proj₁ (Saved.execute (token , metadata) before) ≡ before ⊎ Publication token metadata before
  classification token metadata before with admit (token , metadata) (Step.registration before) in admitted
  ... | just _ = inj₁ refl
  ... | nothing with Store.lookupCancellation before token in active
  ... | just _ = inj₁ refl
  ... | nothing with Store.lookupSaved before token (key token) in step | Store.lookupSaved before token Step.resultKey in result
  ... | just _ | just _ = inj₁ refl
  ... | just _ | nothing = inj₁ refl
  ... | nothing | just _ = inj₁ refl
  ... | nothing | nothing with decide (token , metadata) before in accepted
  ... | inj₁ _ = inj₁ refl
  ... | inj₂ (changed , reply) = inj₂ (changed , reply , refl , refl , refl , refl , refl)

  fresh : ∀ token metadata before changed reply → admit (token , metadata) (Step.registration before) ≡ nothing →
    Store.lookupCancellation before token ≡ nothing → Store.lookupSaved before token (key token) ≡ nothing →
    Store.lookupSaved before token Step.resultKey ≡ nothing → decide (token , metadata) before ≡ inj₂ (changed , reply) →
    Saved.execute (token , metadata) before ≡ (K.publication (token , metadata) changed reply , Step.done reply)
  fresh token metadata before changed reply admitted active step result accepted rewrite admitted | active | step | result | accepted = refl

  allowedAdmission : ∀ token metadata before → admit (token , metadata) (Step.registration before) ≡ nothing →
    Saved.execute (token , metadata) before ≡ K.execute (token , metadata) before
  allowedAdmission token metadata before admitted rewrite admitted = refl

  family : ∀ token first second before → Σ Metadata (λ original →
    Saved.execute (token , second) (proj₁ (Saved.execute (token , first) before)) ≡ Saved.execute (token , original) before)
  family token first second before with classification token first before
  ... | inj₁ unchanged = second , cong (Saved.execute (token , second)) unchanged
  ... | inj₂ (changed , reply , admitted , active , step , result , accepted) = first , trans
    (cong (λ pair → Saved.execute (token , second) (proj₁ pair)) published)
    (trans replayed (sym published))
    where
    published = fresh token first before changed reply admitted active step result accepted
    middle = K.publication (token , first) changed reply
    admittedAfter = trans (cong (admit (token , second)) (K.publicationKeepsRegistration (token , first) before changed reply accepted)) admitted
    replayed = trans (allowedAdmission token second middle admittedAfter)
      (K.replay (token , second) middle reply reply
        (trans (K.publicationKeepsCancellation (token , first) before changed reply accepted) active)
        (K.publishedStepReadable (token , first) before changed reply accepted step)
        (K.publishedResultReadable (token , first) before changed reply accepted result))

  FreshGoal : ℕ → Bound → Metadata → Store.World → Store.World → Saved.Reply → Set
  FreshGoal token binding metadata before after reply =
    (Σ D.Diagnostic (λ diagnostic → after ≡ before × reply ≡ Step.needsInput diagnostic ×
      DecisionGoal binding metadata before (inj₁ diagnostic))) ⊎
    (Σ Store.World (λ changed → Σ Wire.Value (λ answer →
      DecisionGoal binding metadata before (inj₂ (changed , answer)) ×
      after ≡ K.publication (token , metadata) changed answer × reply ≡ Step.done answer)))

  freshMeaning : ∀ token metadata before binding → original token (Step.registration before) ≡ inj₂ binding →
    FreshGoal token binding metadata before (proj₁ (K.fresh (token , metadata) before)) (proj₂ (K.fresh (token , metadata) before))
  freshMeaning token metadata before binding bound rewrite decidesBound token metadata before binding bound
    with checkedDecision binding metadata before
  ... | inj₁ diagnostic , meaningful = inj₁ (diagnostic , refl , refl , meaningful)
  ... | inj₂ (changed , answer) , meaningful = inj₂ (changed , answer , meaningful , refl , refl)

  ObservedGoal : ℕ → Metadata → Store.World → Store.World → Saved.Reply → Set
  ObservedGoal token metadata before after reply with original token (Step.registration before)
  ... | inj₁ fault = after ≡ before × reply ≡ Step.needsInput (D.requestFault fault)
  ... | inj₂ binding with Store.lookupCancellation before token
  ... | just cancelled = after ≡ before × reply ≡ Step.cancelled cancelled
  ... | nothing with Store.lookupSaved before token (key token) | Store.lookupSaved before token Step.resultKey
  ... | just saved | just _ = after ≡ before × reply ≡ Step.done saved
  ... | just _ | nothing = after ≡ before × reply ≡ Step.needsRecovery
  ... | nothing | just _ = after ≡ before × reply ≡ Step.needsRecovery
  ... | nothing | nothing = FreshGoal token binding metadata before after reply

  meaning : ∀ token metadata before → ObservedGoal token metadata before
    (proj₁ (Saved.execute (token , metadata) before)) (proj₂ (Saved.execute (token , metadata) before))
  meaning token metadata before with original token (Step.registration before) in bound
  ... | inj₁ fault = refl , refl
  ... | inj₂ binding with Store.lookupCancellation before token
  ... | just _ = refl , refl
  ... | nothing with Store.lookupSaved before token (key token) | Store.lookupSaved before token Step.resultKey
  ... | just _ | just _ = refl , refl
  ... | just _ | nothing = refl , refl
  ... | nothing | just _ = refl , refl
  ... | nothing | nothing = freshMeaning token metadata before binding bound

  Effect = ℕ
  Reply : Effect → Set
  Reply _ = Metadata × Saved.Reply
  Atomic : Store.World → (token : Effect) → Reply token → Store.World → Set
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

  everyDatabaseReceiptCovered : ∀ token metadata before tag actual →
    DB.Atomic before (proj₁ (Saved.execute (token , metadata) before)) tag actual → X.Interrupted (script token) before actual
  everyDatabaseReceiptCovered token metadata before .DB.committed _ DB.committedAll =
    X.beforeReply [] token (λ reply → E.done (proj₂ reply)) before (metadata , proj₂ (Saved.execute (token , metadata) before)) _
      (E.stopped _) (X.unchanged before) (refl , Saved.expectedPhysical (token , metadata) before)
  everyDatabaseReceiptCovered token metadata before .DB.aborted _ DB.abortedNone =
    X.atPrefix [] (script token) before (E.stopped _) (X.unchanged before)
  everyDatabaseReceiptCovered token metadata before .DB.acknowledgementLost _ DB.unknownBefore =
    X.atPrefix [] (script token) before (E.stopped _) (X.unchanged before)
  everyDatabaseReceiptCovered token metadata before .DB.acknowledgementLost _ DB.unknownAfter =
    X.beforeReply [] token (λ reply → E.done (proj₂ reply)) before (metadata , proj₂ (Saved.execute (token , metadata) before)) _
      (E.stopped _) (X.unchanged before) (refl , Saved.expectedPhysical (token , metadata) before)

  Goal : ℕ → Store.World → Store.World → Saved.Reply → Set
  Goal token before after reply = Σ Metadata (λ metadata → ObservedGoal token metadata before after reply)
  fromObservation : ∀ token metadata before after reply → (after , reply) ≡ Saved.execute (token , metadata) before → Goal token before after reply
  fromObservation token metadata before after reply observed = metadata , subst
    (λ outcome → ObservedGoal token metadata before (proj₁ outcome) (proj₂ outcome)) (sym observed) (meaning token metadata before)

  converges : ∀ token before interrupted after reply → X.Interrupted (script token) before interrupted →
    X.Completed (script token) interrupted after reply → Goal token before after reply
  converges token before interrupted after reply interruption completion
    with interruptionState token before interrupted interruption | completedObservation token interrupted after reply completion
  ... | inj₁ same | metadata , observed = fromObservation token metadata before after reply
    (trans observed (cong (Saved.execute (token , metadata)) same))
  ... | inj₂ (first , same) | second , observed with family token first second before
  ... | original , preserved = fromObservation token original before after reply
    (trans observed (trans (cong (Saved.execute (token , second)) same) preserved))

  progress : ∀ token before → Σ Store.World (λ after → Σ Saved.Reply (λ reply → X.Completed (script token) before after reply))
  progress token before = proj₁ expected , proj₂ expected , X.completed
    ((token , metadata , proj₂ expected) ∷ [])
    (E.replied token (λ reply → E.done (proj₂ reply)) (metadata , proj₂ expected) (E.returned _))
    (X.changed before token _ _ (refl , Saved.expectedPhysical (token , metadata) before) (X.unchanged _))
    where
    metadata = observe token before
    expected = Saved.execute (token , metadata) before

  operation : Recovery.RecoverableFor Store.World ℕ Saved.Reply Goal
  operation = record { Effect = Effect; Reply = Reply; script = script; Atomic = Atomic; converges = converges; progress = progress }

  -- A saved publication takes priority over every new configuration/clock
  -- observation. The exact original answer and complete current World survive.
  completedReplayIgnoresCurrentPolicy : ∀ token metadata before binding saved final →
    original token (Step.registration before) ≡ inj₂ binding →
    Store.lookupCancellation before token ≡ nothing →
    Store.lookupSaved before token (key token) ≡ just saved →
    Store.lookupSaved before token Step.resultKey ≡ just final →
    Saved.execute (token , metadata) before ≡ (before , Step.done saved)
  completedReplayIgnoresCurrentPolicy token metadata before binding saved final bound active step result =
    trans (allowed token metadata before binding bound) (K.replay (token , metadata) before saved final active step result)

  cachedReplay : ∀ token before current raw →
    Store.lookupSaved before token Step.resultKey ≡ nothing →
    Store.lookupSaved current token Step.resultKey ≡ just raw →
    X.Interrupted (script token) before current → X.Completed (script token) current current (Step.done raw)
  cachedReplay token before current raw absent present cut with interruptionState token before current cut
  ... | inj₁ same = ⊥-elim (impossible same)
    where
    impossible : current ≡ before → ⊥
    impossible refl with trans (sym absent) present
    ... | ()
  ... | inj₂ (metadata , same) with classification token metadata before
  ... | inj₁ unchanged = ⊥-elim (impossible (trans same unchanged))
    where
    impossible : current ≡ before → ⊥
    impossible refl with trans (sym absent) present
    ... | ()
  ... | inj₂ (changed , reply , admitted , active , stepAbsent , resultAbsent , accepted) = subst
    (λ outcome → X.Completed (script token) current (proj₁ outcome) (proj₂ outcome)) replayed
    (proj₂ (proj₂ (progress token current)))
    where
    earlier = token , metadata
    later = observe token current
    samePublication = trans same (cong proj₁
      (fresh token metadata before changed reply admitted active stepAbsent resultAbsent accepted))
    admittedCurrent = trans (cong (admit (token , later)) (cong Step.registration samePublication))
      (trans (cong (admit (token , later)) (K.publicationKeepsRegistration earlier before changed reply accepted)) admitted)
    activeCurrent = trans (cong (λ state → Store.lookupCancellation state token) samePublication)
      (trans (K.publicationKeepsCancellation earlier before changed reply accepted) active)
    stepCurrent = trans (cong (λ state → Store.lookupSaved state token (key token)) samePublication)
      (K.publishedStepReadable earlier before changed reply accepted stepAbsent)
    resultCurrent = trans (cong (λ state → Store.lookupSaved state token Step.resultKey) samePublication)
      (K.publishedResultReadable earlier before changed reply accepted resultAbsent)
    sameValue : ∀ {first second : Wire.Value} → just first ≡ just second → first ≡ second
    sameValue refl = refl
    replayed = trans (allowedAdmission token later current admittedCurrent)
      (trans (K.replay (token , later) current reply reply activeCurrent stepCurrent resultCurrent)
        (cong (λ value → current , Step.done value) (sameValue (trans (sym resultCurrent) present))))

-- The service resolves completed historical journals before checking current
-- policy or admitting a new publication. This is the same exact, whole-World
-- readback used by the closed operation controls; an old repeated plan is never
-- converted into the new one-publication plan. It is not a new public tool.
module Historical (library : Library.Contract) (postgres : Controls.PostgreSQL) where
  module Read = Controls.Readback library postgres
  operation = Read.operation
  Goal = Read.Goal
  everyInterruptedReadPreservesWorld = Read.everyInterruptedReadPreservesWorld
  completedRetryReturnsExactJournal = Read.completedRetryReturnsExactJournal
