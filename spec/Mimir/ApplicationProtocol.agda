{-# OPTIONS --safe #-}
-- Concrete dispatch for every public application request. Subprotocols retain
-- their typed effects, failures and commit receipts. Retrieval is a transition
-- system because concurrent data can grow; no arbitrary traversal fuel is used.
module Mimir.ApplicationProtocol where

open import Data.Bool using (Bool; true; false)
open import Data.Float.Base using (Float)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.PublicRequest as Public
import Mimir.PosteriorComputation as Posterior
import Mimir.GraphMutationProtocol as Mutation
import Mimir.GraphReadProtocol as Read
import Mimir.GraphDeletion as Deletion
import Mimir.ProjectDeletion as Project
import Mimir.InferenceProtocol as Inference
import Mimir.GroundingPublication as Ground
import Mimir.EvidenceRead as Evidence
import Mimir.DocumentLoading as Documents
import Mimir.DocumentQuery as DocumentQuery
import Mimir.RetrievalProtocol as Retrieval
import Mimir.RetrievalRanking as Ranking
import Mimir.LearningContextProtocol as Context
import Mimir.LearningOperations as Learning
import Mimir.LearningQueryProtocol as Query
import Mimir.LearningCandidates as Candidates
import Mimir.LearningCapabilities as Capabilities
import Mimir.CandidateGraph as Graph
import Mimir.Effects as Effects
import Mimir.Validation as Validation
import Mimir.McpErrors as Errors
import Mimir.StandardLibrary as Library
import Mimir.PublicEncoding as Encoding
import Mimir.ConfigurationValues as Configuration
import Mimir.StorageReadBinding as Storage
import Mimir.OperationControls as Controls
import Mimir.ExperienceSourceRecovery as Source
import Mimir.SweepRecovery as Sweep
import Mimir.IndependentBeliefRecovery as Independent
import Mimir.ReviewPublicationRecovery as ReviewPublication
import Mimir.ReviewPreparationRecovery as ReviewPreparation
import Mimir.PublicOperationCatalogue as Catalogue
import Mimir.Recovery as Recovery
import Mimir.StructuredValue as Wire
import Mimir.ToolCatalog as Tools
import Mimir.ApplicationStore as Store
import Mimir.PublicRetrievalRecovery as Search
import Mimir.PublicDocumentQueryRecovery as DocumentSearch
module Correction = Errors.AgentCorrection

configurationCorrection : Validation.Fault → Correction.Claim
configurationCorrection detail = Correction.claim
  (Correction.item Correction.configuration detail
    (toList "A user-chosen retirement.grace_hours value in Mimir configuration.")
    (toList "Ask the user to choose or repair the configured retention period. Do not send a per-call override or guess a default.")) []

record Environment : Set₁ where
  field
    library : Library.Contract
    format : Encoding.Formatting
    configuration : Configuration.Config
    databaseSum : List Float → Float
    vectors : Storage.VectorOperations
    postgres : Controls.PostgreSQL
    serverTime : ℕ → Store.World → ℤ
    utcTimestamp : Text → Validation.Fault ⊎ ℤ
    allocateOwner : ℕ → Store.World → Independent.Allocation
    sourcePostgres : Source.PostgreSQL
    sweepObservation : ℕ → Store.World → Sweep.Metadata
    reviewDependencies : ReviewPublication.Dependencies
    reviewCodec : ReviewPreparation.AllocationEncoding.Codec format
    database dimension : ℕ
    calculator : Posterior.Calculator
    embeddingsEnabled : Bool
    f32 : Ranking.F32
    unicode : Ranking.Unicode
    databaseTextBefore : Text → Text → Bool
    now : ℤ
    posteriorTime : ℤ -- PostgreSQL sample after the learning lock, distinct from recorded metadata time
    retirementPolicy : Validation.Fault ⊎ ℤ
    candidateClock : Candidates.Candidate → ℤ
    candidateIdentity : Candidates.Candidate → ℕ
    chunkIdentity : ℕ → ℕ
    reviewBackend : Store.World → ReviewPublication.Preparing.Claim → Text ⊎ List Store.Vector
    reviewEnvironment : ReviewPreparation.Registered.Environment library format database databaseSum calculator
      reviewDependencies reviewCodec postgres

module Run (environment : Environment) where
  open Environment environment
  module C = Catalogue.Run library format databaseSum calculator f32 unicode vectors configuration
    databaseTextBefore allocateOwner database postgres serverTime utcTimestamp sourcePostgres sweepObservation
    reviewDependencies reviewCodec reviewBackend
  open C public using (ReadRequest)
    renaming (graphCall to graphRead; relevantCall to relevantRead; evidenceCall to evidenceRead; documentCall to documentRead)

  Call = C.Call
  choice : Call → C.Choice
  choice = C.resolve
  kind : Call → C.Kind
  kind call = C.Choice.kind (choice call)
  input : (call : Call) → C.Input (kind call)
  input call = C.Choice.input (choice call)
  certificate : (call : Call) → C.Certificate (kind call)
  certificate = C.selectedCertificate reviewEnvironment
  operation : (call : Call) → Recovery.RecoverableFor Store.World (C.Input (kind call))
    (C.Result (kind call)) (C.Goal (kind call))
  operation call = C.executable (kind call) (certificate call)
  module O (call : Call) = Recovery.RecoverableFor (operation call)
  module Checked (call : Call) = Recovery.CheckedFor (operation call) (C.Success (kind call))

  -- There is one state constructor. Its operation is selected above by the
  -- actual closed invocation; no script, goal, physical relation or result can
  -- be supplied to this constructor independently of that operation.
  data State : Set where
    running : (call : Call) (initial : Store.World) →
      Checked.RunState call (input call) initial → State

  start : Tools.Tool → Wire.Value → Store.World → State
  start tool submitted initial = running call initial (Checked.start call (input call) initial)
    where call = C.toolCall tool submitted
  startRead : ReadRequest → Store.World → State
  startRead request initial = running call initial (Checked.start call (input call) initial)
    where call = C.privateRead request

  record Result : Set where
    constructor terminalResult
    field
      call : Call
      initial : Store.World
      terminal : Checked.Terminal call (input call) initial

  resultState : Result → State
  resultState (terminalResult call initial terminal) =
    running call initial (Checked.stopped call terminal)

  reached : Result → Store.World
  reached (terminalResult call initial terminal) =
    Checked.History.current call (Checked.Active.evidence call (Checked.Terminal.active call terminal))

  data Step : State → State → Set where
    observed : ∀ call initial (active : Checked.Active call (input call) initial) effect continuation →
      (exposed : Checked.Active.remaining call active ≡ O.E.ask call effect continuation) →
      (reply : O.Reply call effect) (after : Store.World) →
      (physical : O.Atomic call (Checked.History.current call (Checked.Active.evidence call active)) effect reply after) →
      Step (running call initial (Checked.running call active))
        (running call initial (Checked.continue call active effect continuation exposed reply after physical))
    stopped : ∀ call initial (active : Checked.Active call (input call) initial) →
      (disposition : Checked.Disposition call active) →
      Step (running call initial (Checked.running call active))
        (running call initial (Checked.finish call active disposition))

  record Event : Set where
    constructor event
    field before after : State; physical : Step before after

  data Runs : State → List Event → Result → Set where
    returned : ∀ result → Runs (resultState result) [] result
    advanced : ∀ before after physical events result → Runs after events result →
      Runs before (event before after physical ∷ events) result

  completed : Result → Bool
  completed (terminalResult call initial terminal) with Checked.Terminal.disposition call terminal
  ... | Checked.done reply exposed success = true
  ... | Checked.correction _ = false
  ... | Checked.retry = false
  ... | Checked.fatal _ = false

  -- The public success flag is backed by the actual operation's whole-world
  -- business goal and the exposed returned reply in its physical history.
  Completed : Result → Set
  Completed (terminalResult call initial terminal) =
    Σ (C.Result (kind call)) (λ reply →
      C.Goal (kind call) (input call) initial
        (Checked.History.current call (Checked.Active.evidence call active)) reply ×
      Checked.Active.remaining call active ≡ O.E.done call reply × C.Success (kind call) reply)
    where active = Checked.Terminal.active call terminal

  completedRequiresGoal : ∀ result → completed result ≡ true → Completed result
  completedRequiresGoal (terminalResult call initial terminal) valid with Checked.Terminal.disposition call terminal
  ... | Checked.done reply exposed successful = reply ,
    Checked.doneMeetsGoal call (Checked.Terminal.active call terminal) reply exposed successful , exposed , successful
  ... | Checked.correction _ with valid
  ... | ()
  completedRequiresGoal (terminalResult call initial terminal) valid | Checked.retry with valid
  ... | ()
  completedRequiresGoal (terminalResult call initial terminal) valid | Checked.fatal _ with valid
  ... | ()

  data ReadView : Set where
    basicView : (request : C.Basic.Request) → C.Basic.View request → ReadView
    retrievalView : Search.Request → C.Retrieval.Result → ReadView
    documentView : DocumentSearch.Request → C.DocumentQuery.Result → ReadView

  payloadReadView : (call : Call) → C.Result (kind call) → Store.World → Maybe ReadView
  payloadReadView call reply initial with kind call
  ... | C.basic request = just (basicView request (C.Basic.view request initial))
  ... | C.retrieval request = just (retrievalView request reply)
  ... | C.documentQuery request = just (documentView request reply)
  ... | _ = nothing

  readView : Result → Maybe ReadView
  readView (terminalResult call initial terminal) with Checked.Terminal.disposition call terminal
  ... | Checked.done reply exposed success = payloadReadView call reply initial
  ... | Checked.correction _ = nothing
  ... | Checked.retry = nothing
  ... | Checked.fatal _ = nothing
