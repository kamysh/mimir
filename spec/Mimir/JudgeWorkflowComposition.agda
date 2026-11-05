{-# OPTIONS --safe #-}
-- Whole-batch composition retaining one backend state between revisions.
-- A revision cannot be discharged by a fabricated runner transcript: every
-- model/scoped-tool receipt must satisfy JudgeBackendComposition.
module Mimir.JudgeWorkflowComposition where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Mimir.Text using (Text)
import Mimir.StandardLibrary as Conversion
import Mimir.PublicEncoding as Encoding
import Mimir.ApplicationProtocol as Application
import Mimir.JudgeConfiguration as Config
import Mimir.JudgeHarnessAdapter as Harness
import Mimir.JudgeServiceBinding as Service
import Mimir.JudgeBackendComposition as Backend
import Mimir.JudgeWorkflow as Workflow
import Mimir.JudgeHandshake as Handshake
import Mimir.JudgeFinalizationComposition as Finalization
import Mimir.JudgeStateOperations as State
import Mimir.NotificationConfig as Email
import Mimir.UnixPath as Path
import Mimir.UUIDV4 as UUID
import Mimir.JudgeBatchServiceBinding as BatchService
import Mimir.JudgeClientStartup as ClientStartup
import Mimir.McpClientTransport as Transport
import Mimir.JudgeMcpLifecycle as Client
import Mimir.NotificationCodec as Codec
import Mimir.NotificationDelivery as Delivery
import Mimir.SMTPProtocol as SMTP
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (_×_)

module Compose (conversion : Conversion.Contract) (format : Encoding.Formatting)
  (libraries : Harness.Libraries) (environment : Application.Environment) (errors : Service.Display)
  (config : Config.Llm) (program : Text)
  (contract model batchLimit : ℕ) (project : Maybe Text)
  (mcpProgram : Text) (mcpArguments : List Text) (configurationPath : Path.Path)
  (email : Email.Config) (localTime : ℕ → Text) (sizeMaximum clockMaximum : ℕ)
  (endian : UUID.Endian) (path : Path.Path)
  (json : Codec.JSONLibrary) (buildMessage : SMTP.Message → Delivery.BuildReceipt) where
  private
    module F = Finalization.Bound conversion format localTime sizeMaximum clockMaximum endian path email project json buildMessage
    module S = State.Bound conversion sizeMaximum endian path
    module Batch = BatchService.Bound conversion format (Harness.Libraries.display libraries) errors environment sizeMaximum endian path
  module W = Workflow.Run conversion format (Harness.Libraries.display libraries)
    contract model batchLimit project
  private
    module B (ready : Handshake.Contract.Ready contract model) selected = Backend.Bound conversion format libraries environment errors config program W.initial selected
      (Handshake.CheckedCatalogue.exposed (Handshake.Contract.Ready.catalogue ready))
      sizeMaximum endian path

  data External : W.Effect → Set where
    clock : External W.clock


  data Receipt : Backend.BackendState → (effect : W.Effect) → W.Reply effect → Backend.BackendState → Set where
    external : ∀ backend effect → External effect → (reply : W.Reply effect) → Receipt backend effect reply backend
    started : ∀ backend diagnostics reply client →
      ClientStartup.Run.Started conversion diagnostics contract model mcpProgram mcpArguments configurationPath reply client →
      Receipt backend W.startClient reply backend
    began : ∀ backend report reply → S.Began report 0 reply → Receipt backend (W.beginTrace report) reply backend
    finalized : ∀ backend effect reply → F.Receipt effect reply → Receipt backend (W.finalize effect) reply backend
    selected : ∀ backend effect reply → Batch.SelectionReceipt effect reply → Receipt backend (W.selection effect) reply backend
    observed : ∀ backend effect reply → Batch.ReadbackReceipt effect reply → Receipt backend (W.readback effect) reply backend
    revision : ∀ before after ready selected account report events result →
      (execution : B.Trace ready selected before (W.One.start selected account report) events after (W.One.finished result)) →
      Receipt before (W.revision ready selected account report)
        (W.reviewed result events (B.runnerTrace ready selected execution)) after

  Connection : ∀ {before effect reply after} → Maybe Client.Client → Receipt before effect reply after → Maybe Client.Client → Set
  Connection before (started backend diagnostics reply client receipt) after = before ≡ nothing × after ≡ client
  Connection before (external _ _ _ _) after = before ≡ after
  Connection before (began _ _ _ _) after = before ≡ after
  Connection before (finalized _ _ _ _) after = before ≡ after
  Connection before (selected _ _ _ receipt) after = Client.Chain before (Batch.selectionCalls receipt) after
  Connection before (observed _ _ _ receipt) after = Client.Chain before (Batch.readbackCalls receipt) after
  Connection before (revision _ _ ready snapshot _ _ _ _ execution) after =
    Client.Chain before (B.traceIssued ready snapshot execution) after

  data Runs : Backend.BackendState → Maybe Client.Client → W.P.Script Workflow.R.Report → List W.P.Event →
    Backend.BackendState → Maybe Client.Client → Workflow.R.Report → Set where
    returned : ∀ backend client report → Runs backend client (W.P.done report) [] backend client report
    replied : ∀ before client effect continuation reply middle nextClient events after finalClient report →
      (receipt : Receipt before effect reply middle) → Connection client receipt nextClient →
      Runs middle nextClient (continuation reply) events after finalClient report →
      Runs before client (W.P.ask effect continuation) ((effect , reply) ∷ events) after finalClient report

  workflowTrace : ∀ before client script events after finalClient report →
    Runs before client script events after finalClient report → W.P.Runs script events report
  workflowTrace before client script events after finalClient report (returned backend retained report₁) = W.P.returned report
  workflowTrace before client script events after finalClient report
    (replied before₁ client₁ effect continuation reply middle nextClient events₁ after₁ finalClient₁ report₁ receipt connection execution) =
    W.P.replied effect continuation reply (workflowTrace middle nextClient (continuation reply) events₁ after finalClient report execution)
