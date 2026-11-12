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
import Mimir.JudgeRevision as Revision
import Mimir.JudgeServiceBinding as Service
import Mimir.JudgeBackendComposition as Backend
import Mimir.JudgeWorkflow as Workflow
import Mimir.JudgeHandshake as Handshake
import Mimir.JudgeFinalizationComposition as Finalization
import Mimir.UnixPath as Path
import Mimir.JudgeBatchServiceBinding as BatchService
import Mimir.JudgeClientStartup as ClientStartup
import Mimir.McpClientTransport as Transport
import Mimir.JudgeMcpLifecycle as Client
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (_×_)

module Compose (conversion : Conversion.Contract) (format : Encoding.Formatting)
  (display : Revision.Display) (environment : Application.Environment) (errors : Service.Display)
  (contract model : ℕ) (batchLimit : Maybe ℕ) (project : Maybe Text)
  (mcpProgram : Text) (mcpArguments : List Text) (configurationPath : Path.Path)
  (sizeMaximum : ℕ) where
  private
    module F = Finalization.Bound
    module Batch = BatchService.Bound conversion format display errors environment sizeMaximum
  module W = Workflow.Run conversion format display
    contract model batchLimit project
  private
    module B (clientReady : Handshake.Contract.Ready contract model) selected = Backend.Bound conversion format display environment errors selected

  data External : W.Effect → Set where
    clock : External W.clock
    reportTraceProblem : ∀ failure → External (W.reportTraceProblem failure)


  data Receipt : Backend.BackendState → (effect : W.Effect) → W.Reply effect → Backend.BackendState → Set where
    external : ∀ backend effect → External effect → (reply : W.Reply effect) → Receipt backend effect reply backend
    started : ∀ backend diagnostics reply client →
      ClientStartup.Run.Started conversion diagnostics contract model mcpProgram mcpArguments configurationPath reply client →
      Receipt backend W.startClient reply backend
    began : ∀ backend report reply → Receipt backend (W.beginTrace report) reply backend
    finalized : ∀ backend effect reply → F.Receipt effect reply → Receipt backend (W.finalize effect) reply backend
    selected : ∀ backend effect reply → Batch.SelectionReceipt effect reply → Receipt backend (W.selection effect) reply backend
    observed : ∀ backend effect reply → Batch.ReadbackReceipt effect reply → Receipt backend (W.readback effect) reply backend
    revision : ∀ before after clientReady selected report events result →
      (execution : B.Trace clientReady selected before (W.One.start selected report) events after (W.One.finished result)) →
      Receipt before (W.revision clientReady selected report)
        (W.reviewed result events (B.runnerTrace clientReady selected execution)) after

  Connection : ∀ {before effect reply after} → Maybe Client.Client → Receipt before effect reply after → Maybe Client.Client → Set
  Connection before (started backend diagnostics reply client receipt) after = before ≡ nothing × after ≡ client
  Connection before (external _ _ _ _) after = before ≡ after
  Connection before (began _ _ _) after = before ≡ after
  Connection before (finalized _ _ _ _) after = before ≡ after
  Connection before (selected _ _ _ receipt) after = Client.Chain before (Batch.selectionCalls receipt) after
  Connection before (observed _ _ _ receipt) after = Client.Chain before (Batch.readbackCalls receipt) after
  Connection before (revision _ _ clientReady observedSnapshot _ _ _ execution) after =
    Client.Chain before (B.traceIssued clientReady observedSnapshot execution) after

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
