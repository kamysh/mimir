{-# OPTIONS --safe #-}
-- Relate every selected-review transition to the shared batch accounting.
-- Finished states retain their unused allowance in the external account;
-- starting another selected revision does not replenish either counter.
module Mimir.JudgeControllerBudget where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Product using (Σ; _,_)
import Data.Maybe
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Mimir.ReviewObservation using (Pin)
import Mimir.JudgeReview as Review
import Mimir.JudgeBudget as Budget
import Mimir.ProviderQueue as Provider

module Accounting (Payload : Set) (selected : Pin) where
  module C = Review.Controller Payload selected

  continuationBudget : C.Continue → Budget.Budget → Set
  continuationBudget (C.ask fuel feedback) remaining = fuel ≡ remaining
  continuationBudget (C.invoke fuel request) remaining = fuel ≡ remaining
  continuationBudget (C.observe fuel purpose) remaining = fuel ≡ remaining
  continuationBudget (C.reconsider fuel feedback) remaining = fuel ≡ remaining
  continuationBudget (C.finish result) remaining = ⊤

  Aligned : C.State → Budget.Budget → Set
  Aligned (C.ready fuel feedback) remaining = fuel ≡ remaining
  Aligned (C.tracing event continuation) remaining = continuationBudget continuation remaining
  Aligned (C.modelPending fuel) remaining = fuel ≡ remaining
  Aligned (C.toolPending fuel request) remaining = fuel ≡ remaining
  Aligned (C.receiptPending fuel purpose) remaining = fuel ≡ remaining
  Aligned (C.finished result) remaining = ⊤

  record Transition (before : Budget.Budget) (state : C.State) : Set where
    constructor transition
    field
      remaining : Budget.Budget
      charges : List Budget.Charge
      trace : Budget.Trace before charges remaining
      aligned : Aligned state remaining

  unchanged : ∀ {fuel state} → Aligned state fuel → Transition fuel state
  unchanged {fuel} proof = transition fuel [] Budget.empty proof

  provider : ∀ {models tools state} → Aligned state (Budget.budget models tools) →
    Transition (Budget.budget (suc models) tools) state
  provider {models} {tools} proof = transition (Budget.budget models tools)
    (Budget.provider ∷ []) (Budget.spent refl Budget.empty) proof

  tool : ∀ {models tools state} → Aligned state (Budget.budget models tools) →
    Transition (Budget.budget models (suc tools)) state
  tool {models} {tools} proof = transition (Budget.budget models tools)
    (Budget.tool ∷ []) (Budget.spent refl Budget.empty) proof

  resumeAligned : ∀ continuation fuel → continuationBudget continuation fuel →
    Aligned (C.Step.state (C.resume continuation)) fuel
  resumeAligned (C.ask fuel feedback) .fuel refl = refl
  resumeAligned (C.invoke fuel request) .fuel refl = refl
  resumeAligned (C.observe fuel purpose) .fuel refl = refl
  resumeAligned (C.reconsider fuel feedback) .fuel refl = refl
  resumeAligned (C.finish result) remaining proof = tt

  pendingAligned : ∀ fuel purpose → Aligned (C.Step.state (C.pendingReceipt fuel purpose)) fuel
  pendingAligned fuel C.afterReview = refl
  pendingAligned fuel C.afterLoss = refl
  pendingAligned fuel C.afterDone = tt
  pendingAligned fuel (C.afterIndeterminate faultValue) = refl

  accountStep : ∀ state input fuel → Aligned state fuel →
    Transition fuel (C.Step.state (C.step state input))
  accountStep state C.stop fuel aligned = unchanged tt

  accountStep (C.ready (C.budget zero tools) feedback) C.tick ._ refl = unchanged tt
  accountStep (C.ready (C.budget (suc models) tools) feedback) C.tick ._ refl = provider refl
  accountStep (C.tracing event continuation) C.tick fuel aligned = unchanged aligned
  accountStep (C.modelPending actual) C.tick fuel aligned = unchanged aligned
  accountStep (C.toolPending actual request) C.tick fuel aligned = unchanged aligned
  accountStep (C.receiptPending actual purpose) C.tick fuel aligned = unchanged aligned
  accountStep (C.finished result) C.tick fuel aligned = unchanged tt

  accountStep (C.tracing event continuation) C.traceWritten fuel aligned =
    unchanged (resumeAligned continuation fuel aligned)
  accountStep (C.ready actual feedback) C.traceWritten fuel aligned = unchanged aligned
  accountStep (C.modelPending actual) C.traceWritten fuel aligned = unchanged aligned
  accountStep (C.toolPending actual request) C.traceWritten fuel aligned = unchanged aligned
  accountStep (C.receiptPending actual purpose) C.traceWritten fuel aligned = unchanged aligned
  accountStep (C.finished result) C.traceWritten fuel aligned = unchanged tt

  accountStep (C.tracing event continuation) C.traceWriteFailed fuel aligned = unchanged tt
  accountStep (C.ready actual feedback) C.traceWriteFailed fuel aligned = unchanged aligned
  accountStep (C.modelPending actual) C.traceWriteFailed fuel aligned = unchanged aligned
  accountStep (C.toolPending actual request) C.traceWriteFailed fuel aligned = unchanged aligned
  accountStep (C.receiptPending actual purpose) C.traceWriteFailed fuel aligned = unchanged aligned
  accountStep (C.finished result) C.traceWriteFailed fuel aligned = unchanged tt

  accountStep (C.ready actual feedback) C.timeout fuel aligned = unchanged aligned
  accountStep (C.tracing event continuation) C.timeout fuel aligned = unchanged tt
  accountStep (C.modelPending actual) C.timeout fuel aligned = unchanged tt
  accountStep (C.toolPending actual (C.call (C.query operation) arguments)) C.timeout fuel aligned = unchanged tt
  accountStep (C.toolPending actual (C.call C.review arguments)) C.timeout .actual refl = unchanged refl
  accountStep (C.receiptPending actual purpose) C.timeout fuel aligned = unchanged tt
  accountStep (C.finished result) C.timeout fuel aligned = unchanged tt

  accountStep (C.modelPending actual) (C.modelReply C.done) .actual refl = unchanged refl
  accountStep (C.modelPending (C.budget models zero)) (C.modelReply (C.useTool request)) ._ refl = unchanged tt
  accountStep (C.modelPending (C.budget models (suc tools))) (C.modelReply (C.useTool request)) ._ refl = tool refl
  accountStep (C.modelPending (C.budget models zero)) (C.modelReply (C.malformed faultValue)) ._ refl = unchanged tt
  accountStep (C.modelPending (C.budget models (suc tools))) (C.modelReply (C.malformed faultValue)) ._ refl = tool refl
  accountStep (C.ready actual feedback) (C.modelReply action) fuel aligned = unchanged aligned
  accountStep (C.tracing event continuation) (C.modelReply action) fuel aligned = unchanged aligned
  accountStep (C.toolPending actual request) (C.modelReply action) fuel aligned = unchanged aligned
  accountStep (C.receiptPending actual purpose) (C.modelReply action) fuel aligned = unchanged aligned
  accountStep (C.finished result) (C.modelReply action) fuel aligned = unchanged tt

  accountStep (C.ready (C.budget models zero) feedback) (C.queuedTool request) ._ refl = unchanged tt
  accountStep (C.ready (C.budget models (suc tools)) feedback) (C.queuedTool request) ._ refl = tool refl
  accountStep (C.tracing event continuation) (C.queuedTool request) fuel aligned = unchanged aligned
  accountStep (C.modelPending actual) (C.queuedTool request) fuel aligned = unchanged aligned
  accountStep (C.toolPending actual current) (C.queuedTool request) fuel aligned = unchanged aligned
  accountStep (C.receiptPending actual purpose) (C.queuedTool request) fuel aligned = unchanged aligned
  accountStep (C.finished result) (C.queuedTool request) fuel aligned = unchanged tt

  accountStep (C.ready (C.budget models zero) feedback) (C.queuedMalformed faultValue) ._ refl = unchanged tt
  accountStep (C.ready (C.budget models (suc tools)) feedback) (C.queuedMalformed faultValue) ._ refl = tool refl
  accountStep (C.tracing event continuation) (C.queuedMalformed faultValue) fuel aligned = unchanged aligned
  accountStep (C.modelPending actual) (C.queuedMalformed faultValue) fuel aligned = unchanged aligned
  accountStep (C.toolPending actual current) (C.queuedMalformed faultValue) fuel aligned = unchanged aligned
  accountStep (C.receiptPending actual purpose) (C.queuedMalformed faultValue) fuel aligned = unchanged aligned
  accountStep (C.finished result) (C.queuedMalformed faultValue) fuel aligned = unchanged tt

  accountStep (C.toolPending actual (C.call (C.query operation) arguments)) (C.toolReply (C.returned value)) .actual refl = unchanged refl
  accountStep (C.toolPending actual (C.call C.review arguments)) (C.toolReply (C.returned value)) .actual refl = unchanged refl
  accountStep (C.toolPending actual (C.call (C.query operation) arguments)) (C.toolReply (C.refused faultValue)) .actual refl = unchanged refl
  accountStep (C.toolPending actual (C.call C.review arguments)) (C.toolReply (C.refused faultValue)) .actual refl = unchanged refl
  accountStep (C.toolPending actual (C.call (C.query operation) arguments)) (C.toolReply C.lost) fuel aligned = unchanged tt
  accountStep (C.toolPending actual (C.call C.review arguments)) (C.toolReply C.lost) .actual refl = unchanged refl
  accountStep (C.toolPending actual (C.call (C.query operation) arguments)) (C.toolReply (C.indeterminate faultValue)) fuel aligned = unchanged tt
  accountStep (C.toolPending actual (C.call C.review arguments)) (C.toolReply (C.indeterminate faultValue)) .actual refl = unchanged refl
  accountStep (C.ready actual feedback) (C.toolReply reply) fuel aligned = unchanged aligned
  accountStep (C.tracing event continuation) (C.toolReply reply) fuel aligned = unchanged aligned
  accountStep (C.modelPending actual) (C.toolReply reply) fuel aligned = unchanged aligned
  accountStep (C.receiptPending actual purpose) (C.toolReply reply) fuel aligned = unchanged aligned
  accountStep (C.finished result) (C.toolReply reply) fuel aligned = unchanged tt

  accountStep (C.receiptPending actual purpose) (C.receipt (C.acknowledged receiptEvidence)) fuel aligned = unchanged tt
  accountStep (C.receiptPending actual purpose) (C.receipt C.changed) fuel aligned = unchanged tt
  accountStep (C.receiptPending actual purpose) (C.receipt C.pending) .actual refl = unchanged (pendingAligned actual purpose)
  accountStep (C.receiptPending actual purpose) (C.receipt C.unavailable) fuel aligned = unchanged tt
  accountStep (C.ready actual feedback) (C.receipt reply) fuel aligned = unchanged aligned
  accountStep (C.tracing event continuation) (C.receipt reply) fuel aligned = unchanged aligned
  accountStep (C.modelPending actual) (C.receipt reply) fuel aligned = unchanged aligned
  accountStep (C.toolPending actual request) (C.receipt reply) fuel aligned = unchanged aligned
  accountStep (C.finished result) (C.receipt reply) fuel aligned = unchanged tt

  record Machine (initial : Budget.Budget) : Set where
    constructor tracked
    field
      control : C.State
      accounting : Provider.Account initial
      aligned : Aligned control (Provider.Account.remaining accounting)

  start : ∀ {initial} → Provider.Account initial → Machine initial
  start accounting = tracked (C.ready (Provider.Account.remaining accounting) C.initial) accounting refl

  -- The next selected experience starts from precisely the existing account.
  -- In particular, a per-experience controller cannot reset batch fuel.
  startRetainsAccount : ∀ {initial} (accounting : Provider.Account initial) →
    Machine.accounting (start accounting) ≡ accounting
  startRetainsAccount accounting = refl

  initialMachine : ∀ initial → Machine initial
  initialMachine initial = start (Provider.startAccount initial)

  step : ∀ {initial} → Machine initial → C.Input → Machine initial
  step (tracked control (Provider.account before past history) aligned) input
    with accountStep control input before aligned
  ... | transition remaining charges trace alignedAfter =
    tracked (C.Step.state (C.step control input))
      (Provider.account remaining (past ++ charges) (Budget.join history trace)) alignedAfter

  stepPreservesController : ∀ {initial} (machine : Machine initial) input →
    Machine.control (step machine input) ≡ C.Step.state (C.step (Machine.control machine) input)
  stepPreservesController (tracked control (Provider.account before past history) aligned) input
    with accountStep control input before aligned
  ... | transition remaining charges trace alignedAfter = refl

  run : ∀ {initial} → Machine initial → List C.Input → Machine initial
  run machine [] = machine
  run machine (input ∷ rest) = run (step machine input) rest

  runPreservesController : ∀ {initial} (machine : Machine initial) inputs →
    Machine.control (run machine inputs) ≡ C.after (Machine.control machine) inputs
  runPreservesController machine [] = refl
  runPreservesController machine (input ∷ rest)
    rewrite runPreservesController (step machine input) rest | stepPreservesController machine input = refl

  allRunsModelsBounded : ∀ {initial} (machine : Machine initial) inputs →
    Budget.count Budget.modelCost (Provider.Account.charges (Machine.accounting (run machine inputs))) ≤
      Budget.Budget.models initial
  allRunsModelsBounded machine inputs = Provider.requestsBounded (Machine.accounting (run machine inputs))

  allRunsToolsBounded : ∀ {initial} (machine : Machine initial) inputs →
    Budget.count Budget.toolCost (Provider.Account.charges (Machine.accounting (run machine inputs))) ≤
      Budget.Budget.tools initial
  allRunsToolsBounded machine inputs = Provider.attemptsBounded (Machine.accounting (run machine inputs))

  TraceTo : Budget.Budget → Budget.Budget → Set
  TraceTo before after = Σ (List Budget.Charge) (λ charges → Budget.Trace before charges after)

  prependTrace : ∀ {before middle after charge} → Budget.consume before charge ≡ Data.Maybe.just middle →
    TraceTo middle after → TraceTo before after
  prependTrace {charge = charge} permission (charges , trace) = charge ∷ charges , Budget.spent permission trace

  joinEmpty : ∀ {before charges after} (trace : Budget.Trace before charges after) →
    (charges ++ [] , Budget.join trace Budget.empty) ≡ (charges , trace)
  joinEmpty Budget.empty = refl
  joinEmpty (Budget.spent permission rest) = cong (prependTrace permission) (joinEmpty rest)

  stopRetainsAccount : ∀ {initial} (machine : Machine initial) →
    Machine.accounting (step machine C.stop) ≡ Machine.accounting machine
  stopRetainsAccount (tracked control (Provider.account before past history) aligned) =
    cong (λ { (charges , trace) → Provider.account before charges trace }) (joinEmpty history)
