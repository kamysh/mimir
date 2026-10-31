{-# OPTIONS --safe #-}
-- Provider batch sequencing is separate from tool interpretation. Every call,
-- including malformed arguments, is yielded once and receives its own result.
-- Draining an existing batch consumes tool budget, not provider budget.
module Mimir.ProviderQueue where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (++-assoc; ++-identityʳ; map-++)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong)
open import Mimir.Text using (Text; Nonempty; Bounded; nonempty?; bounded?)
open import Mimir.SourceReview using (_≟Text_)
open import Mimir.Validation
open import Mimir.Collections using (module Equality; atMost; checkCount)
import Mimir.JudgeBudget as Budget

module IDs = Equality Text _≟Text_

record Account (initial : Budget.Budget) : Set where
  constructor account
  field
    remaining : Budget.Budget
    charges : List Budget.Charge
    trace : Budget.Trace initial charges remaining

startAccount : ∀ initial → Account initial
startAccount initial = account initial [] Budget.empty

charge : ∀ {initial} → Account initial → Budget.Charge → Maybe (Account initial)
charge (account before charges trace) kind with Budget.consume before kind in permission
... | nothing = nothing
... | just after = just (account after (charges ++ (kind ∷ []))
  (Budget.join trace (Budget.spent permission Budget.empty)))

requestsBounded : ∀ {initial} (a : Account initial) →
  Budget.count Budget.modelCost (Account.charges a) ≤ Budget.Budget.models initial
requestsBounded a = Budget.modelRequestsBounded (Account.trace a)

attemptsBounded : ∀ {initial} (a : Account initial) →
  Budget.count Budget.toolCost (Account.charges a) ≤ Budget.Budget.tools initial
attemptsBounded a = Budget.toolAttemptsBounded (Account.trace a)

module Queue (Payload : Set) where
  record Call : Set where
    constructor call
    field identity name : Text; arguments : Fault ⊎ Payload

  data NamePolicy : Set where required deferred : NamePolicy

  NameValid : NamePolicy → Text → Set
  NameValid required name = Nonempty name
  NameValid deferred name = ⊤

  checkName : ∀ policy name → Checked (NameValid policy name)
  checkName required name = check (fault [] emptyText "provider function name is empty") (nonempty? name)
  checkName deferred name = accepted tt

  CallValidFor : NamePolicy → Call → Set
  CallValidFor policy c = Nonempty (Call.identity c) ×
    (Bounded 128 (Call.identity c) × NameValid policy (Call.name c))

  CallValid : Call → Set
  CallValid = CallValidFor required

  checkCallFor : ∀ policy c → Checked (CallValidFor policy c)
  checkCallFor policy c = combine
    (check (fault [] emptyText "provider call ID is empty") (nonempty? (Call.identity c)))
    (combine (check (fault [] textTooLong "provider call ID exceeds 128 UTF-8 bytes")
      (bounded? 128 (Call.identity c)))
      (checkName policy (Call.name c)))

  checkCall : ∀ c → Checked (CallValid c)
  checkCall = checkCallFor required

  BatchValidFor : NamePolicy → ℕ → List Call → Set
  BatchValidFor policy maximum calls = atMost maximum calls ×
    (All (CallValidFor policy) calls × IDs.Unique (map Call.identity calls))

  BatchValid : ℕ → List Call → Set
  BatchValid = BatchValidFor required

  checkBatchFor : ∀ policy maximum calls → Checked (BatchValidFor policy maximum calls)
  checkBatchFor policy maximum calls = combine (checkCount maximum calls)
    (combine (allChecked (checkCallFor policy) calls) (IDs.checkUnique (map Call.identity calls)))

  checkBatch : ∀ maximum calls → Checked (BatchValid maximum calls)
  checkBatch = checkBatchFor required

  -- An independent sequence relation records exactly which call each result
  -- answers; argument validity does not remove a call from this relation.
  data Progress (original : List Call) : List (Text × Payload) → List Call → Set where
    begin : Progress original [] original
    answered : ∀ {results current rest} → Progress original results (current ∷ rest) →
      (value : Payload) → Progress original (results ++ ((Call.identity current , value) ∷ [])) rest

  partition : ∀ {original results pending} → Progress original results pending →
    map proj₁ results ++ map Call.identity pending ≡ map Call.identity original
  partition begin = refl
  partition (answered {results} {current} {rest} previous value) =
    trans (cong (_++ map Call.identity rest) (map-++ proj₁ results ((Call.identity current , value) ∷ [])))
      (trans (++-assoc (map proj₁ results) (Call.identity current ∷ []) (map Call.identity rest))
        (partition previous))

  allResultsInOrder : ∀ {original results} → Progress original results [] →
    map proj₁ results ≡ map Call.identity original
  allResultsInOrder {results = results} progress = trans (sym (++-identityʳ (map proj₁ results))) (partition progress)

  record Turn : Set where
    constructor turn
    field message : Payload; results : List (Text × Payload)

  data StopReason : Set where
    complete cancelled providerLimit toolLimit sequenceFailure transportFailure : StopReason
    invalidBatch : Fault → StopReason

  data Phase : Set where
    ready requesting : List Turn → Phase
    waiting : (history : List Turn) (message : Payload) (original : List Call)
      (results : List (Text × Payload)) (current : Call) (rest : List Call) →
      Progress original results (current ∷ rest) → Phase
    stopped : StopReason → Phase

  data Input : Set where
    next stop transportLost : Input
    reply : Payload → List Call → Input
    feedback : Payload → Input

  data Effect : Set where
    request : List Turn → Effect
    yieldCall : Call → Effect
    yieldDone cancelOwned : Effect
    failed : StopReason → Effect

  record Machine (initial : Budget.Budget) : Set where
    constructor machine
    field phase : Phase; accounting : Account initial

  record Step (initial : Budget.Budget) : Set where
    constructor stepResult
    field state : Machine initial; effects : List Effect

  fail : ∀ {initial} → Account initial → StopReason → Step initial
  fail accounting reason = stepResult (machine (stopped reason) accounting) (failed reason ∷ [])

  dispatch : ∀ {initial} → Account initial → (history : List Turn) (message : Payload)
    (original : List Call) (results : List (Text × Payload)) (pending : List Call) →
    Progress original results pending → Step initial
  dispatch accounting history message original results [] progress =
    stepResult (machine (ready (history ++ (turn message results ∷ []))) accounting) []
  dispatch accounting history message original results (current ∷ rest) progress
    with charge accounting Budget.tool
  ... | nothing = fail accounting toolLimit
  ... | just spent = stepResult
    (machine (waiting history message original results current rest progress) spent) (yieldCall current ∷ [])

  NoProviderRequest : Effect → Set
  NoProviderRequest (request history) = ⊥
  NoProviderRequest _ = ⊤

  dispatchHasNoProviderRequest : ∀ {initial} (accounting : Account initial) history message original results pending progress →
    All NoProviderRequest (Step.effects (dispatch accounting history message original results pending progress))
  dispatchHasNoProviderRequest accounting history message original results [] progress = All.[]
  dispatchHasNoProviderRequest accounting history message original results (current ∷ rest) progress
    with charge accounting Budget.tool
  ... | nothing = tt All.∷ All.[]
  ... | just spent = tt All.∷ All.[]

  dispatchPreservesProviderFuel : ∀ {initial} (accounting : Account initial) history message original results pending progress →
    Budget.Budget.models (Account.remaining (Machine.accounting
      (Step.state (dispatch accounting history message original results pending progress)))) ≡
    Budget.Budget.models (Account.remaining accounting)
  dispatchPreservesProviderFuel accounting history message original results [] progress = refl
  dispatchPreservesProviderFuel (account (Budget.budget models Data.Nat.zero) charges trace)
    history message original results (current ∷ rest) progress = refl
  dispatchPreservesProviderFuel (account (Budget.budget models (Data.Nat.suc tools)) charges trace)
    history message original results (current ∷ rest) progress = refl

  stepWithPolicy : ∀ {initial} → NamePolicy → ℕ → Machine initial → Input → Step initial
  stepWithPolicy policy maximum s@(machine (stopped reason) accounting) input = stepResult s []
  stepWithPolicy policy maximum (machine phase accounting) stop =
    stepResult (machine (stopped cancelled) accounting) (cancelOwned ∷ [])
  stepWithPolicy policy maximum (machine (ready history) accounting) next with charge accounting Budget.provider
  ... | nothing = fail accounting providerLimit
  ... | just spent = stepResult (machine (requesting history) spent) (request history ∷ [])
  stepWithPolicy policy maximum (machine (requesting history) accounting) (reply message calls) with checkBatchFor policy maximum calls
  ... | rejected failure invalid = fail accounting (invalidBatch failure)
  ... | accepted valid with calls
  ...   | [] = stepResult (machine (stopped complete) accounting) (yieldDone ∷ [])
  ...   | current ∷ rest = dispatch accounting history message (current ∷ rest) [] (current ∷ rest) begin
  stepWithPolicy policy maximum (machine (waiting history message original results current rest progress) accounting) (feedback value) =
    dispatch accounting history message original (results ++ ((Call.identity current , value) ∷ [])) rest
      (answered progress value)
  stepWithPolicy policy maximum (machine phase accounting) transportLost = fail accounting transportFailure
  stepWithPolicy policy maximum (machine phase accounting) input = fail accounting sequenceFailure

  step : ∀ {initial} → ℕ → Machine initial → Input → Step initial
  step = stepWithPolicy required

  stoppedNeverRestarts : ∀ {initial} maximum reason (accounting : Account initial) input →
    step maximum (machine (stopped reason) accounting) input ≡
      stepResult (machine (stopped reason) accounting) []
  stoppedNeverRestarts maximum reason accounting input = refl

  initialMachine : ∀ initial → Machine initial
  initialMachine initial = machine (ready []) (startAccount initial)

  -- Every returned state carries its full charge trace back to the original
  -- batch budget, including states reached after cancellation or refusal.
  everyStepRequestsBounded : ∀ {initial} maximum (s : Machine initial) input →
    Budget.count Budget.modelCost (Account.charges (Machine.accounting (Step.state (step maximum s input)))) ≤
      Budget.Budget.models initial
  everyStepRequestsBounded maximum s input = requestsBounded (Machine.accounting (Step.state (step maximum s input)))

  everyStepAttemptsBounded : ∀ {initial} maximum (s : Machine initial) input →
    Budget.count Budget.toolCost (Account.charges (Machine.accounting (Step.state (step maximum s input)))) ≤
      Budget.Budget.tools initial
  everyStepAttemptsBounded maximum s input = attemptsBounded (Machine.accounting (Step.state (step maximum s input)))

  everyPolicyRequestsBounded : ∀ {initial} policy maximum (s : Machine initial) input →
    Budget.count Budget.modelCost (Account.charges (Machine.accounting (Step.state (stepWithPolicy policy maximum s input)))) ≤
      Budget.Budget.models initial
  everyPolicyRequestsBounded policy maximum s input = requestsBounded (Machine.accounting (Step.state (stepWithPolicy policy maximum s input)))

  everyPolicyAttemptsBounded : ∀ {initial} policy maximum (s : Machine initial) input →
    Budget.count Budget.toolCost (Account.charges (Machine.accounting (Step.state (stepWithPolicy policy maximum s input)))) ≤
      Budget.Budget.tools initial
  everyPolicyAttemptsBounded policy maximum s input = attemptsBounded (Machine.accounting (Step.state (stepWithPolicy policy maximum s input)))
