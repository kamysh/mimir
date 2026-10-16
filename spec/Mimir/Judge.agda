{-# OPTIONS --safe #-}
-- Pure runner/notification contracts. A confirmed receipt is an observation
-- from the database adapter, never an LLM's assertion. SQL/process/SMTP I/O
-- must implement the assumptions recorded in the correspondence document.
module Mimir.Judge where

open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.Nat using (ℕ; zero; suc; _+_; _≟_)
open import Data.Nat.Properties using (+-suc)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans)

module Completion where
  data Receipt : Set where confirmed pending corrected unavailable : Receipt
  data Status : Set where idle running partial complete blocked : Status

  begin : List Receipt → Status
  begin [] = idle
  begin (_ ∷ _) = running

  nonempty-batch-starts-running : ∀ r rs → begin (r ∷ rs) ≡ running
  nonempty-batch-starts-running r rs = refl

  Confirmed : Receipt → Set
  Confirmed confirmed = ⊤
  Confirmed _ = ⊥

  isConfirmed : Receipt → Bool
  isConfirmed confirmed = true
  isConfirmed _ = false

  allConfirmed : List Receipt → Bool
  allConfirmed [] = true
  allConfirmed (r ∷ rs) = isConfirmed r ∧ allConfirmed rs

  anyConfirmed : List Receipt → Bool
  anyConfirmed [] = false
  anyConfirmed (r ∷ rs) = isConfirmed r ∨ anyConfirmed rs

  finish : List Receipt → Bool → Status
  finish [] false = idle
  finish [] true = blocked
  finish (r ∷ rs) true with anyConfirmed (r ∷ rs)
  ... | true = partial
  ... | false = blocked
  finish (r ∷ rs) false with allConfirmed (r ∷ rs)
  ... | true = complete
  ... | false with anyConfirmed (r ∷ rs)
  ...   | true = partial
  ...   | false = blocked

  all-confirmed-sound : ∀ rs → allConfirmed rs ≡ true → All Confirmed rs
  all-confirmed-sound [] eq = []
  all-confirmed-sound (confirmed ∷ rs) eq = tt ∷ all-confirmed-sound rs eq
  all-confirmed-sound (pending ∷ rs) ()
  all-confirmed-sound (corrected ∷ rs) ()
  all-confirmed-sound (unavailable ∷ rs) ()

  complete-requires-database-receipts : ∀ rs failed →
    finish rs failed ≡ complete → All Confirmed rs
  complete-requires-database-receipts [] false ()
  complete-requires-database-receipts [] true ()
  complete-requires-database-receipts (r ∷ rs) true proof with anyConfirmed (r ∷ rs)
  ... | true = impossible proof
    where
    impossible : partial ≡ complete → All Confirmed (r ∷ rs)
    impossible ()
  ... | false = impossible proof
    where
    impossible : blocked ≡ complete → All Confirmed (r ∷ rs)
    impossible ()
  complete-requires-database-receipts (r ∷ rs) false proof
    with allConfirmed (r ∷ rs) in eq
  ... | true = all-confirmed-sound (r ∷ rs) eq
  ... | false with anyConfirmed (r ∷ rs)
  ...   | true = impossible proof
    where
    impossible : partial ≡ complete → All Confirmed (r ∷ rs)
    impossible ()
  ...   | false = impossible proof
    where
    impossible : blocked ≡ complete → All Confirmed (r ∷ rs)
    impossible ()

  -- A model's completion claim cannot affect the final verdict.
  finishWithClaim : Bool → List Receipt → Bool → Status
  finishWithClaim claim rs failed = finish rs failed
  model-claim-does-not-acknowledge : ∀ claim₁ claim₂ rs failed →
    finishWithClaim claim₁ rs failed ≡ finishWithClaim claim₂ rs failed
  model-claim-does-not-acknowledge claim₁ claim₂ rs failed = refl

module Budget where
  data Action : Set where modelCall toolCall : Action
  record Remaining : Set where
    constructor remaining
    field models tools : ℕ

  spend : Action → Remaining → Maybe Remaining
  spend modelCall (remaining zero tools) = nothing
  spend modelCall (remaining (suc models) tools) = just (remaining models tools)
  spend toolCall (remaining models zero) = nothing
  spend toolCall (remaining models (suc tools)) = just (remaining models tools)

  no-model-call-without-fuel : ∀ tools → spend modelCall (remaining zero tools) ≡ nothing
  no-model-call-without-fuel tools = refl
  no-tool-call-without-fuel : ∀ models → spend toolCall (remaining models zero) ≡ nothing
  no-tool-call-without-fuel models = refl

  -- Each admitted operation spends exactly one of the two independent bounds.
  model-spends-one : ∀ models tools → spend modelCall (remaining (suc models) tools)
    ≡ just (remaining models tools)
  model-spends-one models tools = refl
  tool-spends-one : ∀ models tools → spend toolCall (remaining models (suc tools))
    ≡ just (remaining models tools)
  tool-spends-one models tools = refl

  permitted : Bool → Action → Remaining → Maybe Remaining
  permitted false action fuel = nothing
  permitted true action fuel = spend action fuel
  refused-tool-cannot-spend : ∀ fuel → permitted false toolCall fuel ≡ nothing
  refused-tool-cannot-spend fuel = refl

  -- Admitted traces count every attempted model/tool operation, including
  -- failures. Retries are additional operations, not free recursive steps.
  data Trace : Remaining → List Action → Remaining → Set where
    done : ∀ {fuel} → Trace fuel [] fuel
    model : ∀ {m t actions final} → Trace (remaining m t) actions final →
      Trace (remaining (suc m) t) (modelCall ∷ actions) final
    tool : ∀ {m t actions final} → Trace (remaining m t) actions final →
      Trace (remaining m (suc t)) (toolCall ∷ actions) final

  total : Remaining → ℕ
  total (remaining m t) = m + t

  trace-conserves-budget : ∀ {initial actions final} → Trace initial actions final →
    length actions + total final ≡ total initial
  trace-conserves-budget done = refl
  trace-conserves-budget (model trace) = cong suc (trace-conserves-budget trace)
  trace-conserves-budget (tool {m} {t} trace) =
    trans (cong suc (trace-conserves-budget trace)) (sym (+-suc m t))

-- Diagnostic events are recorded as the runner observes them, before a later
-- model call or successful batch can replace the status snapshot. The concrete
-- file adapter also caps serialized bytes, stores it privately, and retains a
-- bounded number of attempts; those I/O conditions are checked in Rust.
module Diagnostics where
  data Event : Set where
    modelRequest modelReply toolRequest toolResult budgetStop : Event

  data Within (A : Set) : ℕ → Set where
    empty : ∀ {capacity} → Within A capacity
    cons : ∀ {capacity} → A → Within A capacity → Within A (suc capacity)

  capture : ∀ {A capacity} → A → Within A capacity → Within A capacity
  capture {capacity = zero} event empty = empty
  capture {capacity = suc capacity} event empty = cons event empty
  capture {capacity = suc capacity} event (cons first rest) =
    cons first (capture event rest)

  -- The oldest event remains even when the trace fills: exhaustion cannot
  -- erase the sequence that led to it.
  firstSurvives : ∀ {A capacity} (first next : A)
    (rest : Within A capacity) →
    capture next (cons first rest) ≡ cons first (capture next rest)
  firstSurvives first next rest = refl

  record Incident : Set where
    constructor incident
    field
      first : Maybe (Within Event 64)
      latest : Maybe (Within Event 64)
      recovered : Bool

  newFailure : Within Event 64 → Incident → Incident
  newFailure trace (incident nothing latest recovered) =
    incident (just trace) (just trace) false
  newFailure trace (incident (just first) latest recovered) =
    incident (just first) (just trace) false

  completed : Incident → Incident
  completed episode = episode

  idle : Incident → Incident
  idle (incident first latest recovered) = incident first latest true

  completed-preserves-first : ∀ episode →
    Incident.first (completed episode) ≡ Incident.first episode
  completed-preserves-first episode = refl

  repeated-failure-preserves-first : ∀ first latest recovered trace →
    Incident.first (newFailure trace (incident (just first) latest recovered))
      ≡ just first
  repeated-failure-preserves-first first latest recovered trace = refl

  idle-preserves-first : ∀ episode →
    Incident.first (idle episode) ≡ Incident.first episode
  idle-preserves-first (incident first latest recovered) = refl

-- Email may claim that an affected review completed only after a later batch
-- observed its database acknowledgement. An empty queue is a separate fact:
-- it closes the alert episode but cannot itself prove that a specific review
-- was accepted. The Rust adapter supplies only database-observed completions.
module NotificationEvidence where
  data Claim : Set where confirmed unverified : Claim

  record Episode : Set where
    constructor episode
    field
      confirmedIDs : List ℕ
      queueIdle : Bool

  contains : ℕ → List ℕ → Bool
  contains id [] = false
  contains id (candidate ∷ rest) with id ≟ candidate
  ... | yes _ = true
  ... | no _ = contains id rest

  claim : ℕ → Episode → Claim
  claim id (episode confirmedIDs idle) with contains id confirmedIDs
  ... | true = confirmed
  ... | false = unverified

  completed : Bool → ℕ → Episode → Episode
  completed true id (episode confirmedIDs idle) = episode (id ∷ confirmedIDs) idle
  completed false id current = current

  observedIdle : Episode → Episode
  observedIdle (episode confirmedIDs idle) = episode confirmedIDs true

  idle-cannot-create-confirmation : ∀ id current →
    claim id (observedIdle current) ≡ claim id current
  idle-cannot-create-confirmation id (episode confirmedIDs idle) = refl

  unconfirmed-batch-cannot-create-confirmation : ∀ id current →
    claim id (completed false id current) ≡ claim id current
  unconfirmed-batch-cannot-create-confirmation id current = refl

-- Candidate references in a model request must resolve to belief declarations
-- in that same request before the host dispatches it to MCP or the store.
-- Existing belief IDs require their separate scope check in the adapter.
module PreDispatch where
  data Declaration : Set where belief patternDeclaration : ℕ → Declaration
  data Target : Set where existing candidate : ℕ → Target

  declaresBelief : ℕ → List Declaration → Bool
  declaresBelief key [] = false
  declaresBelief key (belief declared ∷ rest) with declared ≟ key
  ... | yes _ = true
  ... | no _ = declaresBelief key rest
  declaresBelief key (patternDeclaration declared ∷ rest) = declaresBelief key rest

  validTarget : List Declaration → Target → Bool
  validTarget declarations (existing id) = true
  validTarget declarations (candidate key) = declaresBelief key declarations

  validTargets : List Declaration → List Target → Bool
  validTargets declarations [] = true
  validTargets declarations (target ∷ rest) =
    validTarget declarations target ∧ validTargets declarations rest

  dispatch : List Declaration → List Target → Maybe (List Target)
  dispatch declarations targets with validTargets declarations targets
  ... | true = just targets
  ... | false = nothing

  undeclared-candidate-never-dispatched : ∀ declarations key rest →
    declaresBelief key declarations ≡ false →
    dispatch declarations (candidate key ∷ rest) ≡ nothing
  undeclared-candidate-never-dispatched declarations key rest absent
    rewrite absent = refl

  pattern-declaration-is-not-a-belief : ∀ declarations key rest →
    declaresBelief key declarations ≡ false →
    dispatch (patternDeclaration key ∷ declarations) (candidate key ∷ rest) ≡ nothing
  pattern-declaration-is-not-a-belief declarations key rest absent =
    undeclared-candidate-never-dispatched
      (patternDeclaration key ∷ declarations) key rest absent

-- A malformed model request is returned as corrective tool feedback; it is
-- not a deferred source revision. Immutable candidate-key conflicts can be
-- deferred after bounded in-run correction, while the watcher keeps one alert
-- episode and its existing backoff for incomplete batches.
module Watch where
  data Outcome : Set where success rejected infrastructureFailure : Outcome
  data Rejection : Set where invalidRequest candidateConflict : Rejection
  data RevisionCheck : Set where unchanged corrected resolved : RevisionCheck
  data Cycle : Set where failed completed idle : Cycle

  deferRejection : Rejection → RevisionCheck → Bool
  deferRejection invalidRequest revision = false
  deferRejection candidateConflict unchanged = true
  deferRejection candidateConflict corrected = false
  deferRejection candidateConflict resolved = false

  invalid-request-remains-eligible : ∀ revision →
    deferRejection invalidRequest revision ≡ false
  invalid-request-remains-eligible revision = refl

  -- A completed batch does not prove that the queue has drained. An idle
  -- observation alone closes a failure episode and permits recovery output.
  episodeAfter : Bool → Cycle → Bool
  episodeAfter previous failed = true
  episodeAfter previous completed = previous
  episodeAfter previous idle = false

  logTransition : Bool → Cycle → Bool
  logTransition false failed = true
  logTransition true idle = true
  logTransition _ _ = false

  completed-preserves-episode : ∀ previous →
    episodeAfter previous completed ≡ previous
  completed-preserves-episode previous = refl

  completed-is-quiet : ∀ previous → logTransition previous completed ≡ false
  completed-is-quiet false = refl
  completed-is-quiet true = refl

  idle-closes-episode : ∀ previous → episodeAfter previous idle ≡ false
  idle-closes-episode previous = refl

  idle-reports-active-episode : ∀ previous →
    logTransition previous idle ≡ previous
  idle-reports-active-episode false = refl
  idle-reports-active-episode true = refl

  reached : ℕ → ℕ → Bool
  reached zero current = true
  reached (suc limit) zero = false
  reached (suc limit) (suc current) = reached limit current

  retryDelay : ℕ → ℕ → ℕ → ℕ → ℕ
  retryDelay threshold failures normal backedOff with reached threshold failures
  ... | true = backedOff
  ... | false = normal

  threshold-switches-to-slow-retry : ∀ normal backedOff →
    retryDelay 3 3 normal backedOff ≡ backedOff
  threshold-switches-to-slow-retry normal backedOff = refl

  retryDeferred : RevisionCheck → Bool
  retryDeferred unchanged = false
  retryDeferred corrected = true
  retryDeferred resolved = false

  unchanged-rejection-is-not-retried : retryDeferred unchanged ≡ false
  unchanged-rejection-is-not-retried = refl

  corrected-revision-can-be-reviewed : retryDeferred corrected ≡ true
  corrected-revision-can-be-reviewed = refl

  failures : Outcome → ℕ → ℕ
  failures success previous = zero
  failures rejected previous = zero
  failures infrastructureFailure previous = suc previous

  rejected-resets-failure-streak : ∀ previous → failures rejected previous ≡ zero
  rejected-resets-failure-streak previous = refl

  infrastructure-failure-increments : ∀ previous →
    failures infrastructureFailure previous ≡ suc previous
  infrastructure-failure-increments previous = refl

module Notification where
  incidentAfter : Bool → Watch.Cycle → Bool
  incidentAfter = Watch.episodeAfter

  completed-batch-keeps-incident : ∀ active →
    incidentAfter active Watch.completed ≡ active
  completed-batch-keeps-incident = Watch.completed-preserves-episode

  idle-clears-incident : ∀ active →
    incidentAfter active Watch.idle ≡ false
  idle-clears-incident = Watch.idle-closes-episode

  data Mail : Set where disabled notNeeded sent exhausted : Mail
                        retryPending : ℕ → Mail
  attempt : ℕ → Bool → Mail
  attempt zero success = exhausted
  attempt (suc fuel) true = sent
  attempt (suc zero) false = exhausted
  attempt (suc (suc fuel)) false = retryPending (suc fuel)

  retry-exhaustion : ∀ success → attempt zero success ≡ exhausted
  retry-exhaustion success = refl
  failed-attempt-never-sent : ∀ fuel → attempt fuel false ≢ sent
  failed-attempt-never-sent zero ()
  failed-attempt-never-sent (suc zero) ()
  failed-attempt-never-sent (suc (suc fuel)) ()
  failure-spends-one : ∀ fuel → attempt (suc (suc fuel)) false ≡ retryPending (suc fuel)
  failure-spends-one fuel = refl

  -- The quantified review state may be any committed review/graph snapshot.
  notify : {ReviewState : Set} → ℕ → Bool → ReviewState × Mail → ReviewState × Mail
  notify fuel accepted (review , previous) = review , attempt fuel accepted
  mail-cannot-undo-review : ∀ {ReviewState : Set} fuel accepted (s : ReviewState × Mail) →
    proj₁ (notify fuel accepted s) ≡ proj₁ s
  mail-cannot-undo-review fuel accepted (review , previous) = refl

  module OAuth where
    -- Tokens and account identities are opaque here. The adapter must perform
    -- exact identity comparison and durable writes before reporting readiness.
    record Cache : Set where
      constructor cache
      field owner refresh : ℕ
            access : Maybe ℕ

    data Refresh : Set where
      unchanged : ℕ → Refresh
      rotated : ℕ → ℕ → Refresh
      denied malformed : Refresh

    data Decision : Set where
      ready authRequired storageFailure : Decision

    -- The first guard means the configured account/client still owns the cache;
    -- the second means the new cache state has been durably stored.
    step : Bool → Refresh → Bool → Cache → Cache × Decision
    step false reply durable old = old , authRequired
    step true denied durable old = old , authRequired
    step true malformed durable old = old , authRequired
    step true (unchanged token) false old = old , storageFailure
    step true (unchanged token) true (cache owner refresh access) =
      cache owner refresh (just token) , ready
    step true (rotated newRefresh token) false old = old , storageFailure
    step true (rotated newRefresh token) true (cache owner refresh access) =
      cache owner newRefresh (just token) , ready

    account-change-refuses : ∀ reply durable old →
      step false reply durable old ≡ (old , authRequired)
    account-change-refuses reply durable old = refl

    no-send-before-durable-write : ∀ reply old →
      proj₂ (step true reply false old) ≢ ready
    no-send-before-durable-write (unchanged token) old ()
    no-send-before-durable-write (rotated refresh token) old ()
    no-send-before-durable-write denied old ()
    no-send-before-durable-write malformed old ()

    rotated-refresh-is-stored : ∀ owner oldRefresh oldAccess newRefresh token →
      proj₁ (step true (rotated newRefresh token) true
        (cache owner oldRefresh oldAccess))
        ≡ cache owner newRefresh (just token)
    rotated-refresh-is-stored owner oldRefresh oldAccess newRefresh token = refl

    rejectAccess : Cache → Cache
    rejectAccess (cache owner refresh access) = cache owner refresh nothing

    rejected-access-keeps-refresh : ∀ owner refresh access →
      rejectAccess (cache owner refresh access) ≡ cache owner refresh nothing
    rejected-access-keeps-refresh owner refresh access = refl
