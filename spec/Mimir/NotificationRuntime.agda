{-# OPTIONS --safe #-}
-- Standalone notifier entry points and the shared, incident-keyed outbox.
-- A lock covers the read/reconcile/reserve/send/final-write sequence. Prefixes
-- model interruption; release follows every normally returned outcome.
module Mimir.NotificationRuntime where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_; _++_; map; take; filterᵇ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_; _≤?_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
import Data.Empty
open import Data.String using (toList)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.TextOrder using (_≤Text?_)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.NotificationIncident as I
import Mimir.NotificationDelivery as D
import Mimir.NotificationSchema as Schema
import Mimir.Validation as V
import Mimir.Effects as Effects

Entries = List (Text × I.Incident)
record Outbox : Set where
  constructor outbox
  field version : ℕ; entries : Entries

-- Valid source/key fields contain no controls. JSON tuple escaping therefore
-- consists exactly of quote/backslash escaping, without an arbitrary encoder.
escapeKey : Text → Text
escapeKey [] = []
escapeKey ('"' ∷ xs) = '\\' ∷ '"' ∷ escapeKey xs
escapeKey ('\\' ∷ xs) = '\\' ∷ '\\' ∷ escapeKey xs
escapeKey (x ∷ xs) = x ∷ escapeKey xs

key : I.Event → Text
key e = toList "[\"" ++ escapeKey (I.Event.source e) ++ toList "\",\"" ++
  escapeKey (I.Event.incidentKey e) ++ toList "\"]"

lookup : Text → Entries → Maybe I.Incident
lookup wanted [] = nothing
lookup wanted ((stored , item) ∷ rest) with wanted ≟Text stored
... | yes _ = just item
... | no _ = lookup wanted rest

remove : Text → Entries → Entries
remove wanted [] = []
remove wanted ((stored , item) ∷ rest) with wanted ≟Text stored
... | yes _ = remove wanted rest
... | no _ = (stored , item) ∷ remove wanted rest

insert : Text → I.Incident → Entries → Entries
insert wanted item [] = (wanted , item) ∷ []
insert wanted item ((stored , previous) ∷ rest) with wanted ≤Text? stored
... | yes _ = (wanted , item) ∷ (stored , previous) ∷ rest
... | no _ = (stored , previous) ∷ insert wanted item rest

put : Text → Maybe I.Incident → Outbox → Outbox
put wanted nothing before = record before { entries = remove wanted (Outbox.entries before) }
put wanted (just item) before = record before
  { entries = insert wanted item (remove wanted (Outbox.entries before)) }

changed : I.Incident → I.Event → Bool
changed before e with I.Event.status e
... | I.progress = false
... | I.recovery with I.Incident.activeCode before
...   | nothing = false
...   | just _ = true
changed before e | I.failure code summary with I.Incident.activeCode before
... | nothing = true
... | just active with active ≟Text code
...   | yes _ = false
...   | no _ = true

data Error : Set where invalidEvent unsupportedVersion storage missingIncident : Error
Result = Error ⊎ I.Outcome
data Effect : Set where
  clock : Effect
  lock release readOutbox : Effect
  freshAlert : Effect
  writeOutbox : Outbox → Effect
  build send : I.Alert → Effect

Reply : Effect → Set
Reply clock = ℕ
Reply lock = Bool
Reply release = ⊤
Reply readOutbox = Error ⊎ Maybe Outbox
Reply freshAlert = Text
Reply (writeOutbox _) = D.WriteReceipt
Reply (build _) = D.BuildReceipt
Reply (send _) = D.MailReceipt
open Effects.Protocol Effect Reply public

-- Interpretation of each incident write into the complete outbox preserves
-- all other keys and feeds the updated map to subsequent retry attempts.
deliver : ∀ {A} → Text → Outbox → D.Script A → Script (Outbox × A)
deliver wanted before (D.done result) = done (before , result)
deliver wanted before (D.ask (D.buildMessage a) next) = ask (build a)
  (λ reply → deliver wanted before (next reply))
deliver wanted before (D.ask (D.sendMessage a) next) = ask (send a)
  (λ reply → deliver wanted before (next reply))
deliver wanted before (D.ask (D.saveIncident value) next) = ask (writeOutbox (put wanted value before))
  (λ reply → deliver wanted (put wanted value before) (next reply))

result : D.Result → Result
result (D.completed value) = inj₂ value
result (D.writeFailed _) = inj₁ storage
result D.invalidMessage = inj₁ invalidEvent

attempt : ℕ → Text → Outbox → Script (Outbox × Result)
attempt now wanted before with lookup wanted (Outbox.entries before)
... | nothing = done (before , inj₁ missingIncident)
... | just savedIncident = deliver wanted before (D.attempt savedIncident) >>= λ pair →
  done (proj₁ pair , result (proj₂ pair))

saveThen : Outbox → Script Result → Script Result
saveThen value next = ask (writeOutbox value) λ where
  D.durable → next
  D.refused → done (inj₁ storage)
  D.uncertain → done (inj₁ storage)

saveReconciled : ℕ → I.Event → Outbox → I.Incident → Text → Script Result
saveReconciled now e before savedIncident identity =
  let updated = put (key e) (just (I.reconcile identity now savedIncident e)) before
  in saveThen updated (attempt now (key e) updated >>= λ pair → done (proj₂ pair))

-- Clearing an undelivered incident produces no recovery alert and therefore
-- does not allocate an alert identity. The unused argument is never stored.
reconcileChanged : ℕ → I.Event → Outbox → I.Incident → Script Result
reconcileChanged now e before savedIncident with I.Event.status e | I.Incident.deliveredCode savedIncident
... | I.recovery | nothing = saveReconciled now e before savedIncident []
... | _ | _ = ask freshAlert (saveReconciled now e before savedIncident)

reconcileExisting : ℕ → I.Event → Outbox → I.Incident → Script Result
reconcileExisting now e before savedIncident with changed savedIncident e
... | false = attempt now (key e) before >>= λ pair → done (proj₂ pair)
... | true = reconcileChanged now e before savedIncident

submitLoaded : ℕ → I.Event → Outbox → Script Result
submitLoaded now e before with lookup (key e) (Outbox.entries before)
... | just savedIncident = reconcileExisting now e before savedIncident
... | nothing with I.Event.status e
...   | I.progress = done (inj₂ I.notNeeded)
...   | I.recovery = done (inj₂ I.notNeeded)
...   | I.failure code summary = reconcileExisting now e before
      (I.incident (I.Event.source e) (I.Event.incidentKey e) nothing nothing nothing)

readLoaded : ∀ {A} → (Error → A) → (Outbox → Script A) → Error ⊎ Maybe Outbox → Script A
readLoaded fail next (inj₁ error) = done (fail error)
readLoaded fail next (inj₂ nothing) = next (outbox 1 [])
readLoaded fail next (inj₂ (just before)) with Outbox.version before ≟ 1
... | yes _ = next before
... | no _ = done (fail unsupportedVersion)

read : ∀ {A} → (Error → A) → (Outbox → Script A) → Script A
read fail next = ask readOutbox (readLoaded fail next)

locked : ∀ {A} → A → Script A → Script A
locked failed body = ask lock λ where
  false → done failed
  true → body >>= λ value → ask release (λ _ → done value)

submitAt : Bool → ℕ → I.Event → Script Result
submitAt enabled now e with Schema.checkEvent e
... | V.rejected _ _ = done (inj₁ invalidEvent)
... | V.accepted valid with enabled
...   | false = done (inj₂ I.disabled)
...   | true = locked (inj₁ storage) (read inj₁ (submitLoaded now e))

submit : Bool → I.Event → Script Result
submit enabled e = ask clock (λ now → submitAt enabled now e)

-- Reconciliation stores the complete incident before the worker acknowledges
-- its incoming notificationEvent. Message building and transport belong to a later pass.
alertOutcome : I.Alert → I.Outcome
alertOutcome pendingAlert with I.Alert.lastError pendingAlert
... | nothing = I.retryPending
... | just I.authRequired = I.authRequired
... | just I.unavailable = I.unavailable

deferMail : Script Result → Script Result
deferMail (done result) = done result
deferMail (ask (build pendingAlert) next) = done (inj₂ (alertOutcome pendingAlert))
deferMail (ask (send pendingAlert) next) = done (inj₂ (alertOutcome pendingAlert))
deferMail (ask effect next) = ask effect (λ reply → deferMail (next reply))

accept : Bool → I.Event → Script Result
accept enabled notificationEvent = deferMail (submit enabled notificationEvent)

NoMail : ∀ {A} → Script A → Set
NoMail (done value) = ⊤
NoMail (ask (build _) next) = Data.Empty.⊥
NoMail (ask (send _) next) = Data.Empty.⊥
NoMail (ask effect next) = ∀ reply → NoMail (next reply)

deferredNeedsNoMail : ∀ script → NoMail (deferMail script)
deferredNeedsNoMail (done value) = tt
deferredNeedsNoMail (ask (build _) next) = tt
deferredNeedsNoMail (ask (send _) next) = tt
deferredNeedsNoMail (ask clock next) reply = deferredNeedsNoMail (next reply)
deferredNeedsNoMail (ask lock next) reply = deferredNeedsNoMail (next reply)
deferredNeedsNoMail (ask release next) reply = deferredNeedsNoMail (next reply)
deferredNeedsNoMail (ask readOutbox next) reply = deferredNeedsNoMail (next reply)
deferredNeedsNoMail (ask freshAlert next) reply = deferredNeedsNoMail (next reply)
deferredNeedsNoMail (ask (writeOutbox _) next) reply = deferredNeedsNoMail (next reply)

acceptNeedsNoMail : ∀ enabled notificationEvent → NoMail (accept enabled notificationEvent)
acceptNeedsNoMail enabled notificationEvent = deferredNeedsNoMail (submit enabled notificationEvent)

hasPendingAlert : Text × I.Incident → Bool
hasPendingAlert pair with I.Incident.outbox (proj₂ pair)
... | nothing = false
... | just _ = true

RetryResult = Error ⊎ List (Text × (Text × I.Outcome))
retryKeys : ℕ → List Text → Outbox → Script RetryResult
retryKeys now [] before = done (inj₂ [])
retryKeys now (wanted ∷ rest) before with lookup wanted (Outbox.entries before)
... | nothing = done (inj₁ missingIncident)
... | just savedIncident = attempt now wanted before >>= λ where
  (after , inj₁ error) → done (inj₁ error)
  (after , inj₂ outcome) → retryKeys now rest after >>= λ where
    (inj₁ error) → done (inj₁ error)
    (inj₂ outcomes) → done (inj₂ ((I.Incident.source savedIncident ,
      (I.Incident.incidentKey savedIncident , outcome)) ∷ outcomes))

retryDue : Bool → Script RetryResult
retryDue false = done (inj₂ [])
retryDue true = locked (inj₁ storage) (read inj₁ (λ before → ask clock λ now →
  retryKeys now (map proj₁ (filterᵇ hasPendingAlert (Outbox.entries before))) before))

writeFailureStops : ∀ value next events outcome →
  Runs (saveThen value next) ((writeOutbox value , D.refused) ∷ events) outcome →
  events ≡ [] × outcome ≡ inj₁ storage
writeFailureStops value next events outcome (replied _ _ _ (returned _)) = refl , refl

-- Durable admission has a separate, short-lived file lock. Its consumer keeps
-- the delivery ownership lock, but never the admission lock, during SMTP.
-- Reopening observes this saved list; no process-local mailbox is its owner.
module Admission where
  record Pending : Set where
    constructor pending
    field identity : Text; event : I.Event

  Queue = List Pending

  append : Pending → Queue → Queue
  append item before = before ++ (item ∷ [])

  acknowledge : Text → Queue → Maybe Queue
  acknowledge id [] = nothing
  acknowledge id (item ∷ rest) with id ≟Text Pending.identity item
  ... | yes _ = just rest
  ... | no _ = nothing

  -- An acknowledgement made after a concurrent append removes exactly the
  -- event that was read. All intervening appends survive, in their original order.
  acknowledgePreservesAppends : ∀ head (rest later : Queue) →
    acknowledge (Pending.identity head) ((head ∷ rest) ++ later) ≡ just (rest ++ later)
  acknowledgePreservesAppends head rest later with Pending.identity head ≟Text Pending.identity head
  ... | yes _ = refl
  ... | no different = Data.Empty.⊥-elim (different refl)

  wrongAcknowledgementCannotRemove : ∀ id head rest →
    (id ≡ Pending.identity head → Data.Empty.⊥) →
    acknowledge id (head ∷ rest) ≡ nothing
  wrongAcknowledgementCannotRemove id head rest different with id ≟Text Pending.identity head
  ... | yes same = Data.Empty.⊥-elim (different same)
  ... | no _ = refl
