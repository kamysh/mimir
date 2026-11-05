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

data Error : Set where invalidEvent invalidLimit unsupportedVersion storage missingIncident : Error
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

attempt : D.Config → ℕ → Text → Outbox → Script (Outbox × Result)
attempt cfg now wanted before with lookup wanted (Outbox.entries before)
... | nothing = done (before , inj₁ missingIncident)
... | just savedIncident = deliver wanted before (D.attempt cfg now savedIncident) >>= λ pair →
  done (proj₁ pair , result (proj₂ pair))

saveThen : Outbox → Script Result → Script Result
saveThen value next = ask (writeOutbox value) λ where
  D.durable → next
  D.refused → done (inj₁ storage)
  D.uncertain → done (inj₁ storage)

saveReconciled : D.Config → ℕ → I.Event → Outbox → I.Incident → Text → Script Result
saveReconciled cfg now e before savedIncident identity =
  let updated = put (key e) (just (I.reconcile identity now savedIncident e)) before
  in saveThen updated (attempt cfg now (key e) updated >>= λ pair → done (proj₂ pair))

-- Clearing an undelivered incident produces no recovery alert and therefore
-- does not allocate an alert identity. The unused argument is never stored.
reconcileChanged : D.Config → ℕ → I.Event → Outbox → I.Incident → Script Result
reconcileChanged cfg now e before savedIncident with I.Event.status e | I.Incident.deliveredCode savedIncident
... | I.recovery | nothing = saveReconciled cfg now e before savedIncident []
... | _ | _ = ask freshAlert (saveReconciled cfg now e before savedIncident)

reconcileExisting : D.Config → ℕ → I.Event → Outbox → I.Incident → Script Result
reconcileExisting cfg now e before savedIncident with changed savedIncident e
... | false = attempt cfg now (key e) before >>= λ pair → done (proj₂ pair)
... | true = reconcileChanged cfg now e before savedIncident

submitLoaded : D.Config → ℕ → I.Event → Outbox → Script Result
submitLoaded cfg now e before with lookup (key e) (Outbox.entries before)
... | just savedIncident = reconcileExisting cfg now e before savedIncident
... | nothing with I.Event.status e
...   | I.progress = done (inj₂ I.notNeeded)
...   | I.recovery = done (inj₂ I.notNeeded)
...   | I.failure code summary = reconcileExisting cfg now e before
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

submitAt : Bool → D.Config → ℕ → I.Event → Script Result
submitAt enabled cfg now e with Schema.checkEvent e
... | V.rejected _ _ = done (inj₁ invalidEvent)
... | V.accepted valid with enabled
...   | false = done (inj₂ I.disabled)
...   | true = locked (inj₁ storage) (read inj₁ (submitLoaded cfg now e))

submit : Bool → D.Config → I.Event → Script Result
submit enabled cfg e = ask clock (λ now → submitAt enabled cfg now e)

due : ℕ → Text × I.Incident → Bool
due now pair with I.Incident.outbox (proj₂ pair)
... | nothing = false
... | just pendingAlert with I.Alert.delivery pendingAlert
...   | I.exhausted = false
...   | I.pending = does (I.Alert.nextDue pendingAlert ≤? now)

RetryResult = Error ⊎ List (Text × (Text × I.Outcome))
retryKeys : D.Config → ℕ → List Text → Outbox → Script RetryResult
retryKeys cfg now [] before = done (inj₂ [])
retryKeys cfg now (wanted ∷ rest) before with lookup wanted (Outbox.entries before)
... | nothing = done (inj₁ missingIncident)
... | just savedIncident = attempt cfg now wanted before >>= λ where
  (after , inj₁ error) → done (inj₁ error)
  (after , inj₂ outcome) → retryKeys cfg now rest after >>= λ where
    (inj₁ error) → done (inj₁ error)
    (inj₂ outcomes) → done (inj₂ ((I.Incident.source savedIncident ,
      (I.Incident.incidentKey savedIncident , outcome)) ∷ outcomes))

retryDue : Bool → D.Config → ℕ → Script RetryResult
retryDue enabled cfg limit with does (1 ≤? limit) ∧ does (limit ≤? 20)
... | false = done (inj₁ invalidLimit)
... | true with enabled
...   | false = done (inj₂ [])
...   | true = locked (inj₁ storage) (read inj₁ (λ before → ask clock λ now →
    retryKeys cfg now (take limit (map proj₁ (filterᵇ (due now) (Outbox.entries before)))) before))

writeFailureStops : ∀ value next events outcome →
  Runs (saveThen value next) ((writeOutbox value , D.refused) ∷ events) outcome →
  events ≡ [] × outcome ≡ inj₁ storage
writeFailureStops value next events outcome (replied _ _ _ (returned _)) = refl , refl
