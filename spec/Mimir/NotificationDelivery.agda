{-# OPTIONS --safe #-}
-- One incident attempt while its outbox lock is held. Message construction,
-- every write receipt and every SMTP outcome are explicit external inputs.
module Mimir.NotificationDelivery where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _<_; _≤_; _≤?_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; Σ; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.NotificationIncident hiding (accepted; Event; event)
open import Mimir.Saturating as Sat using ()
open import Mimir.Effects

data WriteReceipt : Set where durable refused uncertain : WriteReceipt
data MailReceipt : Set where accepted retryable authRequired unavailable : MailReceipt
data BuildReceipt : Set where built invalid : BuildReceipt
data Result : Set where
  completed : Outcome → Result
  writeFailed : WriteReceipt → Result
  invalidMessage : Result

data Effect : Set where
  buildMessage sendMessage : Alert → Effect
  saveIncident : Maybe Incident → Effect

Reply : Effect → Set
Reply (buildMessage _) = BuildReceipt
Reply (sendMessage _) = MailReceipt
Reply (saveIncident _) = WriteReceipt

open Protocol Effect Reply public

record Config : Set where
  constructor config
  field maximumAttempts retrySeconds clockMaximum : ℕ

prune : Incident → Maybe Incident
prune before with Incident.activeCode before | Incident.deliveredCode before | Incident.outbox before
... | nothing | nothing | nothing = nothing
... | _ | _ | _ = just before

save : Maybe Incident → Script Result → Script Result
save value next = ask (saveIncident value) λ where
  durable → next
  refused → done (writeFailed refused)
  uncertain → done (writeFailed uncertain)

reserve : Config → ℕ → Alert → Alert
reserve cfg now a = record a
  { attempts = suc (Alert.attempts a)
  ; nextDue = Sat.add (Config.clockMaximum cfg) now (Config.retrySeconds cfg) }

reserveBounded : ∀ cfg now a → Alert.attempts a < Config.maximumAttempts cfg →
  Alert.attempts (reserve cfg now a) ≤ Config.maximumAttempts cfg
reserveBounded cfg now a proof = proof

reserveClockBounded : ∀ cfg now a → Alert.nextDue (reserve cfg now a) ≤ Config.clockMaximum cfg
reserveClockBounded cfg now a = Sat.bounded (Config.clockMaximum cfg) now (Config.retrySeconds cfg)

withAlert : Incident → Alert → Incident
withAlert before a = record before { outbox = just a }

mailFailure : MailReceipt → Maybe LastError
mailFailure accepted = nothing
mailFailure retryable = nothing
mailFailure authRequired = just authRequired
mailFailure unavailable = just unavailable

failureOutcome : MailReceipt → Outcome
failureOutcome accepted = sent
failureOutcome retryable = retryPending
failureOutcome authRequired = authRequired
failureOutcome unavailable = unavailable

afterFailure : Config → Alert → MailReceipt → Alert × Outcome
afterFailure cfg a reply with Config.maximumAttempts cfg ≤? Alert.attempts a
... | yes _ = record a { delivery = exhausted ; lastError = mailFailure reply } , exhausted
... | no _ = record a { lastError = mailFailure reply } , failureOutcome reply

finishFailure : Config → Incident → Alert → MailReceipt → Script Result
finishFailure cfg before a reply with afterFailure cfg a reply
... | updated , result = save (prune (withAlert before updated)) (done (completed result))

finish : Config → Incident → Alert → MailReceipt → Script Result
finish cfg before a accepted = save (prune (Mimir.NotificationIncident.accepted before a)) (done (completed sent))
finish cfg before a retryable = finishFailure cfg before a retryable
finish cfg before a authRequired = finishFailure cfg before a authRequired
finish cfg before a unavailable = finishFailure cfg before a unavailable

sendReserved : Config → Incident → Alert → Script Result
sendReserved cfg before a = ask (sendMessage a) (finish cfg before a)

eligible : Config → ℕ → Incident → Alert → Script Result
eligible cfg now before a = ask (buildMessage a) λ where
  invalid → done invalidMessage
  built → save (just (withAlert before (reserve cfg now a)))
    (sendReserved cfg (withAlert before (reserve cfg now a)) (reserve cfg now a))

noAlert : Incident → Script Result
noAlert before with Incident.activeCode before | Incident.deliveredCode before
... | nothing | nothing = save nothing (done (completed notNeeded))
... | _ | _ = done (completed notNeeded)

pendingAlert : Config → ℕ → Incident → Alert → Script Result
pendingAlert cfg now before a with Alert.nextDue a ≤? now
... | no _ = done (completed (outcome before))
... | yes _ with Config.maximumAttempts cfg ≤? Alert.attempts a
...   | yes _ = save (just (withAlert before (record a { delivery = exhausted }))) (done (completed exhausted))
...   | no _ = eligible cfg now before a

attempt : Config → ℕ → Incident → Script Result
attempt cfg now before with Incident.outbox before
... | nothing = noAlert before
... | just a with Alert.delivery a
...   | exhausted = done (completed (outcome before))
...   | pending = pendingAlert cfg now before a

-- A write failure ends this invocation. In particular it cannot send mail or
-- report Sent on the strength of an unacknowledged reservation/final write.
refusedHasNoContinuation : ∀ value next events result →
  Runs (save value next) ((saveIncident value , refused) ∷ events) result →
  events ≡ [] × result ≡ writeFailed refused
refusedHasNoContinuation value next events result (replied _ _ _ (returned _)) = refl , refl

uncertainHasNoContinuation : ∀ value next events result →
  Runs (save value next) ((saveIncident value , uncertain) ∷ events) result →
  events ≡ [] × result ≡ writeFailed uncertain
uncertainHasNoContinuation value next events result (replied _ _ _ (returned _)) = refl , refl

-- Exact prefix of every eligible run that reaches SMTP. The alert sent is the
-- one whose incremented attempt and deadline were durably reserved.
data ReachedSMTP (cfg : Config) (now : ℕ) (before : Incident) (a : Alert) : List Event → Set where
  reached : ∀ reply tail → ReachedSMTP cfg now before a
    ((buildMessage a , built) ∷
     (saveIncident (just (withAlert before (reserve cfg now a))) , durable) ∷
     (sendMessage (reserve cfg now a) , reply) ∷ tail)

data ContainsSMTP : List Event → Set where
  here : ∀ a reply tail → ContainsSMTP ((sendMessage a , reply) ∷ tail)
  later : ∀ event {tail} → ContainsSMTP tail → ContainsSMTP (event ∷ tail)

smtpRequiresReservation : ∀ cfg now before a events result →
  Runs (eligible cfg now before a) events result → ContainsSMTP events →
  ReachedSMTP cfg now before a events
smtpRequiresReservation cfg now before a events result
  (replied _ _ invalid (returned _)) (later _ ())
smtpRequiresReservation cfg now before a events result
  (replied _ _ built (replied _ _ refused (returned _))) (later _ (later _ ()))
smtpRequiresReservation cfg now before a events result
  (replied _ _ built (replied _ _ uncertain (returned _))) (later _ (later _ ()))
smtpRequiresReservation cfg now before a events result
  (replied _ _ built (replied _ _ durable (replied _ _ receipt rest))) contains = reached receipt _

saveCompleted : ∀ value result events observed →
  Runs (save value (done (completed result))) events (completed observed) →
  events ≡ (saveIncident value , durable) ∷ [] × observed ≡ result
saveCompleted value result events observed (replied _ _ durable (returned _)) = refl , refl

failureCannotReportSent : ∀ cfg before a receipt →
  (receipt ≡ accepted → ⊥) → ∀ events →
  Runs (finishFailure cfg before a receipt) events (completed sent) → ⊥
failureCannotReportSent cfg before a accepted notAccepted events run = notAccepted refl
failureCannotReportSent cfg before a retryable notAccepted events run
  with Config.maximumAttempts cfg ≤? Alert.attempts a
... | yes _ with proj₂ (saveCompleted _ exhausted events sent run)
...   | ()
failureCannotReportSent cfg before a retryable notAccepted events run | no _
  with proj₂ (saveCompleted _ retryPending events sent run)
... | ()
failureCannotReportSent cfg before a authRequired notAccepted events run
  with Config.maximumAttempts cfg ≤? Alert.attempts a
... | yes _ with proj₂ (saveCompleted _ exhausted events sent run)
...   | ()
failureCannotReportSent cfg before a authRequired notAccepted events run | no _
  with proj₂ (saveCompleted _ authRequired events sent run)
... | ()
failureCannotReportSent cfg before a unavailable notAccepted events run
  with Config.maximumAttempts cfg ≤? Alert.attempts a
... | yes _ with proj₂ (saveCompleted _ exhausted events sent run)
...   | ()
failureCannotReportSent cfg before a unavailable notAccepted events run | no _
  with proj₂ (saveCompleted _ unavailable events sent run)
... | ()

data SentEvidence (cfg : Config) (now : ℕ) (before : Incident) (a : Alert) : List Event → Set where
  sentWithReceipts : SentEvidence cfg now before a
    ((buildMessage a , built) ∷
     (saveIncident (just (withAlert before (reserve cfg now a))) , durable) ∷
     (sendMessage (reserve cfg now a) , accepted) ∷
     (saveIncident (prune (Mimir.NotificationIncident.accepted
       (withAlert before (reserve cfg now a)) (reserve cfg now a))) , durable) ∷ [])

sentRequiresBothReceipts : ∀ cfg now before a events →
  Runs (eligible cfg now before a) events (completed sent) →
  SentEvidence cfg now before a events
sentRequiresBothReceipts cfg now before a events
  (replied _ _ built (replied _ _ durable (replied _ _ accepted
    (replied _ _ durable (returned _))))) = sentWithReceipts
sentRequiresBothReceipts cfg now before a events
  (replied _ _ built (replied _ _ durable (replied _ _ retryable rest))) =
  ⊥-elim (failureCannotReportSent cfg (withAlert before (reserve cfg now a)) (reserve cfg now a) retryable (λ ()) _ rest)
sentRequiresBothReceipts cfg now before a events
  (replied _ _ built (replied _ _ durable (replied _ _ authRequired rest))) =
  ⊥-elim (failureCannotReportSent cfg (withAlert before (reserve cfg now a)) (reserve cfg now a) authRequired (λ ()) _ rest)
sentRequiresBothReceipts cfg now before a events
  (replied _ _ built (replied _ _ durable (replied _ _ unavailable rest))) =
  ⊥-elim (failureCannotReportSent cfg (withAlert before (reserve cfg now a)) (reserve cfg now a) unavailable (λ ()) _ rest)
