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

prune : Incident → Maybe Incident
prune before with Incident.activeCode before | Incident.deliveredCode before | Incident.outbox before
... | nothing | nothing | nothing = nothing
... | _ | _ | _ = just before

save : Maybe Incident → Script Result → Script Result
save value next = ask (saveIncident value) λ where
  durable → next
  refused → done (writeFailed refused)
  uncertain → done (writeFailed uncertain)

reserve : Alert → Alert
reserve a = record a { attempts = suc (Alert.attempts a) ; nextDue = 0 ; delivery = pending }

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

afterFailure : Alert → MailReceipt → Alert × Outcome
afterFailure a reply = record a { delivery = pending ; lastError = mailFailure reply } , failureOutcome reply

finishFailure : Incident → Alert → MailReceipt → Script Result
finishFailure before a reply with afterFailure a reply
... | updated , result = save (prune (withAlert before updated)) (done (completed result))

finish : Incident → Alert → MailReceipt → Script Result
finish before a accepted = save (prune (Mimir.NotificationIncident.accepted before a)) (done (completed sent))
finish before a retryable = finishFailure before a retryable
finish before a authRequired = finishFailure before a authRequired
finish before a unavailable = finishFailure before a unavailable

sendReserved : Incident → Alert → Script Result
sendReserved before a = ask (sendMessage a) (finish before a)

eligible : Incident → Alert → Script Result
eligible before a = ask (buildMessage a) λ where
  invalid → done invalidMessage
  built → save (just (withAlert before (reserve a)))
    (sendReserved (withAlert before (reserve a)) (reserve a))

noAlert : Incident → Script Result
noAlert before with Incident.activeCode before | Incident.deliveredCode before
... | nothing | nothing = save nothing (done (completed notNeeded))
... | _ | _ = done (completed notNeeded)

attempt : Incident → Script Result
attempt before with Incident.outbox before
... | nothing = noAlert before
... | just a = eligible before a

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
-- one whose pending state was durably reserved, without a retry deadline.
data ReachedSMTP (before : Incident) (a : Alert) : List Event → Set where
  reached : ∀ reply tail → ReachedSMTP before a
    ((buildMessage a , built) ∷
     (saveIncident (just (withAlert before (reserve a))) , durable) ∷
     (sendMessage (reserve a) , reply) ∷ tail)

data ContainsSMTP : List Event → Set where
  here : ∀ a reply tail → ContainsSMTP ((sendMessage a , reply) ∷ tail)
  later : ∀ event {tail} → ContainsSMTP tail → ContainsSMTP (event ∷ tail)

smtpRequiresReservation : ∀ before a events result →
  Runs (eligible before a) events result → ContainsSMTP events →
  ReachedSMTP before a events
smtpRequiresReservation before a events result
  (replied _ _ invalid (returned _)) (later _ ())
smtpRequiresReservation before a events result
  (replied _ _ built (replied _ _ refused (returned _))) (later _ (later _ ()))
smtpRequiresReservation before a events result
  (replied _ _ built (replied _ _ uncertain (returned _))) (later _ (later _ ()))
smtpRequiresReservation before a events result
  (replied _ _ built (replied _ _ durable (replied _ _ receipt rest))) contains = reached receipt _

saveCompleted : ∀ value result events observed →
  Runs (save value (done (completed result))) events (completed observed) →
  events ≡ (saveIncident value , durable) ∷ [] × observed ≡ result
saveCompleted value result events observed (replied _ _ durable (returned _)) = refl , refl

failureCannotReportSent : ∀ before a receipt →
  (receipt ≡ accepted → ⊥) → ∀ events →
  Runs (finishFailure before a receipt) events (completed sent) → ⊥
failureCannotReportSent before a accepted notAccepted events run = notAccepted refl
failureCannotReportSent before a retryable notAccepted events run
  with proj₂ (saveCompleted _ retryPending events sent run)
... | ()
failureCannotReportSent before a authRequired notAccepted events run
  with proj₂ (saveCompleted _ authRequired events sent run)
... | ()
failureCannotReportSent before a unavailable notAccepted events run
  with proj₂ (saveCompleted _ unavailable events sent run)
... | ()

data SentEvidence (before : Incident) (a : Alert) : List Event → Set where
  sentWithReceipts : SentEvidence before a
    ((buildMessage a , built) ∷
     (saveIncident (just (withAlert before (reserve a))) , durable) ∷
     (sendMessage (reserve a) , accepted) ∷
     (saveIncident (prune (Mimir.NotificationIncident.accepted
       (withAlert before (reserve a)) (reserve a))) , durable) ∷ [])

sentRequiresBothReceipts : ∀ before a events →
  Runs (eligible before a) events (completed sent) →
  SentEvidence before a events
sentRequiresBothReceipts before a events
  (replied _ _ built (replied _ _ durable (replied _ _ accepted
    (replied _ _ durable (returned _))))) = sentWithReceipts
sentRequiresBothReceipts before a events
  (replied _ _ built (replied _ _ durable (replied _ _ retryable rest))) =
  ⊥-elim (failureCannotReportSent (withAlert before (reserve a)) (reserve a) retryable (λ ()) _ rest)
sentRequiresBothReceipts before a events
  (replied _ _ built (replied _ _ durable (replied _ _ authRequired rest))) =
  ⊥-elim (failureCannotReportSent (withAlert before (reserve a)) (reserve a) authRequired (λ ()) _ rest)
sentRequiresBothReceipts before a events
  (replied _ _ built (replied _ _ durable (replied _ _ unavailable rest))) =
  ⊥-elim (failureCannotReportSent (withAlert before (reserve a)) (reserve a) unavailable (λ ()) _ rest)
