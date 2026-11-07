{-# OPTIONS --safe #-}
-- Finalization requires concrete diagnostic, incident and status persistence
-- and either inline delivery or admission to the owned worker. Queued receipts
-- cannot contain a synchronous notification submission.
module Mimir.JudgeFinalizationComposition where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Mimir.Text using (Text)
import Mimir.StandardLibrary as Conversion
import Mimir.PublicEncoding as Encoding
import Mimir.NotificationConfig as Email
import Mimir.NotificationDelivery as Delivery
import Mimir.NotificationRuntime as Notifier
import Mimir.JudgeNotification as Notification
import Mimir.JudgeFinalization as Finalization
import Mimir.JudgeStateOperations as State
import Mimir.JudgePersistence as Names
import Mimir.UnixPath as Path
import Mimir.UUIDV4 as UUID
import Mimir.NotificationComposition as CompleteNotifier
import Mimir.NotificationCodec as Codec
import Mimir.NotificationIncident as Incident
import Mimir.SMTPProtocol as SMTP
open import Relation.Binary.PropositionalEquality using (_≡_)

module Bound (conversion : Conversion.Contract) (format : Encoding.Formatting)
  (localTime : ℕ → Text) (sizeMaximum clockMaximum : ℕ) (endian : UUID.Endian)
  (path : Path.Path) (email : Email.Config) (project : Maybe Text)
  (json : Codec.JSONLibrary) (buildMessage : SMTP.Message → Delivery.BuildReceipt) where
  private
    module S = State.Bound conversion sizeMaximum endian path
    module N = Notification.Run format localTime email path project
    module Complete service = CompleteNotifier.Bound conversion json buildMessage sizeMaximum clockMaximum endian service
  delivery = Delivery.config (Email.Config.maximumAttempts email) (Email.Config.retrySeconds email) clockMaximum

  data NotificationReceipt : (effect : Notification.Effect) → Notification.Reply effect → Set where
    incident : ∀ reply → S.ReadReceipt Names.failure reply → NotificationReceipt Notification.readFailure reply
    submitted : ∀ event service events reply → CompleteNotifier.new email path ≡ inj₂ service →
      Complete.Runs service (Complete.unlocked {service = service})
        (CompleteNotifier.API.submit service clockMaximum event) events (Complete.unlocked {service = service}) reply →
      NotificationReceipt (Notification.submit event) reply

  record Notified (report : State.R.Report) (reply : Text ⊎ Text) : Set where
    field events : List Notification.Event
          execution : Notification.Runs (N.notify report) events reply
          receipts : All (λ { (effect , value) → NotificationReceipt effect value }) events

  data QueueReply (event : Incident.Event) : Text ⊎ ⊤ → Set where
    accepted : ∀ before after → Finalization.WorkerQueue.Accepted (Finalization.alertJob email path event) before after →
      QueueReply event (inj₂ tt)
    closed : ∀ detail → QueueReply event (inj₁ detail)

  QueueOnlyReceipt : (effect : Notification.Effect) → Notification.Reply effect → Set
  QueueOnlyReceipt Notification.readFailure reply = S.ReadReceipt Names.failure reply
  QueueOnlyReceipt (Notification.enqueue queuedEvent) reply = QueueReply queuedEvent reply
  QueueOnlyReceipt (Notification.submit queuedEvent) reply = ⊥

  record Queued (report : State.R.Report) (reply : Text ⊎ Text) : Set where
    field events : List Notification.Event
          execution : Notification.Runs (N.queue report) events reply
          receipts : All (λ { (effect , value) → QueueOnlyReceipt effect value }) events

  Receipt : (effect : Finalization.Effect) → Finalization.Reply effect → Set
  Receipt Finalization.clock reply = ⊤
  Receipt (Finalization.finishTrace id report) reply = S.Finished id report reply
  Receipt (Finalization.recordIncident report) reply = S.IncidentExecution report reply
  Receipt (Finalization.writeStatus report) reply = S.Written Names.status report reply
  Receipt (Finalization.notify report) reply = Notified report reply
  Receipt (Finalization.enqueueNotification report) reply = Queued report reply

  data Runs {A : Set} : Finalization.E.Script A → List Finalization.E.Event → A → Set where
    returned : ∀ value → Runs (Finalization.E.done value) [] value
    replied : ∀ effect continuation reply events value → Receipt effect reply →
      Runs (continuation reply) events value →
      Runs (Finalization.E.ask effect continuation) ((effect , reply) ∷ events) value
