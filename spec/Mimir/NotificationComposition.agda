{-# OPTIONS --safe #-}
-- Standalone public notification API. No harness/judge dependency is required.
-- One held notification lock covers every outbox/cursor/cache access and send.
module Mimir.NotificationComposition where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (fromℕ)
open import Data.Fin using (toℕ)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.String using (toList)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.StandardLibrary as Conversion
import Mimir.NotificationConfig as Config
import Mimir.NotificationRuntime as N
import Mimir.NotificationIncident as I
import Mimir.NotificationDelivery as D
import Mimir.NotificationCodec as Codec
import Mimir.NotificationFileBinding as Files
import Mimir.NotificationStorage as Names
import Mimir.NotificationMail as Mail
import Mimir.SMTPProtocol as SMTP
import Mimir.DigestDelivery as Digest
import Mimir.UnixPath as Path
import Mimir.UUIDV4 as UUID
import Mimir.Validation as Validation
import Mimir.Effects as Effects

record Notifier : Set where
  constructor notifier
  field config : Config.Config; path : Path.Path
        valid : Config.Valid config
        absolute : Path.absolute path ≡ true

new : Config.Config → Path.Path → Text ⊎ Notifier
new cfg path with Config.validate cfg
... | Validation.rejected failure invalid = inj₁ (Validation.Fault.explanation failure)
... | Validation.accepted valid with Path.absolute path in absolute
...   | false = inj₁ (toList "notification state path must be absolute")
...   | true = inj₂ (notifier cfg path valid absolute)

data Effect : Set where
  notification : N.Effect → Effect
  readCursor : Effect
  digest : Digest.Effect → Effect

Reply : Effect → Set
Reply (notification e) = N.Reply e
Reply readCursor = N.Error ⊎ Digest.Cursor
Reply (digest e) = Digest.Reply e
module P = Effects.Protocol Effect Reply
open P using (Script; done; ask; _>>=_; Event) public

lift : ∀ {A} → N.Script A → Script A
lift (N.done value) = done value
lift (N.ask effect next) = ask (notification effect) (λ reply → lift (next reply))
liftDigest : ∀ {A} → Digest.Script A → Script A
liftDigest (Digest.done value) = done value
liftDigest (Digest.ask effect next) = ask (digest effect) (λ reply → liftDigest (next reply))

module API (service : Notifier) (clockMaximum : ℕ) where
  cfg = Notifier.config service

  submit : I.Event → Script N.Result
  submit notificationEvent = lift (N.submit (Config.Config.enabled cfg) notificationEvent)

  accept : I.Event → Script N.Result
  accept notificationEvent = lift (N.accept (Config.Config.enabled cfg) notificationEvent)

  retry : Script N.RetryResult
  retry = lift (N.retryDue (Config.Config.enabled cfg))

  locked : ∀ {A} → A → Script A → Script A
  locked failure body = ask (notification N.lock) λ where
    false → done failure
    true → body >>= λ value → ask (notification N.release) (λ _ → done value)

  cursor : Script (N.Error ⊎ Digest.Cursor)
  cursor = locked (inj₁ N.storage) (ask readCursor done)

  sendAt : ℕ → Digest.Digest → Script Digest.Result
  sendAt now value with Config.Config.enabled cfg
  ... | false = done Digest.disabled
  ... | true with Digest.digestValid? value
  ...   | no invalid = done Digest.invalidDigest
  ...   | yes valid = locked Digest.storageFailed (ask readCursor λ where
    (inj₁ error) → done Digest.storageFailed
    (inj₂ before) → liftDigest (Digest.send true clockMaximum now before value))

  sendDigest : Digest.Digest → Script Digest.Result
  sendDigest value = ask (notification N.clock) (λ now → sendAt now value)

module Bound (conversion : Conversion.Contract) (library : Codec.JSONLibrary)
  (buildMessage : SMTP.Message → D.BuildReceipt) (sizeMaximum clockMaximum : ℕ)
  (endian : UUID.Endian) (service : Notifier) where
  private
    module F = Files.Bound conversion library sizeMaximum clockMaximum
    module M = Mail.Bound conversion library sizeMaximum clockMaximum
  cfg = Notifier.config service

  -- Built MIME data is retained across durable reservation; sending cannot
  -- silently reconstruct a different message or sample a different hostname.
  data State : Set where
    unlocked : State
    held : F.F.L.Locked → Maybe (Text × SMTP.Message) → State

  outboxResult : F.F.FS.Error ⊎ Maybe N.Outbox → N.Error ⊎ Maybe N.Outbox
  outboxResult (inj₁ _) = inj₁ N.storage
  outboxResult (inj₂ value) = inj₂ value
  cursorResult : F.F.FS.Error ⊎ Maybe Digest.Cursor → N.Error ⊎ Digest.Cursor
  cursorResult (inj₁ _) = inj₁ N.storage
  cursorResult (inj₂ nothing) = inj₂ (Digest.cursor nothing 0 false)
  cursorResult (inj₂ (just value)) = inj₂ value

  built : F.F.L.Locked → Text → SMTP.Message → D.BuildReceipt → State
  built lock host mailMessage D.built = held lock (just (host , mailMessage))
  built lock host mailMessage D.invalid = held lock nothing

  data Receipt : State → (effect : Effect) → Reply effect → State → Set where
    clock : ∀ state now → Receipt state (notification N.clock) now state
    locked : ∀ events lock → F.F.FS.Runs (F.F.acquire (Notifier.path service)) events (inj₂ (just lock)) →
      Receipt unlocked (notification N.lock) true (held lock nothing)
    lockFailed : ∀ events error → F.F.FS.Runs (F.F.acquire (Notifier.path service)) events (inj₁ error) →
      Receipt unlocked (notification N.lock) false unlocked
    lockBusy : ∀ events → F.F.FS.Runs (F.F.acquire (Notifier.path service)) events (inj₂ nothing) →
      Receipt unlocked (notification N.lock) false unlocked
    released : ∀ lock mailMessage events → F.F.FS.Runs (F.F.L.release lock) events tt →
      Receipt (held lock mailMessage) (notification N.release) tt unlocked
    read : ∀ lock mailMessage reply → F.Read lock Names.outbox reply →
      Receipt (held lock mailMessage) (notification N.readOutbox) (outboxResult reply) (held lock mailMessage)
    cursor : ∀ lock mailMessage reply → F.Read lock Names.digest reply →
      Receipt (held lock mailMessage) readCursor (cursorResult reply) (held lock mailMessage)
    written : ∀ lock mailMessage value reply → F.Written lock Names.outbox value reply →
      Receipt (held lock mailMessage) (notification (N.writeOutbox value)) reply (held lock mailMessage)
    cursorWritten : ∀ lock mailMessage value reply → F.Written lock Names.digest value reply →
      Receipt (held lock mailMessage) (digest (Digest.saveCursor value)) reply (held lock mailMessage)
    identity : ∀ lock mailMessage entropy → Receipt (held lock mailMessage) (notification N.freshAlert)
      (Conversion.Contract.formatUUID conversion (UUID.fromRandom conversion endian entropy)) (held lock mailMessage)
    alertBuilt : ∀ lock previous hostname alert →
      Receipt (held lock previous) (notification (N.build alert))
        (buildMessage (SMTP.alertMessage cfg (SMTP.computer hostname) alert))
        (built lock (SMTP.computer hostname) (SMTP.alertMessage cfg (SMTP.computer hostname) alert)
          (buildMessage (SMTP.alertMessage cfg (SMTP.computer hostname) alert)))
    digestBuilt : ∀ lock previous hostname value →
      Receipt (held lock previous) (digest (Digest.buildMessage value))
        (buildMessage (SMTP.digestMessage conversion cfg (SMTP.computer hostname) value))
        (built lock (SMTP.computer hostname) (SMTP.digestMessage conversion cfg (SMTP.computer hostname) value)
          (buildMessage (SMTP.digestMessage conversion cfg (SMTP.computer hostname) value)))
    alertSent : ∀ lock host mailMessage alert reply → mailMessage ≡ SMTP.alertMessage cfg host alert → M.Sent lock cfg mailMessage reply →
      Receipt (held lock (just (host , mailMessage))) (notification (N.send alert)) reply (held lock (just (host , mailMessage)))
    digestSent : ∀ lock host mailMessage value reply → mailMessage ≡ SMTP.digestMessage conversion cfg host value → M.Sent lock cfg mailMessage reply →
      Receipt (held lock (just (host , mailMessage))) (digest (Digest.sendMessage value)) reply (held lock (just (host , mailMessage)))

  data Runs {A : Set} : State → Script A → List Event → State → A → Set where
    returned : ∀ state value → Runs state (done value) [] state value
    replied : ∀ before effect next reply middle events after value → Receipt before effect reply middle →
      Runs middle (next reply) events after value → Runs before (ask effect next) ((effect , reply) ∷ events) after value
