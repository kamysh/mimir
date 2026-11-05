{-# OPTIONS --safe #-}
-- SMTP delivery composes the configured OAuth cache/refresh protocol with
-- the actual message and transport. Cache durability precedes token use.
module Mimir.NotificationMail where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Mimir.Text using (Text)
import Mimir.FloatConversion as Conversion
import Mimir.NotificationConfig as Config
import Mimir.NotificationCodec as Codec
import Mimir.NotificationFileBinding as Files
import Mimir.NotificationStorage as Names
import Mimir.NotificationDelivery as Delivery
import Mimir.OAuthCache as Cache
import Mimir.OAuthComposition as OAuth
import Mimir.OAuthResponseBinding as HTTP
import Mimir.SMTPProtocol as SMTP
import Mimir.SMTPAuth as Auth
import Mimir.JsonCompactRecords as Compact

mailResult : Auth.Result → Delivery.MailReceipt
mailResult Auth.sent = Delivery.accepted
mailResult Auth.retryable = Delivery.retryable
mailResult Auth.authRequired = Delivery.authRequired
mailResult Auth.unavailable = Delivery.unavailable

-- These are standard-library I/O observations, not axioms of successful mail
-- delivery: every failure class remains possible. The message and all Mimir
-- transport options are retained in the operation being observed.
data SMTPObserved : SMTP.Transport → SMTP.Message → SMTP.Receipt → Set where
  result : ∀ transport message reply → SMTPObserved transport message reply

data SMTPCall (cfg : Config.Config) (token : Maybe Text) (message : SMTP.Message) : Auth.SMTPReceipt → Set where
  configurationFailure : SMTP.prepare cfg token ≡ nothing → SMTPCall cfg token message Auth.retryable
  delivered : ∀ transport reply → SMTP.prepare cfg token ≡ just transport → SMTPObserved transport message reply →
    SMTPCall cfg token message (SMTP.classify reply)

module Bound (conversion : Conversion.Contract) (library : Codec.JSONLibrary) (sizeMaximum clockMaximum : ℕ) where
  private
    module F = Files.Bound library sizeMaximum clockMaximum
    module H = HTTP.Decode conversion clockMaximum

  cacheResult : F.F.FS.Error ⊎ Maybe Cache.Cache → Cache.AuthError ⊎ Maybe Cache.Cache
  cacheResult (inj₁ _) = inj₁ Cache.storage
  cacheResult (inj₂ value) = inj₂ value

  data Receipt (held : F.F.L.Locked) (cfg : Config.Config) (message : SMTP.Message) :
    (effect : OAuth.Effect) → OAuth.Reply effect → Set where
    clock : ∀ now → Receipt held cfg message OAuth.clock now
    cacheRead : ∀ reply → F.Read held Names.oauth reply →
      Receipt held cfg message (OAuth.cache Cache.readCache) (cacheResult reply)
    cacheWritten : ∀ value reply → F.Written held Names.oauth value reply →
      Receipt held cfg message (OAuth.cache (Cache.writeCache value)) reply
    refreshed : ∀ request reply → H.Receipt reply → Receipt held cfg message (OAuth.http request) reply
    smtp : ∀ token reply → SMTPCall cfg (just (Cache.Access.value token)) message reply →
      Receipt held cfg message (OAuth.smtp token) reply

  data Runs {A : Set} (held : F.F.L.Locked) (cfg : Config.Config) (message : SMTP.Message) :
    OAuth.Script A → List OAuth.Event → A → Set where
    returned : ∀ value → Runs held cfg message (OAuth.done value) [] value
    replied : ∀ effect next reply events value → Receipt held cfg message effect reply →
      Runs held cfg message (next reply) events value →
      Runs held cfg message (OAuth.ask effect next) ((effect , reply) ∷ events) value

  data Sent (held : F.F.L.Locked) (cfg : Config.Config) (message : SMTP.Message) : Delivery.MailReceipt → Set where
    ordinary : ∀ reply → Config.Config.auth cfg ≢ just Config.oauth2 → SMTPCall cfg nothing message reply →
      Sent held cfg message (mailResult (Auth.withoutOAuth reply))
    oauthMissing : Config.Config.auth cfg ≡ just Config.oauth2 → Config.Config.oauth cfg ≡ nothing →
      Sent held cfg message Delivery.authRequired
    oauth : ∀ settings (supported : Compact.Supported (OAuth.identityMaterial cfg settings)) events result →
      Config.Config.auth cfg ≡ just Config.oauth2 → Config.Config.oauth cfg ≡ just settings →
      Runs held cfg message (OAuth.Configured.send cfg settings supported clockMaximum) events result →
      Sent held cfg message (mailResult result)
