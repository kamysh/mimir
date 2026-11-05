{-# OPTIONS --safe #-}
-- Application-owned file schemas and serialization data. JSON lexical parsing
-- and formatting are standard library boundaries. The parser boundary is an
-- ordered token tree: it must retain repeated keys, as direct Serde visitors
-- do; it is not serde_json::Value's last-key-wins normalization.
module Mimir.NotificationCodec where

open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_)
open import Data.String using (toList)
open import Mimir.Text using (Text)
open import Mimir.Bits using (Byte)
open import Mimir.RecordDecoding using (_>>=_)
import Mimir.StructuredValue as V
import Mimir.Validation as Validation
import Mimir.NotificationIncident as I
import Mimir.NotificationRuntime as N
import Mimir.NotificationWire as Wire
import Mimir.NotificationStorage as Storage
import Mimir.OAuthCache as OAuth
import Mimir.OAuthWire as OAuthWire
import Mimir.DigestDelivery as Digest

record JSONLibrary : Set where
  field orderedTokens : List Byte → Validation.Fault ⊎ V.Value
        pretty : V.Value → Text ⊎ List Byte

optional : ∀ {A : Set} → (A → V.Value) → Maybe A → V.Value
optional encode nothing = V.null
optional encode (just value) = encode value

kind : I.Kind → V.Value
kind I.failure = V.string (toList "failure")
kind I.recovery = V.string (toList "recovery")
delivery : I.Delivery → V.Value
delivery I.pending = V.string (toList "pending")
delivery I.exhausted = V.string (toList "exhausted")
lastError : I.LastError → V.Value
lastError I.authRequired = V.string (toList "auth_required")
lastError I.unavailable = V.string (toList "unavailable")

alert : I.Alert → V.Value
alert value = V.object
  ((toList "id" , V.string (I.Alert.identity value)) ∷ (toList "kind" , kind (I.Alert.kind value)) ∷
   (toList "source" , V.string (I.Alert.source value)) ∷ (toList "code" , V.string (I.Alert.code value)) ∷
   (toList "summary" , V.string (I.Alert.summary value)) ∷ (toList "details" , optional V.string (I.Alert.details value)) ∷
   (toList "attempts" , V.unsigned (I.Alert.attempts value)) ∷ (toList "next_due" , V.unsigned (I.Alert.nextDue value)) ∷
   (toList "delivery" , delivery (I.Alert.delivery value)) ∷ (toList "last_error" , optional lastError (I.Alert.lastError value)) ∷ [])

incident : I.Incident → V.Value
incident value = V.object
  ((toList "source" , V.string (I.Incident.source value)) ∷ (toList "incident_key" , V.string (I.Incident.incidentKey value)) ∷
   (toList "active_code" , optional V.string (I.Incident.activeCode value)) ∷
   (toList "delivered_code" , optional V.string (I.Incident.deliveredCode value)) ∷
   (toList "outbox" , optional alert (I.Incident.outbox value)) ∷ [])

outbox : N.Outbox → V.Value
outbox value = V.object ((toList "schema_version" , V.unsigned (N.Outbox.version value)) ∷
  (toList "incidents" , V.object (map (λ { (key , item) → key , incident item }) (N.Outbox.entries value))) ∷ [])

cursor : Digest.Cursor → V.Value
cursor value = V.object
  ((toList "through_day" , optional V.string (Digest.Cursor.throughDay value)) ∷
   (toList "next_due" , V.unsigned (Digest.Cursor.nextDue value)) ∷
   (toList "last_attempt_failed" , V.boolean (Digest.Cursor.lastAttemptFailed value)) ∷ [])

Value : Storage.Name → Set
Value Storage.outbox = N.Outbox
Value Storage.oauth = OAuth.Cache
Value Storage.digest = Digest.Cursor

encode : (name : Storage.Name) → Value name → V.Value
encode Storage.outbox = outbox
encode Storage.oauth = OAuthWire.encodeCache
encode Storage.digest = cursor

module Decode (library : JSONLibrary) (sizeMaximum clockMaximum : ℕ) where
  private module D = Wire.Decode sizeMaximum clockMaximum
  value : (name : Storage.Name) → V.Value → Validation.Fault ⊎ Value name
  value Storage.outbox = D.outbox
  value Storage.oauth = OAuthWire.decodeCache 4294967295 clockMaximum
  value Storage.digest = D.cursor

  bytes : (name : Storage.Name) → List Byte → Validation.Fault ⊎ Value name
  bytes name input = JSONLibrary.orderedTokens library input >>= value name
