{-# OPTIONS --safe #-}
-- Lettre is the standard SMTP/MIME implementation boundary. Mimir determines
-- these headers, body, TLS mode, credentials, timeout and error categories.
module Mimir.SMTPProtocol where

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Char using (Char; fromℕ)
open import Data.Fin using (toℕ)
open import Data.List using (List; []; _∷_; _++_; concatMap)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_; _<?_; _+_)
open import Data.Nat.DivMod using (_/_; _%_)
open import Data.String using (toList)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.Bits using (Byte)
import Mimir.StandardLibrary as Library
import Mimir.NotificationIncident as Incident
import Mimir.NotificationConfig as Config
import Mimir.DigestDelivery as Digest
import Mimir.SMTPAuth as Auth

computer : Maybe Text → Text
computer nothing = toList "unknown-host"
computer (just []) = toList "unknown-host"
computer (just name@(_ ∷ _)) = name

-- OS capacity is an external ABI fact. Every successfully decoded, nonempty
-- hostname is preserved; Mimir chooses neither a size quota nor an alphabet.
computerPreservesName : ∀ first rest → computer (just (first ∷ rest)) ≡ first ∷ rest
computerPreservesName first rest = refl

private
  hexDigit : ℕ → Char
  hexDigit n with n <? 10
  ... | yes _ = fromℕ (48 + n)
  ... | no _ = fromℕ (87 + n)

  hexByte : Byte → Text
  hexByte value = hexDigit (toℕ value / 16) ∷ hexDigit (toℕ value % 16) ∷ []

-- Only the syntactically constrained identifier uses this representation.
-- Display headers and body retain the original complete hostname.
computerID : Library.Contract → Text → Text
computerID library host = concatMap hexByte (Library.Contract.encodeUTF8 library host)

record Message : Set where
  constructor message
  field sender : Maybe Text; recipients : List Text
        subject messageID contentType body : Text

details : Incident.Alert → Text
details pendingAlert with Incident.Alert.details pendingAlert
... | nothing = toList "Inspect the local component status for details."
... | just value = value

alertMessage : Config.Config → Text → Incident.Alert → Message
alertMessage cfg host pendingAlert with Incident.Alert.kind pendingAlert
... | Incident.failure = message (Config.Config.fromAddress cfg) (Config.Config.recipients cfg)
  (toList "Mimir [" ++ host ++ toList "] notification: attention needed")
  (toList "<mimir-" ++ Incident.Alert.identity pendingAlert ++ toList "@mimir.local>") (toList "text/plain")
  (toList "Mimir reported a failure.\nComputer: " ++ host ++ toList "\nSource: " ++ Incident.Alert.source pendingAlert ++
   toList "\nCode: " ++ Incident.Alert.code pendingAlert ++ toList "\nSummary: " ++ Incident.Alert.summary pendingAlert ++
   toList "\n\n" ++ details pendingAlert ++ toList "\n")
... | Incident.recovery = message (Config.Config.fromAddress cfg) (Config.Config.recipients cfg)
  (toList "Mimir [" ++ host ++ toList "] notification: recovered")
  (toList "<mimir-" ++ Incident.Alert.identity pendingAlert ++ toList "@mimir.local>") (toList "text/plain")
  (toList "Mimir reported recovery.\nComputer: " ++ host ++ toList "\nSource: " ++ Incident.Alert.source pendingAlert ++
   toList "\n\n" ++ details pendingAlert ++ toList "\n")

digestMessage : Library.Contract → Config.Config → Text → Digest.Digest → Message
digestMessage library cfg host digestValue = message (Config.Config.fromAddress cfg) (Config.Config.recipients cfg)
  (toList "Mimir [" ++ host ++ toList "] daily statistics through " ++ Digest.Digest.throughDay digestValue)
  (toList "<mimir-daily-" ++ Digest.Digest.throughDay digestValue ++ toList "-" ++ computerID library host ++ toList "@mimir.local>")
  (toList "text/plain") (toList "Computer: " ++ host ++ toList "\n" ++ Digest.Digest.body digestValue)

data Credentials : Set where
  anonymous : Credentials
  password xoauth2Only : Text → Text → Credentials

credentials : Config.Config → Maybe Text → Maybe Credentials
credentials cfg token with Config.Config.auth cfg
... | nothing = nothing
... | just Config.anonymous = just anonymous
... | just Config.passwordAuth with Config.Config.username cfg | Config.Config.password cfg
...   | just user | just secret = just (password user secret)
...   | _ | _ = nothing
credentials cfg token | just Config.oauth2 with Config.Config.username cfg | token
... | just user | just value = just (xoauth2Only user value)
... | _ | _ = nothing

record Transport : Set where
  constructor transport
  field host : Text; port : ℕ; tls : Config.TLS; auth : Credentials

prepare : Config.Config → Maybe Text → Maybe Transport
prepare cfg token with Config.Config.host cfg | Config.Config.port cfg | Config.Config.tls cfg | credentials cfg token
... | just host | just port | just tls | just auth = just (transport host port tls auth)
... | _ | _ | _ | _ = nothing

failure : Maybe ℕ → Auth.SMTPReceipt
failure nothing = Auth.retryable
failure (just code) with does (code ≟ 530) ∨ does (code ≟ 534) ∨ does (code ≟ 535)
... | true = Auth.authRejected
... | false = Auth.retryable

data Receipt : Set where
  accepted : Receipt
  unavailable timeout : Receipt
  rejected : Maybe ℕ → Receipt

classify : Receipt → Auth.SMTPReceipt
classify accepted = Auth.accepted
classify unavailable = Auth.retryable
classify timeout = Auth.retryable
classify (rejected status) = failure status
