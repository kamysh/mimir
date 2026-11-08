{-# OPTIONS --safe #-}
-- Strict notification TOML fields after standard TOML parsing. Disabled email
-- bypasses semantic validation, not structural/type checking of present fields.
module Mimir.NotificationConfigurationWire where

open import Data.Bool using (false)
open import Data.List using ([]; _∷_)
open import Data.Sum using (_⊎_; inj₂)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Mimir.Validation using (Fault)
open import Mimir.RecordDecoding using (_>>=_; readArray)
open import Mimir.PublicInput
open import Mimir.LearningWire using (recordOf)
import Mimir.StructuredValue as V
import Mimir.NotificationConfig as N
import Mimir.Binary64 as Binary

tls = enum (("starttls" , N.starttls) ∷ ("tls" , N.encrypted) ∷ [])
auth = enum (("password" , N.passwordAuth) ∷ ("oauth2" , N.oauth2) ∷ ("none" , N.anonymous) ∷ [])
provider = enum (("google" , N.google) ∷ ("microsoft" , N.microsoft) ∷ [])

oauth : V.Value → Fault ⊎ N.OAuth
oauth = recordOf ("provider" ∷ "client_id" ∷ "client_secret" ∷ "refresh_token" ∷ "tenant" ∷ "scope" ∷ [])
  (λ fields → required "provider" provider fields >>= λ p → required "client_id" V.asString fields >>= λ id →
    optional "client_secret" V.asString fields >>= λ secret → required "refresh_token" V.asString fields >>= λ refresh →
    optional "tenant" V.asString fields >>= λ tenant → optional "scope" V.asString fields >>= λ scope →
    inj₂ (N.oauthSettings p id refresh secret tenant scope))

module Decode (sizeMaximum : ℕ) where
  decode : V.Value → Fault ⊎ N.Config
  decode = recordOf ("enabled" ∷ "host" ∷ "port" ∷ "tls" ∷ "from" ∷ "to" ∷ "username" ∷ "auth" ∷
    "password" ∷ "oauth" ∷ []) (λ fields →
    defaulted "enabled" false V.asBoolean fields >>= λ enabled → optional "host" V.asString fields >>= λ host →
    optional "port" (unsigned 65535) fields >>= λ port → optional "tls" tls fields >>= λ tls →
    optional "from" V.asString fields >>= λ from → defaulted "to" [] (readArray V.asString) fields >>= λ to →
    optional "username" V.asString fields >>= λ user → optional "auth" auth fields >>= λ auth →
    optional "password" V.asString fields >>= λ password → optional "oauth" oauth fields >>= λ oauth →
    inj₂ (N.config enabled host port tls from to user password auth oauth))
