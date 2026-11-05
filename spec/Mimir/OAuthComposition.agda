{-# OPTIONS --safe #-}
-- Configuration identity, provider requests and cache/SMTP composition.
-- Cryptographic primitives and HTTP/SMTP are dependency boundaries; the
-- material hashed, fields sent, timing, limits and retry policy are explicit.
module Mimir.OAuthComposition where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (toList)
open import Data.Vec using () renaming (toList to vectorList)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Mimir.Text using (Text)
import Mimir.NotificationConfig as Config
import Mimir.OAuthCache as Cache
import Mimir.SMTPAuth as SMTP
import Mimir.StructuredValue as V
import Mimir.StandardLibrary as Library
import Mimir.Effects as Effects

optionalText : Maybe Text → V.Value
optionalText nothing = V.null
optionalText (just value) = V.string value

provider : Config.Provider → Text
provider Config.google = toList "google"
provider Config.microsoft = toList "microsoft"

identityMaterial : Config.Config → Config.OAuth → V.Value
identityMaterial cfg oauth = V.array
  (V.string (provider (Config.OAuth.provider oauth)) ∷ optionalText (Config.Config.host cfg) ∷
   optionalText (Config.Config.username cfg) ∷ V.string (Config.OAuth.clientID oauth) ∷
   optionalText (Config.OAuth.clientSecret oauth) ∷ optionalText (Config.OAuth.tenant oauth) ∷
   optionalText (Config.OAuth.scope oauth) ∷ V.string (Config.OAuth.refreshToken oauth) ∷ [])

-- Mimir chooses the identity material; serialization and hashing are supplied
-- library operations. No collision-freedom or hash implementation is proved.
abstract
  identity : Library.Contract → Config.Config → Config.OAuth → Cache.Bytes
  identity library cfg oauth = vectorList (Library.Contract.sha256 library
    (Library.Contract.compactJSON library (identityMaterial cfg oauth)))

endpoint : Config.OAuth → Cache.AuthError ⊎ Text
endpoint oauth with Config.OAuth.provider oauth
... | Config.google = inj₂ (toList "https://oauth2.googleapis.com/token")
... | Config.microsoft with Config.OAuth.tenant oauth
...   | nothing = inj₁ Cache.needsAttention
...   | just tenant = inj₂ (toList "https://login.microsoftonline.com/" ++ tenant ++ toList "/oauth2/v2.0/token")

secret : Config.OAuth → List (Text × Text)
secret oauth with Config.OAuth.clientSecret oauth
... | nothing = []
... | just value = (toList "client_secret" , value) ∷ []

scope : Config.OAuth → Cache.AuthError ⊎ List (Text × Text)
scope oauth with Config.OAuth.provider oauth
... | Config.google = inj₂ []
... | Config.microsoft with Config.OAuth.scope oauth
...   | nothing = inj₁ Cache.needsAttention
...   | just value = inj₂ ((toList "scope" , value) ∷ [])

record Request : Set where
  constructor request
  field url : Text; form : List (Text × Text); timeoutSeconds : ℕ
        followRedirects : Bool; maximumReply : ℕ

prepare : Config.Config → Config.OAuth → Text → Cache.AuthError ⊎ Request
prepare cfg oauth current with endpoint oauth | scope oauth
... | inj₁ error | _ = inj₁ error
... | _ | inj₁ error = inj₁ error
... | inj₂ url | inj₂ scopes = inj₂ (request url
  ((toList "grant_type" , toList "refresh_token") ∷
   (toList "refresh_token" , current) ∷ (toList "client_id" , Config.OAuth.clientID oauth) ∷
   (secret oauth ++ scopes)) (Config.Config.timeoutSeconds cfg) false 16384)

data Effect : Set where
  clock : Effect
  cache : Cache.Effect → Effect
  http : Request → Effect
  smtp : Cache.Access → Effect

Reply : Effect → Set
Reply clock = ℕ
Reply (cache e) = Cache.Reply e
Reply (http _) = Cache.AuthError ⊎ Cache.Refresh
Reply (smtp _) = SMTP.SMTPReceipt
open Effects.Protocol Effect Reply public

module Configured (library : Library.Contract) (cfg : Config.Config) (oauth : Config.OAuth)
  (clockMaximum : ℕ) where
  boundIdentity = identity library cfg oauth

  cacheProgram : ∀ {A} → Cache.Script A → Script A
  cacheProgram (Cache.done value) = done value
  cacheProgram (Cache.ask Cache.readCache next) = ask (cache Cache.readCache)
    (λ reply → cacheProgram (next reply))
  cacheProgram (Cache.ask (Cache.writeCache value) next) = ask (cache (Cache.writeCache value))
    (λ reply → cacheProgram (next reply))
  cacheProgram (Cache.ask (Cache.refreshToken current) next) with prepare cfg oauth current
  ... | inj₁ error = cacheProgram (next (inj₁ error))
  ... | inj₂ req = ask (http req) (λ reply → cacheProgram (next reply))

  authProgram : ∀ {A} → SMTP.Script A → Script A
  authProgram (SMTP.done value) = done value
  authProgram (SMTP.ask SMTP.acquireCachedOrRefresh next) = ask clock λ now →
    cacheProgram (Cache.getAccess clockMaximum boundIdentity now false (Config.OAuth.refreshToken oauth)) >>=
      λ reply → authProgram (next reply)
  authProgram (SMTP.ask SMTP.acquireForcedRefresh next) = ask clock λ now →
    cacheProgram (Cache.getAccess clockMaximum boundIdentity now true (Config.OAuth.refreshToken oauth)) >>=
      λ reply → authProgram (next reply)
  authProgram (SMTP.ask SMTP.invalidateAccess next) =
    cacheProgram (Cache.invalidate boundIdentity) >>= λ reply → authProgram (next reply)
  authProgram (SMTP.ask (SMTP.deliver token) next) = ask (smtp token)
    (λ reply → authProgram (next reply))

  send : Script SMTP.Result
  send = authProgram SMTP.sendOAuth
