{-# OPTIONS --safe #-}
-- Cache admission and refresh persistence. HTTP framing, identity hashing and
-- configuration decoding feed this protocol; their validity is not assumed
-- merely because a cache or refresh response could be deserialized.
module Mimir.OAuthCache where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.List.Properties using (≡-dec)
open import Data.Fin using (Fin)
import Data.Fin.Properties as Fin
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤_; _≤?_; _<_; _<?_; _≟_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable.Core using (_×-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.CharacterRules using (TokenValid; tokenValid?; Bearer; bearer?)
import Mimir.Saturating as Sat
open import Mimir.Effects
open import Mimir.NotificationDelivery using (WriteReceipt; durable; refused; uncertain)

Bytes = List (Fin 256)
Token = TokenValid 8192

record Cache : Set where
  constructor cache
  field schema : ℕ; identity : Bytes; refresh : Text; access : Maybe Text; expires : ℕ

OptionalToken : Maybe Text → Set
OptionalToken nothing = ⊤
OptionalToken (just text) = Token text

optionalToken? : ∀ value → Dec (OptionalToken value)
optionalToken? nothing = yes tt
optionalToken? (just text) = tokenValid? 8192 text

IdentityValid : Bytes → Cache → Set
IdentityValid identity c = Cache.schema c ≡ 1 × Cache.identity c ≡ identity

identityValid? : ∀ identity c → Dec (IdentityValid identity c)
identityValid? identity c = (Cache.schema c ≟ 1) ×-dec (≡-dec Fin._≟_ (Cache.identity c) identity)

CacheValid : Bytes → Cache → Set
CacheValid identity c = IdentityValid identity c ×
  (Token (Cache.refresh c) × OptionalToken (Cache.access c))

cacheValid? : ∀ identity c → Dec (CacheValid identity c)
cacheValid? identity c = identityValid? identity c ×-dec
  (tokenValid? 8192 (Cache.refresh c) ×-dec optionalToken? (Cache.access c))

record Refresh : Set where
  constructor refresh
  field tokenType access : Text; rotated : Maybe Text; expiresIn : ℕ

RefreshValid : Refresh → Set
RefreshValid reply = Bearer (Refresh.tokenType reply) × (Token (Refresh.access reply) ×
  (OptionalToken (Refresh.rotated reply) × 0 < Refresh.expiresIn reply))

refreshValid? : ∀ reply → Dec (RefreshValid reply)
refreshValid? reply = bearer? (Refresh.tokenType reply) ×-dec (tokenValid? 8192 (Refresh.access reply) ×-dec
  (optionalToken? (Refresh.rotated reply) ×-dec (0 <? Refresh.expiresIn reply)))

chooseRefresh : Text → Maybe Text → Text
chooseRefresh previous nothing = previous
chooseRefresh previous (just rotated) = rotated

data AuthError : Set where retryable needsAttention storage : AuthError
record Access : Set where
  constructor access
  field value : Text; cached : Bool

data Effect : Set where
  readCache : Effect
  refreshToken : Text → Effect
  writeCache : Cache → Effect

Reply : Effect → Set
Reply readCache = AuthError ⊎ Maybe Cache
Reply (refreshToken _) = AuthError ⊎ Refresh
Reply (writeCache _) = WriteReceipt

open Protocol Effect Reply public
Result = AuthError ⊎ Access

newCache : ℕ → Bytes → ℕ → Text → Refresh → Cache
newCache maximum identity now previous reply = cache 1 identity
  (chooseRefresh previous (Refresh.rotated reply)) (just (Refresh.access reply))
  (Sat.add maximum now (Refresh.expiresIn reply))

newCacheValid : ∀ maximum identity now previous reply → Token previous → RefreshValid reply →
  CacheValid identity (newCache maximum identity now previous reply)
newCacheValid maximum identity now previous (refresh kind value nothing duration) old (bearer , token , tt , positive) =
  (refl , refl) , old , token
newCacheValid maximum identity now previous (refresh kind value (just rotated) duration) old (bearer , token , rotatedToken , positive) =
  (refl , refl) , rotatedToken , token

newExpiryBounded : ∀ maximum identity now previous reply →
  Cache.expires (newCache maximum identity now previous reply) ≤ maximum
newExpiryBounded maximum identity now previous reply = Sat.bounded maximum now (Refresh.expiresIn reply)

publish : Cache → Text → Script Result
publish c value = ask (writeCache c) λ where
  durable → done (inj₂ (access value false))
  refused → done (inj₁ storage)
  uncertain → done (inj₁ storage)

processRefresh : ℕ → Bytes → ℕ → Text → AuthError ⊎ Refresh → Script Result
processRefresh maximum identity now previous (inj₁ failure) = done (inj₁ failure)
processRefresh maximum identity now previous (inj₂ reply) with refreshValid? reply
... | no _ = done (inj₁ needsAttention)
... | yes valid = publish (newCache maximum identity now previous reply) (Refresh.access reply)

renew : ℕ → Bytes → ℕ → Text → Script Result
renew maximum identity now previous = ask (refreshToken previous) (processRefresh maximum identity now previous)

fromValidCache : ℕ → Bytes → ℕ → Bool → Cache → Script Result
fromValidCache maximum identity now true c = renew maximum identity now (Cache.refresh c)
fromValidCache maximum identity now false c with Sat.add maximum now 60 <? Cache.expires c
... | no _ = renew maximum identity now (Cache.refresh c)
... | yes _ with Cache.access c
...   | nothing = renew maximum identity now (Cache.refresh c)
...   | just value = done (inj₂ (access value true))

processCache : ℕ → Bytes → ℕ → Bool → Text → AuthError ⊎ Maybe Cache → Script Result
processCache maximum identity now force configured (inj₁ failure) = done (inj₁ storage)
processCache maximum identity now force configured (inj₂ nothing) = renew maximum identity now configured
processCache maximum identity now force configured (inj₂ (just c)) with cacheValid? identity c
... | no _ = done (inj₁ needsAttention)
... | yes valid = fromValidCache maximum identity now force c

getAccess : ℕ → Bytes → ℕ → Bool → Text → Script Result
getAccess maximum identity now force configured = ask readCache (processCache maximum identity now force configured)

invalidateLoaded : Bytes → AuthError ⊎ Maybe Cache → Script (AuthError ⊎ ⊤)
invalidateLoaded identity (inj₁ failure) = done (inj₁ storage)
invalidateLoaded identity (inj₂ nothing) = done (inj₁ needsAttention)
invalidateLoaded identity (inj₂ (just c)) with identityValid? identity c
... | no _ = done (inj₁ needsAttention)
... | yes valid = ask (writeCache (record c { access = nothing ; expires = 0 })) λ where
  durable → done (inj₂ tt)
  refused → done (inj₁ storage)
  uncertain → done (inj₁ storage)

invalidate : Bytes → Script (AuthError ⊎ ⊤)
invalidate identity = ask readCache (invalidateLoaded identity)

freshAccessRequiresDurableWrite : ∀ c value events observed →
  Runs (publish c value) events (inj₂ observed) →
  events ≡ (writeCache c , durable) ∷ [] × observed ≡ access value false
freshAccessRequiresDurableWrite c value events observed (replied _ _ durable (returned _)) = refl , refl

rotationRetained : ∀ maximum identity now previous kind value rotated duration →
  Cache.refresh (newCache maximum identity now previous (refresh kind value (just rotated) duration)) ≡ rotated
rotationRetained maximum identity now previous kind value rotated duration = refl

absentRotationPreservesRefresh : ∀ maximum identity now previous kind value duration →
  Cache.refresh (newCache maximum identity now previous (refresh kind value nothing duration)) ≡ previous
absentRotationPreservesRefresh maximum identity now previous kind value duration = refl

forcedRefreshCannotReuseAccess : ∀ maximum identity now c →
  fromValidCache maximum identity now true c ≡ renew maximum identity now (Cache.refresh c)
forcedRefreshCannotReuseAccess maximum identity now c = refl

invalidCacheStops : ∀ maximum identity now force configured c →
  (CacheValid identity c → ⊥) →
  processCache maximum identity now force configured (inj₂ (just c)) ≡ done (inj₁ needsAttention)
invalidCacheStops maximum identity now force configured c invalid with cacheValid? identity c
... | no _ = refl
... | yes valid = ⊥-elim (invalid valid)
