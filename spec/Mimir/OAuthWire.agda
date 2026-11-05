{-# OPTIONS --safe #-}
-- Concrete OAuth cache and provider response fields after JSON tokenization.
-- Cache objects reject unknown fields; provider replies tolerate them.
module Mimir.OAuthWire where

open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Fin using (Fin; toℕ)
open import Data.Nat using (ℕ; _≤_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.Validation using (Fault)
open import Mimir.StructuredValue
open import Mimir.RecordDecoding
open import Mimir.JsonObjects using (forbid; ignore; rejectKnownRepeated)
open import Mimir.OAuthCache using (Cache; cache; Refresh; refresh; Bytes)
import Mimir.UnsignedWire as UInt
import Mimir.SerdeSequence as Sequence
import Mimir.JudgeStatePrimitives as P

encodeOptional : Maybe Text → Value
encodeOptional nothing = null
encodeOptional (just value) = string value

optionalRoundTrip : ∀ value → nullable asString (just (encodeOptional value)) ≡ inj₂ value
optionalRoundTrip nothing = refl
optionalRoundTrip (just value) = refl

encodeByte : Fin 256 → Value
encodeByte value = unsigned (toℕ value)

byteArrayRoundTrip : ∀ bytes → readArray (UInt.finite 255) (array (map encodeByte bytes)) ≡ inj₂ bytes
byteArrayRoundTrip bytes = elementsRoundTrip encodeByte (UInt.finite 255) (UInt.finiteRoundTrip 255) 0 bytes

cacheNames : List Text
cacheNames = toList "schema_version" ∷ toList "identity_hash" ∷ toList "refresh_token" ∷
  toList "access_token" ∷ toList "expires_at" ∷ []

readCacheFields : ℕ → ℕ → Object.View → Fault ⊎ Cache
readCacheFields schemaMaximum clockMaximum view =
  required (toList "schema_version") (UInt.natural schemaMaximum) view >>= λ schema →
  required (toList "identity_hash") (readArray (UInt.finite 255)) view >>= λ identity →
  required (toList "refresh_token") asString view >>= λ refreshToken →
  optional (toList "access_token") asString view >>= λ accessToken →
  required (toList "expires_at") (UInt.natural clockMaximum) view >>= λ expires →
  inj₂ (cache schema identity refreshToken accessToken expires)

decodeCache : ℕ → ℕ → Value → Fault ⊎ Cache
decodeCache schemaMaximum clockMaximum (array input) = P.recordDecoder fields build (array input)
  where
  fields = P.required (toList "schema_version") ℕ (UInt.natural schemaMaximum) ∷
    P.required (toList "identity_hash") Bytes (readArray (UInt.finite 255)) ∷
    P.required (toList "refresh_token") Text asString ∷ P.optional (toList "access_token") Text asString ∷
    P.required (toList "expires_at") ℕ (UInt.natural clockMaximum) ∷ []
  build : Sequence.Values fields → Cache
  build (Sequence.more version (Sequence.more identity (Sequence.more refreshToken
    (Sequence.more accessToken (Sequence.more expires Sequence.empty))))) = cache version identity refreshToken accessToken expires
decodeCache schemaMaximum clockMaximum raw =
  readRecord forbid rejectKnownRepeated cacheNames (readCacheFields schemaMaximum clockMaximum) raw

encodeCache : Cache → Value
encodeCache c = object
  ((toList "schema_version" , unsigned (Cache.schema c)) ∷
  (toList "identity_hash" , array (map encodeByte (Cache.identity c))) ∷
  (toList "refresh_token" , string (Cache.refresh c)) ∷
  (toList "access_token" , encodeOptional (Cache.access c)) ∷
  (toList "expires_at" , unsigned (Cache.expires c)) ∷ [])

cacheRoundTrip : ∀ schemaMaximum clockMaximum c → Cache.schema c ≤ schemaMaximum → Cache.expires c ≤ clockMaximum →
  decodeCache schemaMaximum clockMaximum (encodeCache c) ≡ inj₂ c
cacheRoundTrip schemaMaximum clockMaximum (cache schema identity refreshToken accessToken expires) schemaBound timeBound
  rewrite UInt.naturalRoundTrip schemaMaximum schema schemaBound |
    byteArrayRoundTrip identity | optionalRoundTrip accessToken |
    UInt.naturalRoundTrip clockMaximum expires timeBound = refl

refreshNames : List Text
refreshNames = toList "access_token" ∷ toList "token_type" ∷ toList "expires_in" ∷ toList "refresh_token" ∷ []

readRefreshFields : ℕ → Object.View → Fault ⊎ Refresh
readRefreshFields clockMaximum view =
  required (toList "access_token") asString view >>= λ accessToken →
  required (toList "token_type") asString view >>= λ tokenType →
  required (toList "expires_in") (UInt.natural clockMaximum) view >>= λ expires →
  optional (toList "refresh_token") asString view >>= λ refreshToken →
  inj₂ (refresh tokenType accessToken refreshToken expires)

decodeRefresh : ℕ → Value → Fault ⊎ Refresh
decodeRefresh clockMaximum = readRecord ignore rejectKnownRepeated refreshNames (readRefreshFields clockMaximum)

encodeRefresh : Refresh → Value
encodeRefresh reply = object
  ((toList "access_token" , string (Refresh.access reply)) ∷
  (toList "token_type" , string (Refresh.tokenType reply)) ∷
  (toList "expires_in" , unsigned (Refresh.expiresIn reply)) ∷
  (toList "refresh_token" , encodeOptional (Refresh.rotated reply)) ∷ [])

refreshRoundTrip : ∀ clockMaximum reply → Refresh.expiresIn reply ≤ clockMaximum →
  decodeRefresh clockMaximum (encodeRefresh reply) ≡ inj₂ reply
refreshRoundTrip clockMaximum (refresh tokenType accessToken refreshToken expires) bound
  rewrite UInt.naturalRoundTrip clockMaximum expires bound | optionalRoundTrip refreshToken = refl
