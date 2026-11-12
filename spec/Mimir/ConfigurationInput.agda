{-# OPTIONS --safe #-}
module Mimir.ConfigurationInput where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; fromList; _≟_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.Unsigned as U
open import Mimir.ConfigurationValues

data Key : Set where
  hostKey portKey databaseKey userKey passwordKey passfileKey modeKey rootKey
    certificateKey clientKeyKey backendKey modelKey apiKeyKey batchKey cacheKey : Key

keys : List (String × Key)
keys = ("host" , hostKey) ∷ ("port" , portKey) ∷ ("dbname" , databaseKey) ∷
  ("user" , userKey) ∷ ("password" , passwordKey) ∷ ("pgpassfile" , passfileKey) ∷
  ("ssl_mode" , modeKey) ∷ ("ssl_root_cert" , rootKey) ∷
  ("ssl_client_cert" , certificateKey) ∷ ("ssl_client_key" , clientKeyKey) ∷
  ("backend" , backendKey) ∷ ("model" , modelKey) ∷ ("api_key" , apiKeyKey) ∷
  ("batch_size" , batchKey) ∷ ("cache_dir" , cacheKey) ∷ []

lookup : ∀ {A : Set} → String → List (String × A) → Maybe A
lookup key [] = nothing
lookup key ((name , value) ∷ rest) with key ≟ name
... | yes _ = just value
... | no _ = lookup key rest

modes : List (String × Mode)
modes = ("disable" , disable) ∷ ("prefer" , prefer) ∷ ("require" , require) ∷
  ("verify-ca" , verifyCa) ∷ ("verify-full" , verifyFull) ∷ []

backends : List (String × Backend)
backends = ("voyage" , voyage) ∷ ("openai" , openai) ∷ ("local" , local) ∷ []

data Error : Set where
  unknownKey invalidMode invalidBackend zeroBatchSize : Error
  invalidPort invalidBatchSize : U.Error → Error

module Read (parser : U.Parser) (sizeMaximum : ℕ) where
  open Overrides sizeMaximum

  decode : Key → Text → Error ⊎ Setting
  decode hostKey value = inj₂ (host value)
  decode portKey value with U.parse parser 65535 value
  ... | inj₁ error = inj₁ (invalidPort error)
  ... | inj₂ parsed = inj₂ (port parsed)
  decode databaseKey value = inj₂ (dbname value)
  decode userKey value = inj₂ (user value)
  decode passwordKey value = inj₂ (password value)
  decode passfileKey value = inj₂ (pgpassfile value)
  decode modeKey value with lookup (fromList value) modes
  ... | nothing = inj₁ invalidMode
  ... | just parsed = inj₂ (mode parsed)
  decode rootKey value = inj₂ (rootCertificate value)
  decode certificateKey value = inj₂ (clientCertificate value)
  decode clientKeyKey value = inj₂ (clientKey value)
  decode backendKey value with lookup (fromList value) backends
  ... | nothing = inj₁ invalidBackend
  ... | just parsed = inj₂ (backend parsed)
  decode modelKey value = inj₂ (model value)
  decode apiKeyKey value = inj₂ (apiKey value)
  decode batchKey value with U.parse parser sizeMaximum value
  ... | inj₁ error = inj₁ (invalidBatchSize error)
  ... | inj₂ parsed with U.UInt.number parsed
  ...   | zero = inj₁ zeroBatchSize
  ...   | suc count = inj₂ (batchSize parsed)
  decode cacheKey value = inj₂ (cacheDirectory value)

  pair : String × Text → Error ⊎ Setting
  pair (name , value) with lookup name keys
  ... | nothing = inj₁ unknownKey
  ... | just key = decode key value

  collect : Config → List (String × Text) → Error ⊎ Config
  collect c [] = inj₂ c
  collect c (input ∷ rest) with pair input
  ... | inj₁ error = inj₁ error
  ... | inj₂ setting = collect (apply setting c) rest

  create : List (String × Text) → Error ⊎ Config
  create = collect defaultConfig

  -- A failed earlier argument is not hidden by a later override of that key.
  firstErrorPreserved : ∀ c input rest error → pair input ≡ inj₁ error →
    collect c (input ∷ rest) ≡ inj₁ error
  firstErrorPreserved c input rest error rejected rewrite rejected = refl

  noOverridesPreserveConfiguration : ∀ configuration → collect configuration [] ≡ inj₂ configuration
  noOverridesPreserveConfiguration configuration = refl

  literalPasswordAccepted : ∀ value → decode passwordKey value ≡ inj₂ (password value)
  literalPasswordAccepted value = refl
