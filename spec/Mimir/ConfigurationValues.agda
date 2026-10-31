{-# OPTIONS --safe #-}
-- Core configuration values and the ordered KEY=VALUE update semantics.
-- Judge-owned TOML sections have their own schema; create_from_kv leaves them
-- absent. This module never emits filesystem or process effects.
module Mimir.ConfigurationValues where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤_; _≤?_)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable using (toWitness)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.Unsigned using (UInt)

data Backend : Set where voyage openai local : Backend
data Mode : Set where disable prefer require verifyCa verifyFull : Mode

record Database : Set where
  constructor database
  field
    host dbname user : Text
    port : ℕ
    password pgpassfile : Maybe Text
    mode : Mode
    rootCertificate clientCertificate clientKey : Maybe Text

record Embeddings : Set where
  constructor embeddings
  field
    backend : Backend
    model : Text
    apiKey : Maybe Text
    batchSize : ℕ
    cacheDirectory : Maybe Text

record Config : Set where
  constructor config
  field db : Database; embed : Maybe Embeddings

defaultDatabase : Database
defaultDatabase = database (toList "localhost") (toList "mimir") (toList "mimir")
  5432 nothing nothing prefer nothing nothing nothing

defaultEmbeddings : Embeddings
defaultEmbeddings = embeddings local [] nothing 0 nothing

defaultConfig : Config
defaultConfig = config defaultDatabase nothing

defaultPortBounded : Database.port (Config.db defaultConfig) ≤ 65535
defaultPortBounded = toWitness {a? = 5432 ≤? 65535} tt

getEmbeddings : Maybe Embeddings → Embeddings
getEmbeddings nothing = defaultEmbeddings
getEmbeddings (just e) = e

-- Size maximum is the chosen target's usize bound. Port retains its u16 bound.
module Overrides (sizeMaximum : ℕ) where
  data Setting : Set where
    host dbname user : Text → Setting
    port : UInt 65535 → Setting
    password pgpassfile rootCertificate clientCertificate clientKey : Text → Setting
    mode : Mode → Setting
    backend : Backend → Setting
    model apiKey cacheDirectory : Text → Setting
    batchSize : UInt sizeMaximum → Setting

  changeDatabase : (Database → Database) → Config → Config
  changeDatabase f c = config (f (Config.db c)) (Config.embed c)

  changeEmbedding : (Embeddings → Embeddings) → Config → Config
  changeEmbedding f c = config (Config.db c) (just (f (getEmbeddings (Config.embed c))))

  apply : Setting → Config → Config
  apply (host value) = changeDatabase (λ d → record d { host = value })
  apply (dbname value) = changeDatabase (λ d → record d { dbname = value })
  apply (user value) = changeDatabase (λ d → record d { user = value })
  apply (port value) = changeDatabase (λ d → record d { port = UInt.number value })
  apply (password value) = changeDatabase (λ d → record d { password = just value })
  apply (pgpassfile value) = changeDatabase (λ d → record d { pgpassfile = just value })
  apply (mode value) = changeDatabase (λ d → record d { mode = value })
  apply (rootCertificate value) = changeDatabase (λ d → record d { rootCertificate = just value })
  apply (clientCertificate value) = changeDatabase (λ d → record d { clientCertificate = just value })
  apply (clientKey value) = changeDatabase (λ d → record d { clientKey = just value })
  apply (backend value) = changeEmbedding (λ e → record e { backend = value })
  apply (model value) = changeEmbedding (λ e → record e { model = value })
  apply (apiKey value) = changeEmbedding (λ e → record e { apiKey = just value })
  apply (batchSize value) = changeEmbedding (λ e → record e { batchSize = UInt.number value })
  apply (cacheDirectory value) = changeEmbedding (λ e → record e { cacheDirectory = just value })

  applyAll : List Setting → Config → Config
  applyAll [] c = c
  applyAll (setting ∷ rest) c = applyAll rest (apply setting c)

  finalHostWins : ∀ old new c → apply (host new) (apply (host old) c) ≡ apply (host new) c
  finalHostWins old new c = refl

  finalPortWins : ∀ old new c → apply (port new) (apply (port old) c) ≡ apply (port new) c
  finalPortWins old new c = refl

  passwordPreservedLiterally : ∀ value c → Database.password (Config.db (apply (password value) c)) ≡ just value
  passwordPreservedLiterally value c = refl

  modelCreatesEmbedding : ∀ value db → Config.embed (apply (Setting.model value) (config db nothing)) ≡
    just (record defaultEmbeddings { model = value })
  modelCreatesEmbedding value db = refl

  backendPreservesModel : ∀ value db e →
    Config.embed (apply (Setting.backend value) (config db (just e))) ≡ just (record e { backend = value })
  backendPreservesModel value db e = refl

  portBoundPreserved : ∀ setting c → Database.port (Config.db c) ≤ 65535 →
    Database.port (Config.db (apply setting c)) ≤ 65535
  portBoundPreserved (host value) c proof = proof
  portBoundPreserved (dbname value) c proof = proof
  portBoundPreserved (user value) c proof = proof
  portBoundPreserved (port value) c proof = UInt.bounded value
  portBoundPreserved (password value) c proof = proof
  portBoundPreserved (pgpassfile value) c proof = proof
  portBoundPreserved (rootCertificate value) c proof = proof
  portBoundPreserved (clientCertificate value) c proof = proof
  portBoundPreserved (clientKey value) c proof = proof
  portBoundPreserved (mode value) c proof = proof
  portBoundPreserved (backend value) c proof = proof
  portBoundPreserved (model value) c proof = proof
  portBoundPreserved (apiKey value) c proof = proof
  portBoundPreserved (cacheDirectory value) c proof = proof
  portBoundPreserved (batchSize value) c proof = proof

  allPortsBounded : ∀ settings c → Database.port (Config.db c) ≤ 65535 →
    Database.port (Config.db (applyAll settings c)) ≤ 65535
  allPortsBounded [] c proof = proof
  allPortsBounded (setting ∷ rest) c proof = allPortsBounded rest (apply setting c) (portBoundPreserved setting c proof)
