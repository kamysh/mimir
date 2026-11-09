{-# OPTIONS --safe #-}
-- Every database path uses this credential/TLS preparation. Environment,
-- filesystem, certificate parsing and transport are explicit dependencies;
-- Mimir's precedence, certificate policy and startup ordering are concrete.
-- Transport I/O is external: its Rust interpreter disables driver-selected
-- idle connection probes and supplies no query deadline. This module does not
-- model TCP timers; shared driver settings and real connections are tested.
module Mimir.ConnectionProtocol where

open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.List using (List; []; _∷_; filterᵇ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (toList)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text; trim)
import Mimir.Bits as Bits
import Mimir.ConfigurationValues as Config
import Mimir.ConfigurationPath as Path
import Mimir.Password as Password
import Mimir.Connection as Connection
import Mimir.TLS as TLS
import Mimir.Effects as Effects

record Environment : Set where
  field password : Maybe Text; passfile home : Maybe Path.NativePath

passfile : Config.Database → Environment → Maybe Path.Path
passfile config env with Config.Database.pgpassfile config
... | just path = just (Path.utf8 path)
... | nothing with Environment.passfile env
...   | just path = just (Path.native path)
...   | nothing with Environment.home env
...     | nothing = nothing
...     | just path = just (Path.join (Path.native path) (toList ".pgpass"))

record Metadata : Set where
  constructor metadata
  field regular privatePermissions : Bool

data Failure : Set where
  tlsOptions : TLS.OptionError → Failure
  rootRead rootPEM emptyRoots certificateRead keyRead identityPEM connectorBuild transportFailure : Text → Failure

record Parameters : Set where
  constructor parameters
  field database : Config.Database; password : Maybe Text; searchPath : Text

record Usable (mode : Config.Mode) : Set where
  constructor usable
  field client : ℕ; transport : Connection.Transport; trusted hostname : Bool
        reached : TLS.Reachable mode (TLS.usable transport trusted hostname)

data Effect : Set where
  metadataAt : Path.Path → Effect
  readPasswordFile : Path.Path → Effect
  warnPermissions : Effect
  readRoot : Text → Effect
  parseRoot : Text → Effect
  addRoot disableBuiltinRoots : Effect
  readCertificate readKey : Text → Effect
  parseIdentity : List Bits.Byte → List Bits.Byte → Effect
  build : TLS.Options → Effect
  connect : (parameters : Parameters) → Effect
  spawnConnectionTask : ℕ → Effect

Reply : Effect → Set
Reply (metadataAt _) = Maybe Metadata
Reply (readPasswordFile _) = Maybe Text
Reply warnPermissions = ⊤
Reply (readRoot _) = Text ⊎ Text
Reply (parseRoot _) = Text ⊎ ⊤
Reply addRoot = ⊤
Reply disableBuiltinRoots = ⊤
Reply (readCertificate _) = Text ⊎ List Bits.Byte
Reply (readKey _) = Text ⊎ List Bits.Byte
Reply (parseIdentity _ _) = Text ⊎ ⊤
Reply (build _) = Text ⊎ ⊤
Reply (connect params) = Text ⊎ Usable (Config.Database.mode (Parameters.database params))
Reply (spawnConnectionTask _) = ⊤

module P = Effects.Protocol Effect Reply
open P using (Script; done; ask; _>>=_)

module Prepare (decimalPort : ℕ → Text) (certificateBlocks : Text → List Text) (unix : Bool) where
  selectors : Config.Database → Password.Selectors
  selectors config = Password.connection (Config.Database.host config) (decimalPort (Config.Database.port config))
    (Config.Database.dbname config) (Config.Database.user config)

  readPassword : Config.Database → Path.Path → Script (Maybe Text)
  readPassword config path = ask (readPasswordFile path) λ where
    nothing → done nothing
    (just content) → done (Password.lookupFile (selectors config) content)

  afterMetadata : Config.Database → Path.Path → Maybe Metadata → Script (Maybe Text)
  afterMetadata config path nothing = done nothing
  afterMetadata config path (just (metadata false secure)) = done nothing
  afterMetadata config path (just (metadata true secure)) with unix ∧ not secure
  ... | true = ask warnPermissions (λ _ → done nothing)
  ... | false = readPassword config path

  fromFile : Config.Database → Environment → Script (Maybe Text)
  fromFile config env with passfile config env
  ... | nothing = done nothing
  ... | just path = ask (metadataAt path) (afterMetadata config path)

  password : Config.Database → Environment → Script (Maybe Text)
  password config env with Config.Database.password config
  ... | just value = done (just value)
  ... | nothing with Password.nonempty (Environment.password env)
  ...   | just value = done (just value)
  ...   | nothing = fromFile config env

  nonblank : Text → Bool
  nonblank block with trim block
  ... | [] = false
  ... | _ ∷ _ = true

  roots : List Text → Script (Failure ⊎ ⊤)
  roots [] = ask disableBuiltinRoots (λ _ → done (inj₂ tt))
  roots (block ∷ rest) = ask (parseRoot block) λ where
    (inj₁ error) → done (inj₁ (rootPEM error))
    (inj₂ tt) → ask addRoot (λ _ → roots rest)

  rootFile : Maybe Text → Script (Failure ⊎ ⊤)
  rootFile nothing = done (inj₂ tt)
  rootFile (just path) = ask (readRoot path) after
    where
    after : Text ⊎ Text → Script (Failure ⊎ ⊤)
    after (inj₁ error) = done (inj₁ (rootRead error))
    after (inj₂ content) with filterᵇ nonblank (certificateBlocks content)
    ... | [] = done (inj₁ (emptyRoots (toList "ssl_root_cert contains no certificates")))
    ... | blocks@(_ ∷ _) = roots blocks

  identity : TLS.Identity → Script (Failure ⊎ ⊤)
  identity TLS.absent = done (inj₂ tt)
  identity (TLS.present cert key) = ask (readCertificate cert) λ where
    (inj₁ error) → done (inj₁ (certificateRead error))
    (inj₂ certificate) → ask (readKey key) λ where
      (inj₁ error) → done (inj₁ (keyRead error))
      (inj₂ keyBytes) → ask (parseIdentity certificate keyBytes) λ where
        (inj₁ error) → done (inj₁ (identityPEM error))
        (inj₂ tt) → done (inj₂ tt)

  connector : Config.Database → Script (Failure ⊎ ⊤)
  connector config with TLS.validateOptions (Config.Database.mode config) (Config.Database.rootCertificate config)
    (Config.Database.clientCertificate config) (Config.Database.clientKey config)
  ... | inj₁ error = done (inj₁ (tlsOptions error))
  ... | inj₂ connectionOptions = rootFile (TLS.Options.root connectionOptions) >>= λ where
    (inj₁ error) → done (inj₁ error)
    (inj₂ tt) → identity (TLS.Options.identity connectionOptions) >>= λ where
      (inj₁ error) → done (inj₁ error)
      (inj₂ tt) → ask (build connectionOptions) λ where
        (inj₁ error) → done (inj₁ (connectorBuild error))
        (inj₂ tt) → done (inj₂ tt)

  openConnection : (config : Config.Database) → Environment → Script (Failure ⊎ Usable (Config.Database.mode config))
  openConnection config env = password config env >>= λ selected → connector config >>= λ where
    (inj₁ error) → done (inj₁ error)
    (inj₂ tt) → ask (connect (parameters config selected (toList "public,ag_catalog"))) λ where
      (inj₁ error) → done (inj₁ (transportFailure error))
      (inj₂ client) → ask (spawnConnectionTask (Usable.client client)) (λ _ → done (inj₂ client))

  forPath : Connection.Path → (config : Config.Database) → Environment → Script (Failure ⊎ Usable (Config.Database.mode config))
  forPath path = openConnection

  uniformConnectionPolicy : ∀ path config env → forPath path config env ≡ openConnection config env
  uniformConnectionPolicy path config env = refl
