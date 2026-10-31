{-# OPTIONS --safe #-}
-- Service startup composes the existing concrete migration runtime and the
-- shared connection protocol. Creating an embedding backend is lazy: startup
-- does not load a tokenizer/model or send an embedding request.
module Mimir.ServiceStartup where

open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.Char using (Char; toℕ; _≟_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤?_)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.ConfigurationValues as Config
import Mimir.ConnectionProtocol as Connection
import Mimir.MigrationRuntime as Migration

asciiNameChar : Char → Bool
asciiNameChar c = (does (48 ≤? n) ∧ does (n ≤? 57)) ∨
  (does (65 ≤? n) ∧ does (n ≤? 90)) ∨ (does (97 ≤? n) ∧ does (n ≤? 122)) ∨ does (c ≟ '_')
  where n = toℕ c

allNameChars : Text → Bool
allNameChars [] = true
allNameChars (c ∷ cs) = asciiNameChar c ∧ allNameChars cs

graphName : Text → Bool
graphName [] = false
graphName text@(_ ∷ _) = allNameChars text

module Run (config : Config.Config) (env : Connection.Environment)
  (decimalPort : ℕ → Text) (certificateBlocks : Text → List Text) (unix : Bool) where
  module M = Migration.Runtime Text Text
  module C = Connection.Prepare decimalPort certificateBlocks unix
  db = Config.Config.db config

  record Service : Set where
    constructor service
    field client : Connection.Usable (Config.Database.mode db)
          embeddings : Maybe Config.Embeddings
          nameValid : graphName (Config.Database.dbname db) ≡ true

  data Failure : Set where
    migration : M.Problem → Failure
    connection : Connection.Failure → Failure
    invalidGraphName : Failure

  data State : Set where
    migrating : M.E.Script (M.Problem ⊎ Data.Unit.⊤) → State
    connecting : Connection.P.Script (Connection.Failure ⊎ Connection.Usable (Config.Database.mode db)) → State
    ready : Service → State
    failed : Failure → State

  connected : Connection.Usable (Config.Database.mode db) → State
  connected client with graphName (Config.Database.dbname db) in valid
  ... | false = failed invalidGraphName
  ... | true = ready (service client (Config.Config.embed config) valid)

  data Event : Set where
    migration : M.E.Event → Event
    connection : Connection.P.Event → Event
    returned : Event

  data Step : State → Event → State → Set where
    migrationReply : ∀ effect continuation reply → Step (migrating (M.E.ask effect continuation))
      (migration (effect , reply)) (migrating (continuation reply))
    migrationFailure : ∀ error → Step (migrating (M.E.done (inj₁ error))) returned (failed (migration error))
    migrated : Step (migrating (M.E.done (inj₂ tt))) returned (connecting (C.openConnection db env))
    connectionReply : ∀ effect continuation reply → Step (connecting (Connection.P.ask effect continuation))
      (connection (effect , reply)) (connecting (continuation reply))
    connectionFailure : ∀ error → Step (connecting (Connection.P.done (inj₁ error))) returned (failed (connection error))
    usable : ∀ client → Step (connecting (Connection.P.done (inj₂ client))) returned (connected client)

  start : M.Inputs → State
  start inputs = migrating (M.Run.migrate inputs)

  data Trace : State → List Event → State → Set where
    empty : ∀ state → Trace state [] state
    more : ∀ before event middle events after → Step before event middle → Trace middle events after →
      Trace before (event ∷ events) after
