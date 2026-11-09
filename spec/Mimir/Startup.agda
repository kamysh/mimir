{-# OPTIONS --safe #-}
-- MCP process startup: argument handling precedes configuration and database I/O.
module Mimir.Startup where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans)

data Argument : Set where
  help version embeddingWorker unknown : Argument

data Invocation : Set where
  serve showHelp showVersion reject : Invocation

-- -h/--help and -V/--version map to help and version respectively.
-- Unknown includes positional, unsupported, and non-Unicode OS arguments.
-- Only an empty argument list starts the stdio MCP server.
classify : List Argument → Invocation
classify [] = serve
classify (help ∷ []) = showHelp
classify (version ∷ []) = showVersion
classify (embeddingWorker ∷ []) = reject
classify (unknown ∷ []) = reject
classify (_ ∷ _ ∷ _) = reject

accessesConfigurationOrDatabase : Invocation → Bool
accessesConfigurationOrDatabase serve = true
accessesConfigurationOrDatabase showHelp = false
accessesConfigurationOrDatabase showVersion = false
accessesConfigurationOrDatabase reject = false

-- Help/version exit successfully; rejected invocations exit with usage status 2.
-- None may load configuration, connect, or run migrations.
arguments-preclude-startup : ∀ arg rest →
  accessesConfigurationOrDatabase (classify (arg ∷ rest)) ≡ false
arguments-preclude-startup help [] = refl
arguments-preclude-startup version [] = refl
arguments-preclude-startup embeddingWorker [] = refl
arguments-preclude-startup unknown [] = refl
arguments-preclude-startup help (arg ∷ rest) = refl
arguments-preclude-startup version (arg ∷ rest) = refl
arguments-preclude-startup embeddingWorker (arg ∷ rest) = refl
arguments-preclude-startup unknown (arg ∷ rest) = refl

-- The synchronous executable entry selects the private worker BEFORE entering
-- application_main (and before its Tokio runtime). classify models only that
-- application entry, where the private flag would be a usage error.
data Entry : Set where
  application : Invocation → Entry
  worker : Entry

entryPoint : List Argument → Entry
entryPoint (embeddingWorker ∷ []) = worker
entryPoint args = application (classify args)

ApplicationEntry : List Argument → Set
ApplicationEntry args = entryPoint args ≡ application (classify args)

workerIsSeparate : ∀ invocation → worker ≢ application invocation
workerIsSeparate invocation ()

workerCannotEnterApplication : ∀ args → entryPoint args ≡ worker → ApplicationEntry args → ⊥
workerCannotEnterApplication args selected admitted =
  workerIsSeparate _ (trans (sym selected) admitted)
