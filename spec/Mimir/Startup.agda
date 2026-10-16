{-# OPTIONS --safe #-}
-- MCP process startup: argument handling precedes configuration and database I/O.
module Mimir.Startup where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Argument : Set where
  help version unknown : Argument

data Invocation : Set where
  serve showHelp showVersion reject : Invocation

-- -h/--help and -V/--version map to help and version respectively.
-- Unknown includes positional, unsupported, and non-Unicode OS arguments.
-- Only an empty argument list starts the stdio MCP server.
classify : List Argument → Invocation
classify [] = serve
classify (help ∷ []) = showHelp
classify (version ∷ []) = showVersion
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
arguments-preclude-startup unknown [] = refl
arguments-preclude-startup help (arg ∷ rest) = refl
arguments-preclude-startup version (arg ∷ rest) = refl
arguments-preclude-startup unknown (arg ∷ rest) = refl
