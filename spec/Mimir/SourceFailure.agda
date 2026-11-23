{-# OPTIONS --safe #-}
-- Status records retain the failure location, reported cause and input byte count.
module Mimir.SourceFailure where

open import Data.List using (List; _++_; length)
open import Data.Nat using (ℕ)
open import Data.String using (toList)
open import Mimir.Bits using (Byte)
open import Mimir.Text using (Text)
import Mimir.StandardLibrary as Library

record Failure : Set where
  constructor failure
  field stage detail : Text
        totalBytes : ℕ

display : Failure → Text
display result = Failure.stage result ++ (toList ": " ++ Failure.detail result)

module Current (library : Library.Contract) where
  input : Text → List Byte → Text → Failure
  input stage source detail = failure stage detail (length source)

  json : Text → List Byte → Library.JSONError → Failure
  json stage source error = input stage source (Library.JSONError.message error)
