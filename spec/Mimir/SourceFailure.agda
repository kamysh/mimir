{-# OPTIONS --safe #-}
-- Complete private source text. Decoding and JSON error messages belong to
-- the standard library; Mimir does not crop or reinterpret their input.
module Mimir.SourceFailure where

open import Data.List using (List; length; _++_)
open import Data.Nat using (ℕ)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Bits using (Byte)
open import Mimir.Text using (Text)
import Mimir.StandardLibrary as Library

record Failure : Set where
  constructor failure
  field
    stage detail : Text
    totalBytes excerptStart : ℕ
    excerpt : Text

display : Failure → Text
display result = Failure.stage result ++ (toList ": " ++ Failure.detail result)

module With (library : Library.Contract) where
  input : Text → List Byte → Text → Failure
  input stage source detail = failure stage detail (length source) 0
    (Library.Contract.lossyUTF8 library source)

  completeInput : ∀ stage source detail →
    Failure.excerpt (input stage source detail) ≡ Library.Contract.lossyUTF8 library source
  completeInput stage source detail = refl

  json : Text → List Byte → Library.JSONError → Failure
  json stage source error = input stage source (Library.JSONError.message error)

  completeJSONSource : ∀ stage source error →
    Failure.excerpt (json stage source error) ≡ Library.Contract.lossyUTF8 library source
  completeJSONSource stage source error = refl

  exactDetail : ∀ stage source error → Failure.detail (json stage source error) ≡ Library.JSONError.message error
  exactDetail stage source error = refl

  exactSourceSize : ∀ stage source error → Failure.totalBytes (json stage source error) ≡ length source
  exactSourceSize stage source error = refl

  exactStage : ∀ stage source error → Failure.stage (json stage source error) ≡ stage
  exactStage stage source error = refl

module Current = With
