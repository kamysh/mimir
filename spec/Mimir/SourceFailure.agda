{-# OPTIONS --safe #-}
-- The original source and the reported cause remain available for diagnosis.
-- Text decoding and JSON error descriptions are supplied externally.
module Mimir.SourceFailure where

open import Data.List using (List; _++_)
open import Data.String using (toList)
open import Mimir.Bits using (Byte)
open import Mimir.Text using (Text)
import Mimir.StandardLibrary as Library

record Failure : Set where
  constructor failure
  field stage detail excerpt : Text

display : Failure → Text
display result = Failure.stage result ++ (toList ": " ++ Failure.detail result)

module Current (library : Library.Contract) where
  input : Text → List Byte → Text → Failure
  input stage source detail = failure stage detail (Library.Contract.lossyUTF8 library source)

  json : Text → List Byte → Library.JSONError → Failure
  json stage source error = input stage source (Library.JSONError.message error)
