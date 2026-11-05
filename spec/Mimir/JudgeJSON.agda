{-# OPTIONS --safe #-}
-- Mimir chooses the error stage and bounded private source excerpt. The
-- supplied library performs complete JSON parsing and text encoding.
import Mimir.StandardLibrary
module Mimir.JudgeJSON (conversion : Mimir.StandardLibrary.Contract) where

open import Data.List using (List)
open import Data.Maybe using (just)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Mimir.Text using (Text)
open import Mimir.Bits using (Byte)
import Mimir.StandardLibrary as Library
import Mimir.StructuredValue as Value
import Mimir.SourceFailure as Source
import Mimir.JudgeRevision as Revision

convert : Text → List Byte → Library.JSONResult → Revision.Error ⊎ Value.Value
convert stage input (Library.parsed value) = inj₂ value
convert stage input (Library.rejected error) = inj₁ (Revision.error (Source.display source) (just source))
  where source = Source.Current.json conversion stage input error
convert stage input (Library.panicked message) = inj₁ (Revision.error (Source.display source) (just source))
  where source = Source.Current.input conversion stage input message

read : Text → List Byte → Revision.Error ⊎ Value.Value
read stage input = convert stage input (Library.Contract.jsonValue conversion input)

text : Text → Text → Revision.Error ⊎ Value.Value
text stage source = read stage (Library.Contract.encodeUTF8 conversion source)
