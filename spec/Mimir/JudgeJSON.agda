{-# OPTIONS --safe #-}
-- Reuse the checked release JSON parser and source-window diagnostics for all
-- judge adapters. Syntax errors preserve the original byte buffer and position.
import Mimir.FloatConversion
module Mimir.JudgeJSON (conversion : Mimir.FloatConversion.Contract) where

open import Data.List using (List; [])
open import Data.Maybe using (just)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Mimir.Text using (Text)
open import Mimir.Bits using (Byte)
import Mimir.JsonReleaseDocument as JSONDependency
import Mimir.SchemaDocument as SchemaDependency
import Mimir.StructuredValue as Value
import Mimir.SourceFailure as Source
import Mimir.JudgeRevision as Revision
module JSON = JSONDependency conversion
module Schema = SchemaDependency conversion

convert : ∀ {input} → Text → JSON.Result input → Revision.Error ⊎ Value.Value
convert stage (JSON.accepted parsedDocument position complete) = inj₂ (Schema.Document.value parsedDocument)
convert stage (JSON.rejected failure safe) = inj₁ (Revision.error (Source.display source) (just source))
  where source = Source.Current.json stage failure safe

read : Text → List Byte → Revision.Error ⊎ Value.Value
read stage input = convert stage (JSON.read input)

text : Text → Text → Revision.Error ⊎ Value.Value
text stage source with JSON.readString source
... | JSON.invalidScalar _ = inj₁ (Revision.error stage (just
    (Source.Current.input stage [] (Data.String.toList "non-scalar input text"))))
  where import Data.String
... | JSON.admitted valid result = convert stage result
