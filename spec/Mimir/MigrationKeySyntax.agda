{-# OPTIONS --safe #-}
-- Close the migration grammar's character-classification input with the
-- pinned compiler-table reference definition. SHA-256 remains explicit.
module Mimir.MigrationKeySyntax where

open import Mimir.Text using (Text)
import Mimir.ExactBytes as Bytes
import Mimir.RustUnicode as Unicode
import Mimir.MigrationSyntax as Syntax
import Mimir.MigrationParserSafety as Safety

module WithChecksum (sha256 : Text → Bytes.Bytes 32) where
  module Parser = Syntax.File Unicode.isAlphanumeric sha256
  module Laws = Safety.FileLaws Unicode.isAlphanumeric sha256
  open Parser public
  open Laws public
