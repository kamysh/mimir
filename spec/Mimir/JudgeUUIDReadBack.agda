{-# OPTIONS --safe #-}
-- Canonical UUID strings round-trip through the actual raw UUID field reader.
import Mimir.FloatConversion
module Mimir.JudgeUUIDReadBack (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.List using (_++_)
import Mimir.JudgeStateAtoms as AtomsDependency
private
  module Atoms = AtomsDependency floatConversion
import Mimir.JudgeStatePrimitives as Primitive
import Mimir.JudgeTextReadBack as TextDependency
private
  module Text = TextDependency floatConversion
import Mimir.UUIDSchema as UUID
import Mimir.JsonString as String
import Mimir.JsonTextWriter as Writer
import Mimir.SerdeReadBack as Back
import Mimir.SignedMachine as Machine

module Parser (checks : Machine.OverflowChecks) where
  roundTrip : ∀ value suffix → Back.Returns (Atoms.Parser.readUUID checks)
    (String.spellString (String.StringValue.body (Writer.render (UUID.text value) (UUID.valid value))) ++ suffix)
    value suffix
  roundTrip value suffix = Text.Parser.checkedRoundTrip checks Atoms.uuid Atoms.stringExpected
    (UUID.text value) (UUID.valid value) value
    (Primitive.uuidRoundTrip value) suffix
