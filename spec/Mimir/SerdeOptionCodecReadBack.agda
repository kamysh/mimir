{-# OPTIONS --safe #-}
-- Non-null scalar and object codecs compose through the optional reader.
import Mimir.FloatConversion
module Mimir.SerdeOptionCodecReadBack (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Bool using (true)
open import Data.Fin using (#_)
open import Data.List using (_∷_; _++_)
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; sym)
import Mimir.SerdeFlow as Flow
import Mimir.SerdeReadBack as Back
import Mimir.SerdeOption as OptionDependency
private
  module Option = OptionDependency floatConversion
import Mimir.SerdeOptionReadBack as OptionBackDependency
private
  module OptionBack = OptionBackDependency floatConversion
import Mimir.SerdeNumberStart as StartDependency
private
  module Start = StartDependency floatConversion
import Mimir.JsonTreeParser as TokensDependency
private
  module Tokens = TokensDependency floatConversion
import Mimir.JsonCompactRecords as Compact
import Mimir.JsonObjectReadBack as Encoding
import Mimir.StructuredValue as JSON
import Mimir.JsonString as String
import Mimir.JsonTextWriter as Writer

numberNotNull : ∀ byte → Tokens.classify byte ≡ Tokens.numberToken → byte ≢ (# 110)
numberNotNull byte () refl

number : ∀ {Value} (child : Flow.Parser Value) input value suffix → Start.Starts input →
  Back.Returns child input value suffix → Back.Returns (Option.read child) input (just value) suffix
number child .(byte ∷ rest) value suffix (Start.starts byte rest refl classified) receipt = OptionBack.some child byte rest value suffix
  (numberNotNull byte classified) (Start.notSpace byte classified)
  receipt

string : ∀ {Value} (child : Flow.Parser Value) text valid value suffix →
  Back.Returns child
    (String.spellString (String.StringValue.body (Writer.render text valid)) ++ suffix) value suffix →
  Back.Returns (Option.read child)
    (String.spellString (String.StringValue.body (Writer.render text valid)) ++ suffix) (just value) suffix
string child text valid value suffix receipt = OptionBack.some child (# 34)
  (String.spellBody
   (String.StringValue.body (Writer.render text valid))
   ++ suffix)
  value suffix (λ ()) (λ ()) receipt

object : ∀ {Value} (child : Flow.Parser Value) pairs valid value suffix →
  Back.Returns child (Compact.bytes (JSON.object pairs) (Compact.object valid) ++ suffix) value suffix →
  Back.Returns (Option.read child)
    (Compact.bytes (JSON.object pairs) (Compact.object valid) ++ suffix) (just value) suffix
object child pairs valid value suffix receipt = subst
  (λ input →
     Back.Returns (Option.read child) input (just value) suffix)
  (sym (Encoding.spelling pairs valid suffix))
  (OptionBack.some child (# 123)
   (Encoding.members true pairs valid suffix) value suffix (λ ())
   (λ ())
   (subst (λ input → Back.Returns child input value suffix)
    (Encoding.spelling pairs valid suffix) receipt))
