{-# OPTIONS --safe #-}
-- JSON whitespace may occur at every lexical boundary accepted by the skip reader.
import Mimir.FloatConversion
module Mimir.JsonIgnoredSpacedSyntax (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (#_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Bits using (Byte)
import Mimir.ByteText as Wire
import Mimir.JsonWhitespace as White
import Mimir.JsonIgnoredString as String
import Mimir.JsonIgnoredReadBack as ScalarDependency
private
  module Scalar = ScalarDependency floatConversion
import Mimir.JsonIgnoredValueSyntax as CompactDependency
private
  module Compact = CompactDependency floatConversion
import Mimir.JsonIgnoredNumberSyntax as Number
import Mimir.JsonIgnoredNumberReadBack as Character
import Mimir.DecimalLexer as Digits

record Gap : Set where
  constructor gap
  field bytes : List Byte; valid : All White.Space bytes

mutual
  data Value : Set where
    value : Gap → Core → Value

  data Core : Set where
    null : Core
    boolean : Bool → Core
    string : Compact.Quoted → Core
    number : ∀ bytes item → Wire.text bytes ≡ Number.spell item [] → Core
    array : Items → Core
    object : Members → Core

  data Items : Set where
    itemsEnd : Gap → Items
    itemsMore : Gap → Value → Items → Items

  data Members : Set where
    membersEnd : Gap → Members
    membersMore : Gap → Gap → Compact.Quoted → Gap → Value → Members → Members

mutual
  spell : Value → List Byte → List Byte
  spell (value before item) suffix = Gap.bytes before ++ core item suffix

  core : Core → List Byte → List Byte
  core null suffix = (# 110) ∷ (# 117) ∷ (# 108) ∷ (# 108) ∷ suffix
  core (boolean choice) suffix = Scalar.spelling choice ++ suffix
  core (string text) suffix = (# 34) ∷ (String.spellBody (Compact.Quoted.body text) ++ suffix)
  core (number bytes item exact) suffix = bytes ++ suffix
  core (array items) suffix = (# 91) ∷ arrayBody true items suffix
  core (object members) suffix = (# 123) ∷ objectBody true members suffix

  arrayBody : Bool → Items → List Byte → List Byte
  arrayBody first (itemsEnd before) suffix = Gap.bytes before ++ ((# 93) ∷ suffix)
  arrayBody true (itemsMore before item items) suffix = Gap.bytes before ++ spell item (arrayBody false items suffix)
  arrayBody false (itemsMore before item items) suffix = Gap.bytes before ++ ((# 44) ∷ spell item (arrayBody false items suffix))

  objectBody : Bool → Members → List Byte → List Byte
  objectBody first (membersEnd before) suffix = Gap.bytes before ++ ((# 125) ∷ suffix)
  objectBody true (membersMore before keyGap name colonGap item members) suffix = Gap.bytes before ++
    fieldBytes keyGap name colonGap item (objectBody false members suffix)
  objectBody false (membersMore before keyGap name colonGap item members) suffix = Gap.bytes before ++
    ((# 44) ∷ fieldBytes keyGap name colonGap item (objectBody false members suffix))

  fieldBytes : Gap → Compact.Quoted → Gap → Value → List Byte → List Byte
  fieldBytes before name colonGap item suffix = Gap.bytes before ++ memberBytes name colonGap item suffix

  memberBytes : Compact.Quoted → Gap → Value → List Byte → List Byte
  memberBytes name before item suffix = (# 34) ∷
    (String.spellBody (Compact.Quoted.body name) ++ (Gap.bytes before ++ ((# 58) ∷ spell item suffix)))

begins : ∀ item suffix → Compact.Leading (core item suffix)
begins null suffix = Compact.begins Compact.null suffix
begins (boolean choice) suffix = Compact.begins (Compact.boolean choice) suffix
begins (string text) suffix = Compact.begins (Compact.string text) suffix
begins (number bytes item exact) suffix = Compact.begins (Compact.number bytes item exact) suffix
begins (array items) suffix = Compact.leading (# 91) _ refl (λ ()) (λ ())
begins (object members) suffix = Compact.leading (# 123) _ refl (λ ()) (λ ())

spaceStopped : ∀ byte → White.Space byte → ∀ suffix → Character.Stopped (Wire.text (byte ∷ suffix))
spaceStopped .(# 32) White.sp suffix = Digits.notDecoded ' ' refl , (λ ()) , (λ ()) , (λ ())
spaceStopped .(# 9) White.ht suffix = Digits.notDecoded '\t' refl , (λ ()) , (λ ()) , (λ ())
spaceStopped .(# 10) White.lf suffix = Digits.notDecoded '\n' refl , (λ ()) , (λ ()) , (λ ())
spaceStopped .(# 13) White.cr suffix = Digits.notDecoded '\r' refl , (λ ()) , (λ ()) , (λ ())

gapStopped : ∀ before suffix → Character.Stopped (Wire.text suffix) →
  Character.Stopped (Wire.text (Gap.bytes before ++ suffix))
gapStopped (gap [] All.[]) suffix stopped = stopped
gapStopped (gap (byte ∷ bytes) (admitted All.∷ valid)) suffix stopped = spaceStopped byte admitted (bytes ++ suffix)

arrayDelimiter : ∀ items suffix → Character.Stopped (Wire.text (arrayBody false items suffix))
arrayDelimiter (itemsEnd before) suffix = gapStopped before (# 93 ∷ suffix)
  (Digits.notDecoded ']' refl , (λ ()) , (λ ()) , (λ ()))
arrayDelimiter (itemsMore before item items) suffix = gapStopped before
  (# 44 ∷ spell item (arrayBody false items suffix))
  (Digits.notDecoded ',' refl , (λ ()) , (λ ()) , (λ ()))

objectDelimiter : ∀ members suffix → Character.Stopped (Wire.text (objectBody false members suffix))
objectDelimiter (membersEnd before) suffix = gapStopped before (# 125 ∷ suffix)
  (Digits.notDecoded '}' refl , (λ ()) , (λ ()) , (λ ()))
objectDelimiter (membersMore before keyGap name colonGap item members) suffix = gapStopped before
  (# 44 ∷
   fieldBytes keyGap name colonGap item
   (objectBody false members suffix))
  (Digits.notDecoded ',' refl , (λ ()) , (λ ()) , (λ ()))
