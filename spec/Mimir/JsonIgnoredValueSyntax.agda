{-# OPTIONS --safe #-}
-- Recursive ignored-value grammar, initially without inter-token whitespace.
import Mimir.FloatConversion
module Mimir.JsonIgnoredValueSyntax (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (#_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (map-++)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym)
open import Mimir.Bits using (Byte)
import Mimir.ByteText as Wire
import Mimir.JsonIgnoredString as String
import Mimir.JsonIgnoredReadBack as ScalarDependency
private
  module Scalar = ScalarDependency floatConversion
import Mimir.JsonIgnoredNumberSyntax as Number
import Mimir.JsonIgnoredNumberWireReadBack as NumericDependency
private
  module Numeric = NumericDependency floatConversion
import Mimir.JsonIgnoredNumberReadBack as Character
import Mimir.DecimalLexer as Digits
import Mimir.Unsigned as Decimal
import Mimir.JsonNumberWire as Encoding
import Mimir.SerdeNumberStart as StartDependency
private
  module Start = StartDependency floatConversion
import Mimir.JsonTreeParser as TokensDependency
private
  module Tokens = TokensDependency floatConversion
import Mimir.JsonWhitespace as White

record Quoted : Set where
  constructor quoted
  field body : String.Body; valid : String.ValidBody body

data Value : Set where
  null : Value
  boolean : Bool → Value
  string : Quoted → Value
  number : ∀ bytes value → Wire.text bytes ≡ Number.spell value [] → Value
  array : List Value → Value
  object : List (Quoted × Value) → Value

mutual
  spell : Value → List Byte → List Byte
  spell null suffix = (# 110) ∷ (# 117) ∷ (# 108) ∷ (# 108) ∷ suffix
  spell (boolean value) suffix = Scalar.spelling value ++ suffix
  spell (string value) suffix = (# 34) ∷ (String.spellBody (Quoted.body value) ++ suffix)
  spell (number bytes value exact) suffix = bytes ++ suffix
  spell (array values) suffix = (# 91) ∷ arrayBody true values suffix
  spell (object fields) suffix = (# 123) ∷ objectBody true fields suffix

  arrayBody : Bool → List Value → List Byte → List Byte
  arrayBody first [] suffix = (# 93) ∷ suffix
  arrayBody true (value ∷ values) suffix = spell value (arrayBody false values suffix)
  arrayBody false (value ∷ values) suffix = (# 44) ∷ spell value (arrayBody false values suffix)

  objectBody : Bool → List (Quoted × Value) → List Byte → List Byte
  objectBody first [] suffix = (# 125) ∷ suffix
  objectBody true (entry ∷ fields) suffix = fieldBytes entry (objectBody false fields suffix)
  objectBody false (entry ∷ fields) suffix = (# 44) ∷ fieldBytes entry (objectBody false fields suffix)

  fieldBytes : Quoted × Value → List Byte → List Byte
  fieldBytes (name , value) suffix = (# 34) ∷
    (String.spellBody (Quoted.body name) ++ ((# 58) ∷ spell value suffix))

numberText : ∀ bytes value → Wire.text bytes ≡ Number.spell value [] → ∀ suffix →
  Wire.text (bytes ++ suffix) ≡ Number.spell value (Wire.text suffix)
numberText bytes value exact suffix = trans (map-++ Wire.character bytes suffix)
  (trans (cong (_++ Wire.text suffix) exact)
   (sym (Number.spellAppend value [] (Wire.text suffix))))

record Leading (input : List Byte) : Set where
  constructor leading
  field
    first : Byte
    rest : List Byte
    exact : input ≡ first ∷ rest
    stopped : White.Stopped (first ∷ rest)
    notClose : first ≢ (# 93)

numericToken : ∀ byte → Numeric.Start byte → Tokens.classify byte ≡ Tokens.numberToken
numericToken .(# 45) Numeric.minus = refl
numericToken .(Wire.byte (Decimal.character value) (Encoding.digitBounded value)) (Numeric.digit value) = Start.digitToken value

numberNotClose : ∀ byte → Tokens.classify byte ≡ Tokens.numberToken → byte ≢ (# 93)
numberNotClose byte () refl

begins : ∀ value suffix → Leading (spell value suffix)
begins null suffix = leading (# 110) _ refl (λ ()) (λ ())
begins (boolean true) suffix = leading (# 116) _ refl (λ ()) (λ ())
begins (boolean false) suffix = leading (# 102) _ refl (λ ()) (λ ())
begins (string value) suffix = leading (# 34) _ refl (λ ()) (λ ())
begins (number bytes value exact) suffix with Numeric.syntaxStart bytes value [] exact
... | Numeric.starts first rest refl valid = leading first (rest ++ suffix) refl
  (Start.notSpace first (numericToken first valid))
  (numberNotClose first (numericToken first valid))
begins (array values) suffix = leading (# 91) _ refl (λ ()) (λ ())
begins (object fields) suffix = leading (# 123) _ refl (λ ()) (λ ())

arrayDelimiter : ∀ values suffix → Character.Stopped (Wire.text (arrayBody false values suffix))
arrayDelimiter [] suffix = Digits.notDecoded ']' refl , (λ ()) , (λ ()) , (λ ())
arrayDelimiter (value ∷ values) suffix = Digits.notDecoded ',' refl , (λ ()) , (λ ()) , (λ ())

objectDelimiter : ∀ fields suffix → Character.Stopped (Wire.text (objectBody false fields suffix))
objectDelimiter [] suffix = Digits.notDecoded '}' refl , (λ ()) , (λ ()) , (λ ())
objectDelimiter (entry ∷ fields) suffix = Digits.notDecoded ',' refl , (λ ()) , (λ ()) , (λ ())
