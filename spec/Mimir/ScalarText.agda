{-# OPTIONS --safe #-}
-- Text operations directly over decoded Unicode scalars. Their connection to
-- the existing Char-based schema model is proved through Represents, without
-- assuming an inverse for the primitive Nat-to-Char conversion.
module Mimir.ScalarText where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; reverse)
open import Data.List.Properties using (unfold-reverse)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
import Mimir.UTF8Packet as Packet
import Mimir.Text as Text
import Mimir.UnicodeText as Unicode

Values = List Packet.Scalar

isWhitespace : Packet.Scalar → Bool
isWhitespace value = Text.member (Packet.codePoint (Packet.Scalar.raw value)) Text.whiteSpaceCodepoints

trimStart : Values → Values
trimStart [] = []
trimStart (value ∷ rest) with isWhitespace value
... | true = trimStart rest
... | false = value ∷ rest

trim : Values → Values
trim values = reverse (trimStart (reverse (trimStart values)))

representsAppend : ∀ {firstText firstValues secondText secondValues} →
  Unicode.Represents firstText firstValues → Unicode.Represents secondText secondValues →
  Unicode.Represents (firstText ++ secondText) (firstValues ++ secondValues)
representsAppend Unicode.empty second = second
representsAppend (Unicode.more same first) second = Unicode.more same (representsAppend first second)

representsReverse : ∀ {text values} → Unicode.Represents text values →
  Unicode.Represents (reverse text) (reverse values)
representsReverse Unicode.empty = Unicode.empty
representsReverse (Unicode.more {c = c} {chars = chars} {value = value} {values = values} same rest)
  rewrite unfold-reverse c chars | unfold-reverse value values =
  representsAppend (representsReverse rest) (Unicode.more same Unicode.empty)

representsTrimStart : ∀ {text values} → Unicode.Represents text values →
  Unicode.Represents (Text.trimStart text) (trimStart values)
representsTrimStart Unicode.empty = Unicode.empty
representsTrimStart (Unicode.more {c = c} same rest)
  rewrite sym (cong (λ number → Text.member number Text.whiteSpaceCodepoints) same)
  with Text.isWhitespace c
... | true = representsTrimStart rest
... | false = Unicode.more same rest

representsTrim : ∀ {text values} → Unicode.Represents text values →
  Unicode.Represents (Text.trim text) (trim values)
representsTrim represented = representsReverse
  (representsTrimStart (representsReverse (representsTrimStart represented)))

emptyTextMeansEmptyValues : ∀ {values} → Unicode.Represents [] values → values ≡ []
emptyTextMeansEmptyValues Unicode.empty = refl

emptyValuesMeanEmptyText : ∀ {text} → Unicode.Represents text [] → text ≡ []
emptyValuesMeanEmptyText Unicode.empty = refl
