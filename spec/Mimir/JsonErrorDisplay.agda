{-# OPTIONS --safe #-}
-- Error origin, clamped peek position, and serde_json Display messages.
-- Native arithmetic panics remain outside the JSON error-message channel.
module Mimir.JsonErrorDisplay where

open import Data.List using ([]; _∷_; _++_; length)
open import Data.List.Properties using (++-identityʳ; length-++)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (zero; suc; _≤_; _⊓_; s≤s)
open import Data.Nat.Properties using (m≤n⇒m⊓n≡m; m≥n⇒m⊓n≡n; n≤1+n; m≤m+n; +-suc)
open import Data.Product using (_,_)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
open import Mimir.Text using (Text)
import Mimir.JsonControls as Controls
import Mimir.JsonFlow as Flow
import Mimir.NumericTokens as Numeric
import Mimir.JsonStringParser as Strings
import Mimir.JsonEscapeParser as Escapes
import Mimir.JsonPosition as Position
import Mimir.NatDecimal as Decimal
module F = Flow.F

locate : ∀ {input} → Numeric.Position → F.Cursor input → Position.Position
locate Numeric.current origin = Position.scan (Position.position 1 0) (F.Cursor.consumed origin)
locate Numeric.peek (F.cursor consumed [] exact) = Position.scan (Position.position 1 0) consumed
locate Numeric.peek (F.cursor consumed (byte ∷ rest) exact) = Position.step (Position.scan (Position.position 1 0) consumed) byte

peekIndex : ∀ {input} → F.Cursor input → Data.Nat.ℕ
peekIndex (F.cursor consumed [] exact) = length consumed
peekIndex (F.cursor consumed (byte ∷ rest) exact) = suc (length consumed)

peekIndexClamped : ∀ {input} (cursor : F.Cursor input) → peekIndex cursor ≡ length input ⊓ suc (length (F.Cursor.consumed cursor))
peekIndexClamped (F.cursor consumed [] refl) rewrite ++-identityʳ consumed = sym (m≤n⇒m⊓n≡m (n≤1+n (length consumed)))
peekIndexClamped (F.cursor consumed (byte ∷ rest) refl) = sym (m≥n⇒m⊓n≡n
  (subst (suc (length consumed) ≤_) (sym (trans (length-++ consumed) (+-suc (length consumed) (length rest))))
    (s≤s (m≤m+n (length consumed) (length rest)))))

peekSlicePosition : ∀ {input} consumed byte rest exact →
  locate Numeric.peek (F.cursor {input} consumed (byte ∷ rest) exact) ≡ Position.slicePosition (consumed ++ (byte ∷ []))
peekSlicePosition consumed byte rest exact = trans (sym (Position.scanAppend (Position.position 1 0) consumed (byte ∷ [])))
  (Position.sourceCorrespondence (consumed ++ (byte ∷ [])))

escapeMessage : Escapes.Code → Text
escapeMessage Escapes.eofString = toList "EOF while parsing a string"
escapeMessage Escapes.invalidEscape = toList "invalid escape"
escapeMessage Escapes.unexpectedEndHex = toList "unexpected end of hex escape"
escapeMessage Escapes.loneSurrogate = toList "lone leading surrogate in hex escape"

stringMessage : Strings.Code → Text
stringMessage Strings.eofString = toList "EOF while parsing a string"
stringMessage Strings.controlCharacter = toList "control character (\\u0000-\\u001F) found while parsing a string"
stringMessage Strings.expectedQuote = toList "expected `\"`"
stringMessage (Strings.escapeError error) = escapeMessage error
stringMessage (Strings.invalidUnicode error) = toList "invalid unicode code point"

message : Controls.Reason → Maybe Text
message Controls.eofValue = just (toList "EOF while parsing a value")
message Controls.eofList = just (toList "EOF while parsing a list")
message Controls.eofObject = just (toList "EOF while parsing an object")
message Controls.expectedIdent = just (toList "expected ident")
message Controls.expectedValue = just (toList "expected value")
message Controls.expectedColon = just (toList "expected `:`")
message Controls.expectedListCommaOrEnd = just (toList "expected `,` or `]`")
message Controls.expectedObjectCommaOrEnd = just (toList "expected `,` or `}`")
message Controls.keyString = just (toList "key must be a string")
message Controls.trailingComma = just (toList "trailing comma")
message Controls.trailingCharacters = just (toList "trailing characters")
message Controls.recursionLimit = just (toList "recursion limit exceeded")
message (Controls.numericError Numeric.eofValue) = just (toList "EOF while parsing a value")
message (Controls.numericError Numeric.invalidNumber) = just (toList "invalid number")
message (Controls.numericError Numeric.numberOutOfRange) = just (toList "number out of range")
message (Controls.numericError Numeric.arithmeticPanic) = nothing
message (Controls.stringError error) = just (stringMessage error)

atPosition : Text → Position.Position → Text
atPosition message (Position.position zero column) = message
atPosition message (Position.position (suc line) column) = message ++
  (toList " at line " ++ (Decimal.text (suc line) ++ (toList " column " ++ Decimal.text column)))

renderFault : ∀ {input} → F.Fault input → Maybe Text
renderFault (F.fault (reason , mode) origin) with message reason
... | nothing = nothing
... | just text = just (atPosition text (locate mode origin))

renderRejected : ∀ {input} → F.Rejected input → Maybe Text
renderRejected failure = renderFault (F.Rejected.firstError failure)

cleanupPreservesMessage : ∀ {input} (failure : F.Rejected input) after →
  renderRejected (F.extendRejected failure after) ≡ renderRejected failure
cleanupPreservesMessage failure after = refl
