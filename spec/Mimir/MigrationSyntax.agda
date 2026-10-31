{-# OPTIONS --safe #-}
-- Complete-parser control composition for Kryzhen's migration_file. The
-- compiler's alphanumeric predicate and SHA-256 implementation remain explicit
-- inputs until their source correspondence is closed; neither is postulated.
module Mimir.MigrationSyntax where

open import Data.Bool using (Bool; true; false)
open import Data.Char using (Char)
import Data.Char.Properties as Char
open import Data.List using (List; []; _∷_; _++_)
import Data.List.Properties as List
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.String using (toList)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong)
open import Mimir.Text using (Text; isWhitespace; trim)
import Mimir.ExactBytes as Bytes
import Mimir.BacktrackingParser as Backtracking
import Mimir.TextFields as Fields
import Mimir.MigrationHeader as Header
import Mimir.MigrationSlices as Slices
import Mimir.MigrationLedger as Ledger

module P = Backtracking.Parsers Char ⊤ ⊥ (λ first second → second) (λ error → error)
open P

bind : ∀ {A B} → Parser A → (A → Parser B) → Parser B
bind first next input = andThen (first input) (λ value rest → next value rest)

mapParser : ∀ {A B} → (A → B) → Parser A → Parser B
mapParser transform parser input = mapResult transform (parser input)

preceded : ∀ {A B} → Parser A → Parser B → Parser B
preceded first second = bind first (λ ignored → second)

terminated : ∀ {A B} → Parser A → Parser B → Parser A
terminated first second = bind first (λ value → mapParser (λ ignored → value) second)

literal : Text → Parser Text
literal expected input with Slices.Scan.Match.prefix? expected input
... | no missing = fail (backtrack tt) input
... | yes present with Slices.Scan.stripPrefix present
...   | rest , exact = success expected expected rest exact

character : Char → Parser Char
character expected = mapParser (λ ignored → expected) (literal (expected ∷ []))

notQuote : Parser Char
notQuote [] = fail (backtrack tt) []
notQuote (char ∷ rest) with char Char.≟ '"'
... | yes same = fail (backtrack tt) (char ∷ rest)
... | no different = success char (char ∷ []) rest refl

module Take (predicate : Char → Bool) where
  stop? : ∀ char → Dec (predicate char ≡ false)
  stop? char with predicate char
  ... | false = yes refl
  ... | true = no (λ ())
  module Split = Fields.Split (λ char → predicate char ≡ false) stop?

  zeroOrMore : Parser Text
  zeroOrMore input with Split.split input
  ... | Split.cut before after exact notStopped boundary = success before before after exact

  oneOrMore : Parser Text
  oneOrMore input with Split.split input
  ... | Split.cut [] after exact notStopped boundary = fail (backtrack tt) input
  ... | Split.cut before@(_ ∷ _) after exact notStopped boundary = success before before after exact

horizontal : Char → Bool
horizontal char with char Char.≟ ' '
... | yes same = true
... | no other with char Char.≟ '\t'
...   | yes same = true
...   | no different = false

ws hspace : Parser Text
ws = Take.zeroOrMore isWhitespace
hspace = Take.zeroOrMore horizontal

quotedChar : Parser Char
quotedChar = alternative (preceded (character '\\')
  (alternative (character '"') (character '\\'))) notQuote

quotedString : Parser Text
quotedString = preceded (character '"') (terminated (repeat quotedChar) (character '"'))

comma : Parser Text
comma = preceded ws (preceded (character ',') ws)

array : Parser Header.Value
array = mapParser Header.multiple (preceded (character '[')
  (preceded ws (terminated (separated quotedString comma) (preceded ws (character ']')))))

fieldValue : Parser Header.Value
fieldValue = preceded ws (alternative array (mapParser Header.single quotedString))

commentPrefix : Parser Text
commentPrefix = preceded ws (literal (toList "-- "))

shebang : Parser ⊤
shebang input with Slices.shebang input
... | nothing = fail (backtrack tt) input
... | just found = success tt (Slices.Shebang.before found ++ Slices.marker) (Slices.Shebang.rest found)
  (trans (Slices.shebangConservation input found)
    (sym (List.++-assoc (Slices.Shebang.before found) Slices.marker (Slices.Shebang.rest found))))

body : Parser Text
body input with Slices.readBody input | Slices.conservation input (Slices.readBody input)
... | parsedBody | spaces , whitespace , exact =
  success (Slices.script parsedBody) (spaces ++ Slices.Body.raw parsedBody) (Slices.Body.rest parsedBody)
    (trans exact (sym (List.++-assoc spaces (Slices.Body.raw parsedBody) (Slices.Body.rest parsedBody))))

module HeaderSyntax (alphanumeric : Char → Bool) where
  keyCharacter : Char → Bool
  keyCharacter char with alphanumeric char
  ... | true = true
  ... | false with char Char.≟ '_'
  ...   | yes same = true
  ...   | no different = false

  keyValue : Parser (Text × Header.Value)
  keyValue = preceded commentPrefix (bind (Take.oneOrMore keyCharacter) λ key →
    mapParser (key ,_) (preceded ws (preceded (character ':') (preceded ws fieldValue))))

  fieldEnding : Char → Parser (Text × Header.Value)
  fieldEnding ending = terminated keyValue
    (preceded hspace (preceded (character ending) (preceded hspace (character '\n'))))

  header : Parser Header.Fields
  header = bind (repeat (fieldEnding ',')) (λ before → mapParser (λ last → before ++ last ∷ []) (fieldEnding ';'))

module File (alphanumeric : Char → Bool) (sha256 : Text → Bytes.Bytes 32) where
  open HeaderSyntax alphanumeric public

  construct : Header.Fields → Text → Parser Ledger.Migration
  construct fields script input with Header.interpret fields
  ... | nothing = fail (cut tt) input
  ... | just decoded = done (Ledger.migrationRecord (Header.Header.name decoded)
    (Ledger.metadata (Header.Header.description decoded) (Header.Header.requires decoded)
      (sha256 (trim script)) script)) input

  migration : Parser Ledger.Migration
  migration = preceded shebang (bind header (λ fields → bind body (construct fields)))

  -- Parser::parse appends EOF after repeat. Input left by a recoverable
  -- failed migration therefore becomes an EOF error at the restored cursor.
  finish : ∀ {A input} → Result A input → Result A input
  finish (failure code consumed remaining exact) = failure code consumed remaining exact
  finish result@(success value consumed [] exact) = result
  finish (success value consumed remaining@(_ ∷ _) exact) = failure (backtrack tt) consumed remaining exact

  parseFile : Parser (List Ledger.Migration)
  parseFile input = finish (repeat migration input)

  missingRequiredFieldCuts : ∀ fields script input → Header.interpret fields ≡ nothing →
    construct fields script input ≡ fail (cut tt) input
  missingRequiredFieldCuts fields script input missing rewrite missing = refl

  finishedSuccessConsumesAll : ∀ {A input} (result : Result A input) value consumed remaining exact →
    finish result ≡ success value consumed remaining exact → remaining ≡ []
  finishedSuccessConsumesAll (failure code before after same) value consumed remaining exact ()
  finishedSuccessConsumesAll (success value before [] same) .value .before .[] .same refl = refl
  finishedSuccessConsumesAll (success value before (_ ∷ _) same) other consumed remaining exact ()

  fileSuccessConsumesAll : ∀ input value consumed remaining exact →
    parseFile input ≡ success value consumed remaining exact → remaining ≡ []
  fileSuccessConsumesAll input = finishedSuccessConsumesAll (repeat migration input)
