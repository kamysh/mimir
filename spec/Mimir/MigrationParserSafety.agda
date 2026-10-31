{-# OPTIONS --safe #-}
-- All migration-file inputs either succeed or report ordinary parse failure.
-- No partial-stream, repetition-stall or separator-stall outcome is reachable.
module Mimir.MigrationParserSafety where

open import Data.Bool using (Bool)
open import Data.Char using (Char)
import Data.Char.Properties as Char
open import Data.List using ([]; _∷_; length)
open import Data.List.Properties using (length-++-≤ʳ)
open import Data.Maybe using (nothing; just)
open import Data.Nat using (s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.String using (toList)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (refl)
open import Mimir.Text using (Text; isWhitespace)
import Mimir.ExactBytes as Bytes
import Mimir.ParserSafety as Safety
import Mimir.MigrationHeader as Header
import Mimir.MigrationSlices as Slices
open import Mimir.MigrationSyntax
open P
module L = Safety.Laws Char ⊤ ⊥ (λ first second → second) (λ error → error)
open L

mapClean : ∀ {A B} f (parser : Parser A) → CleanParser parser → CleanParser (mapParser {B = B} f parser)
mapClean f parser proof input = cleanMap f (parser input) (proof input)

mapAdvances : ∀ {A B} f (parser : Parser A) → AdvancingParser parser → AdvancingParser (mapParser {B = B} f parser)
mapAdvances f parser proof input = advancesMap f (parser input) (proof input)

bindClean : ∀ {A B} (first : Parser A) (next : A → Parser B) →
  CleanParser first → (∀ value → CleanParser (next value)) → CleanParser (bind first next)
bindClean first next firstProof nextProof input = cleanBind (first input) next (firstProof input) nextProof

precededClean : ∀ {A B} (first : Parser A) (second : Parser B) →
  CleanParser first → CleanParser second → CleanParser (preceded first second)
precededClean first second firstProof secondProof = bindClean first (λ ignored → second) firstProof (λ ignored → secondProof)

terminatedClean : ∀ {A B} (first : Parser A) (second : Parser B) →
  CleanParser first → CleanParser second → CleanParser (terminated first second)
terminatedClean first second firstProof secondProof =
  bindClean first _ firstProof (λ value → mapClean (λ ignored → value) second secondProof)

precededAdvancesFirst : ∀ {A B} (first : Parser A) (second : Parser B) →
  AdvancingParser first → AdvancingParser (preceded first second)
precededAdvancesFirst first second proof input = advancesBindFirst (first input) _ (proof input)

precededAdvancesSecond : ∀ {A B} (first : Parser A) (second : Parser B) →
  AdvancingParser second → AdvancingParser (preceded first second)
precededAdvancesSecond first second proof input = advancesBindNext (first input) _ (λ ignored → proof)

terminatedAdvancesFirst : ∀ {A B} (first : Parser A) (second : Parser B) →
  AdvancingParser first → AdvancingParser (terminated first second)
terminatedAdvancesFirst first second proof input = advancesBindFirst (first input) _ (proof input)

literalClean : ∀ expected → CleanParser (literal expected)
literalClean expected input with Slices.Scan.Match.prefix? expected input
... | no missing = recoverable tt
... | yes present with Slices.Scan.stripPrefix present
...   | rest , exact = tt

literalAdvances : ∀ char rest → AdvancingParser (literal (char ∷ rest))
literalAdvances char rest input with Slices.Scan.Match.prefix? (char ∷ rest) input
... | no missing = tt
... | yes present with Slices.Scan.stripPrefix present
...   | after , exact = s≤s z≤n

characterClean : ∀ char → CleanParser (character char)
characterClean char = mapClean _ _ (literalClean (char ∷ []))

characterAdvances : ∀ char → AdvancingParser (character char)
characterAdvances char = mapAdvances _ _ (literalAdvances char [])

notQuoteClean : CleanParser notQuote
notQuoteClean [] = recoverable tt
notQuoteClean (char ∷ rest) with char Char.≟ '"'
... | yes same = recoverable tt
... | no different = tt

notQuoteAdvances : AdvancingParser notQuote
notQuoteAdvances [] = tt
notQuoteAdvances (char ∷ rest) with char Char.≟ '"'
... | yes same = tt
... | no different = s≤s z≤n

takeClean : ∀ predicate → CleanParser (Take.zeroOrMore predicate)
takeClean predicate input with Take.Split.split predicate input
... | Take.Split.cut before after exact notStopped boundary = tt

takeOneClean : ∀ predicate → CleanParser (Take.oneOrMore predicate)
takeOneClean predicate input with Take.Split.split predicate input
... | Take.Split.cut [] after exact notStopped boundary = recoverable tt
... | Take.Split.cut (_ ∷ _) after exact notStopped boundary = tt

wsClean : CleanParser ws
wsClean = takeClean isWhitespace

hspaceClean : CleanParser hspace
hspaceClean = takeClean horizontal

quotedCharClean : CleanParser quotedChar
quotedCharClean = cleanAlternative
  (preceded (character '\\') (alternative (character '"') (character '\\'))) notQuote
  (precededClean (character '\\') (alternative (character '"') (character '\\')) (characterClean '\\')
    (cleanAlternative (character '"') (character '\\') (characterClean '"') (characterClean '\\'))) notQuoteClean

quotedCharAdvances : AdvancingParser quotedChar
quotedCharAdvances = advancesAlternative
  (preceded (character '\\') (alternative (character '"') (character '\\'))) notQuote
  (precededAdvancesFirst (character '\\') (alternative (character '"') (character '\\')) (characterAdvances '\\')) notQuoteAdvances

quotedStringClean : CleanParser quotedString
quotedStringClean = precededClean (character '"') (terminated (repeat quotedChar) (character '"')) (characterClean '"')
  (terminatedClean (repeat quotedChar) (character '"') (cleanRepeat quotedChar quotedCharClean quotedCharAdvances) (characterClean '"'))

quotedStringAdvances : AdvancingParser quotedString
quotedStringAdvances = precededAdvancesFirst (character '"') (terminated (repeat quotedChar) (character '"')) (characterAdvances '"')

commaClean : CleanParser comma
commaClean = precededClean ws (preceded (character ',') ws) wsClean
  (precededClean (character ',') ws (characterClean ',') wsClean)

commaAdvances : AdvancingParser comma
commaAdvances = precededAdvancesSecond ws (preceded (character ',') ws)
  (precededAdvancesFirst (character ',') ws (characterAdvances ','))

arrayClean : CleanParser array
arrayClean = mapClean Header.multiple
  (preceded (character '[') (preceded ws (terminated (separated quotedString comma) (preceded ws (character ']')))))
  (precededClean (character '[') (preceded ws (terminated (separated quotedString comma) (preceded ws (character ']')))) (characterClean '[')
    (precededClean ws (terminated (separated quotedString comma) (preceded ws (character ']'))) wsClean
      (terminatedClean (separated quotedString comma) (preceded ws (character ']'))
        (cleanSeparated quotedString comma quotedStringClean commaClean commaAdvances)
        (precededClean ws (character ']') wsClean (characterClean ']')))))

fieldValueClean : CleanParser fieldValue
fieldValueClean = precededClean ws (alternative array (mapParser Header.single quotedString)) wsClean
  (cleanAlternative array (mapParser Header.single quotedString) arrayClean (mapClean Header.single quotedString quotedStringClean))

commentPrefixClean : CleanParser commentPrefix
commentPrefixClean = precededClean ws (literal (toList "-- ")) wsClean (literalClean (toList "-- "))

commentPrefixAdvances : AdvancingParser commentPrefix
commentPrefixAdvances = precededAdvancesSecond ws (literal (toList "-- ")) (literalAdvances '-' (toList "- "))

shebangClean : CleanParser shebang
shebangClean input with Slices.shebang input
... | nothing = recoverable tt
... | just found = tt

shebangAdvances : AdvancingParser shebang
shebangAdvances input with Slices.shebang input
... | nothing = tt
... | just found = ≤-trans (s≤s z≤n)
  (length-++-≤ʳ Slices.marker {xs = Slices.Shebang.before found})

bodyClean : CleanParser body
bodyClean input with Slices.readBody input | Slices.conservation input (Slices.readBody input)
... | parsedBody | spaces , whitespace , exact = tt

module HeaderLaws (alphanumeric : Char → Bool) where
  open HeaderSyntax alphanumeric

  keyValueClean : CleanParser keyValue
  keyValueClean = precededClean commentPrefix
    (bind (Take.oneOrMore keyCharacter) (λ key → mapParser (key ,_) (preceded ws (preceded (character ':') (preceded ws fieldValue)))))
    commentPrefixClean
    (bindClean (Take.oneOrMore keyCharacter)
      (λ key → mapParser (key ,_) (preceded ws (preceded (character ':') (preceded ws fieldValue))))
      (takeOneClean keyCharacter) (λ key → mapClean (key ,_) (preceded ws (preceded (character ':') (preceded ws fieldValue)))
        (precededClean ws (preceded (character ':') (preceded ws fieldValue)) wsClean
          (precededClean (character ':') (preceded ws fieldValue) (characterClean ':')
            (precededClean ws fieldValue wsClean fieldValueClean)))))

  keyValueAdvances : AdvancingParser keyValue
  keyValueAdvances = precededAdvancesFirst commentPrefix
    (bind (Take.oneOrMore keyCharacter) (λ key → mapParser (key ,_) (preceded ws (preceded (character ':') (preceded ws fieldValue)))))
    commentPrefixAdvances

  fieldEndingClean : ∀ ending → CleanParser (fieldEnding ending)
  fieldEndingClean ending = terminatedClean keyValue
    (preceded hspace (preceded (character ending) (preceded hspace (character '\n')))) keyValueClean
    (precededClean hspace (preceded (character ending) (preceded hspace (character '\n'))) hspaceClean
      (precededClean (character ending) (preceded hspace (character '\n')) (characterClean ending)
        (precededClean hspace (character '\n') hspaceClean (characterClean '\n'))))

  fieldEndingAdvances : ∀ ending → AdvancingParser (fieldEnding ending)
  fieldEndingAdvances ending = terminatedAdvancesFirst keyValue
    (preceded hspace (preceded (character ending) (preceded hspace (character '\n')))) keyValueAdvances

  headerClean : CleanParser header
  headerClean = bindClean (repeat (fieldEnding ','))
    (λ before → mapParser (λ last → before Data.List.++ last ∷ []) (fieldEnding ';'))
    (cleanRepeat (fieldEnding ',') (fieldEndingClean ',') (fieldEndingAdvances ','))
    (λ before → mapClean (λ last → before Data.List.++ last ∷ []) (fieldEnding ';') (fieldEndingClean ';'))

module FileLaws (alphanumeric : Char → Bool) (sha256 : Text → Bytes.Bytes 32) where
  open File alphanumeric sha256
  open HeaderLaws alphanumeric public

  constructClean : ∀ fields script → CleanParser (construct fields script)
  constructClean fields script input with Header.interpret fields
  ... | nothing = fatal tt
  ... | just decoded = tt

  migrationClean : CleanParser migration
  migrationClean = precededClean shebang (bind header (λ fields → bind body (construct fields))) shebangClean
    (bindClean header (λ fields → bind body (construct fields)) headerClean
      (λ fields → bindClean body (construct fields) bodyClean (constructClean fields)))

  migrationAdvances : AdvancingParser migration
  migrationAdvances = precededAdvancesFirst shebang (bind header (λ fields → bind body (construct fields))) shebangAdvances

  finishClean : ∀ {A input} (result : Result A input) → Clean result → Clean (finish result)
  finishClean (failure code before after exact) proof = proof
  finishClean (success value before [] exact) proof = tt
  finishClean (success value before (_ ∷ _) exact) proof = recoverable tt

  parseFileClean : CleanParser parseFile
  parseFileClean input = finishClean _ (cleanRepeat migration migrationClean migrationAdvances input)
