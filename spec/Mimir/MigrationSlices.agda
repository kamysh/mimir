{-# OPTIONS --safe #-}
-- Exact shebang search and SQL body boundaries. A delimiter inside SQL text
-- still ends the body: this parser does not lex SQL strings or comments.
module Mimir.MigrationSlices where

open import Data.Char using (Char)
import Data.Char.Properties as Char
open import Data.Bool using (true)
open import Data.List using ([]; _∷_; _++_; reverse)
import Data.List.Properties as List
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Data.String using (toList)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Mimir.Text using (Text; trimStart; isWhitespace)
import Mimir.SubstringScan as Substring
import Mimir.WhitespaceCut as Whitespace

module Scan = Substring.Scan Char Char._≟_

marker delimiter : Text
marker = toList "-- #!migration"
delimiter = toList "\n-- #!"

record Shebang (input : Text) : Set where
  constructor shebangAt
  field
    before atMarker rest : Text
    first : Scan.First marker input before atMarker
    consumed : atMarker ≡ marker ++ rest

shebang : ∀ input → Maybe (Shebang input)
shebang input with Scan.search marker input
... | Scan.absent missing = nothing
... | Scan.found before atMarker first with Scan.stripPrefix (Scan.startsAtBoundary first)
...   | rest , consumed = just (shebangAt before atMarker rest first consumed)

data BodyCase (prepared : Text) : Text → Text → Set where
  atEnd : ¬ Scan.Match.Contains delimiter prepared → BodyCase prepared prepared []
  atDelimiter : ∀ {raw rest} → Scan.First delimiter prepared raw rest → BodyCase prepared raw rest

record Body (input : Text) : Set where
  constructor bodyAt
  field raw rest : Text; boundary : BodyCase (trimStart input) raw rest

readBody : ∀ input → Body input
readBody input with Scan.search delimiter (trimStart input)
... | Scan.absent missing = bodyAt (trimStart input) [] (atEnd missing)
... | Scan.found before after first = bodyAt before after (atDelimiter first)

trimEnd : Text → Text
trimEnd text = reverse (trimStart (reverse text))

script : ∀ {input} → Body input → Text
script parsedBody = trimEnd (Body.raw parsedBody)

bodyExact : ∀ {prepared raw rest} → BodyCase prepared raw rest → prepared ≡ raw ++ rest
bodyExact {prepared} (atEnd missing) = sym (List.++-identityʳ prepared)
bodyExact (atDelimiter first) = Scan.exact first

conservation : ∀ input (parsedBody : Body input) → Σ Text λ spaces →
  All (λ char → isWhitespace char ≡ true) spaces × input ≡ spaces ++ (Body.raw parsedBody ++ Body.rest parsedBody)
conservation input parsedBody with Whitespace.cut input
... | Whitespace.cutAt spaces rest exact whitespace boundary trimmed = spaces , whitespace ,
  trans exact (cong (spaces ++_) (trans trimmed (bodyExact (Body.boundary parsedBody))))

shebangConservation : ∀ input (parsedShebang : Shebang input) →
  input ≡ Shebang.before parsedShebang ++ (marker ++ Shebang.rest parsedShebang)
shebangConservation input parsedShebang = trans (Scan.exact (Shebang.first parsedShebang))
  (cong (Shebang.before parsedShebang ++_) (Shebang.consumed parsedShebang))
