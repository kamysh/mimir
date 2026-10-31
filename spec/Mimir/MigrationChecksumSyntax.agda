{-# OPTIONS --safe #-}
-- Migration syntax with concrete compiler-table classification, admitted
-- Unicode text, UTF-8 encoding and the complete reference SHA-256 checksum.
module Mimir.MigrationChecksumSyntax where

open import Data.List using (List; []; _∷_; _++_)
import Data.List.Properties as List
open import Data.Maybe using (nothing; just)
open import Data.Product using (Σ; _,_; proj₁)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)
open import Mimir.Text using (Text; trim)
import Mimir.UnicodeText as Unicode
import Mimir.UnicodeChecksum as Checksum
import Mimir.UnicodeParser as U
import Mimir.RustUnicode as Classify
import Mimir.MigrationSyntax as Syntax
import Mimir.MigrationHeader as Header
import Mimir.MigrationSlices as Slices
import Mimir.MigrationLedger as Ledger

module Raw = Syntax.P
module H = Syntax.HeaderSyntax Classify.isAlphanumeric
open Raw using (Result; success; failure; cut; backtrack; fail; done; mapResult)

body : U.Parser (Σ Text Unicode.Valid)
body input valid with Slices.readBody input | Slices.conservation input (Slices.readBody input)
... | parsedBody | spaces , whitespace , exact =
  success (Slices.script parsedBody , U.Keep.body input parsedBody valid)
    (spaces ++ Slices.Body.raw parsedBody) (Slices.Body.rest parsedBody)
    (trans exact (sym (List.++-assoc spaces (Slices.Body.raw parsedBody) (Slices.Body.rest parsedBody))))

bodyErases : ∀ input valid → mapResult proj₁ (body input valid) ≡ Syntax.body input
bodyErases input valid with Slices.readBody input | Slices.conservation input (Slices.readBody input)
... | parsedBody | spaces , whitespace , exact = refl

construct : Header.Fields → Σ Text Unicode.Valid → U.Parser Ledger.Migration
construct fields (script , admitted) input valid with Header.interpret fields
... | nothing = fail (cut tt) input
... | just decoded = done (Ledger.migrationRecord (Header.Header.name decoded)
  (Ledger.metadata (Header.Header.description decoded) (Header.Header.requires decoded)
    (Checksum.checksum (trim script) (U.Keep.trimAll admitted)) script)) input

migration : U.Parser Ledger.Migration
migration = U.bind (U.lift Syntax.shebang) (λ ignored →
  U.bind (U.lift H.header) (λ fields → U.bind body (construct fields)))

finish : ∀ {A input} → Result A input → Result A input
finish result@(failure code consumed remaining exact) = result
finish result@(success value consumed [] exact) = result
finish (success value consumed remaining@(_ ∷ _) exact) = failure (backtrack tt) consumed remaining exact

parseFile : U.Parser (List Ledger.Migration)
parseFile input valid = finish (U.repeat migration input valid)

successConsumesAll : ∀ {A input} (result : Result A input) value consumed remaining exact →
  finish result ≡ success value consumed remaining exact → remaining ≡ []
successConsumesAll (failure code before after same) value consumed remaining exact ()
successConsumesAll (success value before [] same) .value .before .[] .same refl = refl
successConsumesAll (success value before (_ ∷ _) same) other consumed remaining exact ()

fileSuccessConsumesAll : ∀ input valid value consumed remaining exact →
  parseFile input valid ≡ success value consumed remaining exact → remaining ≡ []
fileSuccessConsumesAll input valid = successConsumesAll (U.repeat migration input valid)
