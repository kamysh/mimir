{-# OPTIONS --safe #-}
-- No-progress/incomplete outcomes are unreachable in the concrete checksum
-- parser for every admitted Unicode input, without a checksum oracle.
module Mimir.MigrationChecksumSafety where

open import Data.List using ([]; _∷_)
open import Data.Maybe using (nothing; just)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
import Mimir.MigrationSyntax as RawSyntax
import Mimir.MigrationParserSafety as RawSafety
import Mimir.UnicodeParser as U
open import Mimir.UnicodeParserSafety
open import Mimir.MigrationChecksumSyntax
import Mimir.MigrationHeader as Header
import Mimir.MigrationSlices as Slices
import Mimir.RustUnicode as Classify
open RawSyntax.P using (Result; success; failure)
open RawSafety.L using (Clean; recoverable; fatal)
module HSafe = RawSafety.HeaderLaws Classify.isAlphanumeric

bodyClean : CleanParser body
bodyClean input valid with Slices.readBody input | Slices.conservation input (Slices.readBody input)
... | parsedBody | spaces , whitespace , exact = tt

constructClean : ∀ fields script → CleanParser (construct fields script)
constructClean fields (script , admitted) input valid with Header.interpret fields
... | nothing = fatal tt
... | just decoded = tt

migrationClean : CleanParser migration
migrationClean = cleanBind (U.lift RawSyntax.shebang)
  (λ ignored → U.bind (U.lift H.header) (λ fields → U.bind body (construct fields)))
  (cleanLift RawSyntax.shebang RawSafety.shebangClean)
  (λ ignored → cleanBind (U.lift H.header) (λ fields → U.bind body (construct fields))
    (cleanLift H.header HSafe.headerClean)
    (λ fields → cleanBind body (construct fields) bodyClean (constructClean fields)))

migrationAdvances : AdvancingParser migration
migrationAdvances = advancesBind (U.lift RawSyntax.shebang)
  (λ ignored → U.bind (U.lift H.header) (λ fields → U.bind body (construct fields)))
  (advancesLift RawSyntax.shebang RawSafety.shebangAdvances)

finishClean : ∀ {A input} (result : Result A input) → Clean result → Clean (finish result)
finishClean (failure code before after exact) proof = proof
finishClean (success value before [] exact) proof = tt
finishClean (success value before (_ ∷ _) exact) proof = recoverable tt

fileClean : CleanParser parseFile
fileClean input valid = finishClean (U.repeat migration input valid)
  (cleanRepeat migration migrationClean migrationAdvances input valid)
