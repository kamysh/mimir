{-# OPTIONS --safe #-}
-- Embedded-file content handling: strict UTF-8, concrete syntax/checksum,
-- source-byte error offsets, and independent per-file implicit dependencies.
module Mimir.MigrationFileParsing where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Nat using (ℕ; _≤_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Mimir.Text using (Text; byteLength)
open import Mimir.Bits using (Byte)
import Mimir.UnicodeText as Unicode
import Mimir.UTF8Text as UTF8
import Mimir.DecodedText as Decoded
import Mimir.UnicodeCursorBytes as Cursor
import Mimir.MigrationChecksumSyntax as Parser
import Mimir.MigrationChecksumSafety as Safety
import Mimir.MigrationParserSafety as RawSafety
import Mimir.MigrationLedger as Ledger
import Mimir.MigrationImplicit as Implicit
import Mimir.WinnowPosition as Position
open Parser.Raw using (Result; success; failure; backtrack; cut; incomplete; repeatNoProgress; separatorNoProgress)

data Severity : Set where
  recoverable fatal : Severity

record Diagnostic (input : List Byte) : Set where
  constructor diagnostic
  field
    severity : Severity
    offset : ℕ
    bounded : offset ≤ length input

data Error : Set where
  invalidUtf8 : Text → Error
  parseError : (label : Text) (input : List Byte) → Diagnostic input → Error

location : ∀ {input} → Diagnostic input → Position.Location
location {input} error = Position.translate input (Diagnostic.offset error)

convert : ∀ label bytes input (valid : Unicode.Valid input) → Cursor.encoded input valid ≡ bytes →
  (parsed : Result (List Ledger.Migration) input) → RawSafety.L.Clean parsed → Error ⊎ List Ledger.Migration
convert label bytes input valid exact (success migrations before after consumed) ordinary = inj₂ (Implicit.file migrations)
convert label bytes input valid exact result@(failure (backtrack code) before after consumed) ordinary =
  inj₁ (parseError label bytes (diagnostic recoverable (byteLength before)
    (subst (λ source → byteLength before ≤ length source) exact (Cursor.offsetBound result valid))))
convert label bytes input valid exact result@(failure (cut code) before after consumed) ordinary =
  inj₁ (parseError label bytes (diagnostic fatal (byteLength before)
    (subst (λ source → byteLength before ≤ length source) exact (Cursor.offsetBound result valid))))
convert label bytes input valid exact (failure (incomplete needed) before after consumed) ()
convert label bytes input valid exact (failure repeatNoProgress before after consumed) ()
convert label bytes input valid exact (failure separatorNoProgress before after consumed) ()

readFile : Text → List Byte → Error ⊎ List Ledger.Migration
readFile label bytes with UTF8.decode bytes
... | inj₁ malformed = inj₁ (invalidUtf8 label)
... | inj₂ decodedInput = convert label bytes input admitted (Cursor.decodedBytesExact decodedInput)
  (Parser.parseFile input admitted) (Safety.fileClean input admitted)
  where
  input = Decoded.text (UTF8.Decoded.values decodedInput)
  admitted = Decoded.valid (UTF8.Decoded.values decodedInput)

invalidUtf8Refused : ∀ label bytes malformed → UTF8.decode bytes ≡ inj₁ malformed → readFile label bytes ≡ inj₁ (invalidUtf8 label)
invalidUtf8Refused label bytes malformed observed rewrite observed = refl

record File : Set where
  constructor file
  field label : Text; contents : List Byte

loadOrdered : List File → Error ⊎ List Ledger.Migration
loadOrdered [] = inj₂ []
loadOrdered (entry ∷ rest) with readFile (File.label entry) (File.contents entry)
... | inj₁ problem = inj₁ problem
... | inj₂ migrations with loadOrdered rest
...   | inj₁ problem = inj₁ problem
...   | inj₂ remaining = inj₂ (migrations ++ remaining)

firstFailureStops : ∀ entry rest problem → readFile (File.label entry) (File.contents entry) ≡ inj₁ problem →
  loadOrdered (entry ∷ rest) ≡ inj₁ problem
firstFailureStops entry rest problem observed rewrite observed = refl
