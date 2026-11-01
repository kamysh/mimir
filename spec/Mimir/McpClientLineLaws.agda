{-# OPTIONS --safe #-}
module Mimir.McpClientLineLaws where

open import Data.List.Relation.Unary.All using (All)
import Mimir.McpClientLine as Line
import Mimir.ReadLine as LF

module Laws where
  module F = Line.Framing
  successfulBodyContainsNoLF : ∀ (buffer : F.Buffer) → All LF.NotLF (F.Buffer.bytes buffer)
  successfulBodyContainsNoLF = F.Buffer.noLF

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.Nat using (_≟_)
open import Data.Fin using (toℕ)
open import Data.Product using (_,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Mimir.Bits using (Byte)

module Exact where
  module F = Line.Framing

  bytesRead : List Line.E.Event → List Byte
  bytesRead [] = []
  bytesRead ((Line.readByte , Line.byteRead byte) ∷ rest) = byte ∷ bytesRead rest
  bytesRead (_ ∷ rest) = bytesRead rest

  -- A completed frame consumes every accumulated byte followed by exactly one
  -- LF; no ordinary byte can vanish while the reader waits for the delimiter.
  data Framed (before : F.Buffer) : List Line.E.Event → F.Buffer → Set where
    delimiter : ∀ byte → toℕ byte ≡ 10 →
      Framed before ((Line.readByte , Line.byteRead byte) ∷ []) before
    ordinary : ∀ byte notLF events after →
      Framed (F.advance before byte notLF) events after →
      Framed before ((Line.readByte , Line.byteRead byte) ∷ events) after

  diagnosticCannotComplete : ∀ events after →
    F.Runs F.diagnostic events (F.complete after) → ⊥
  diagnosticCannotComplete ._ after (F.replied refl bytes (F.replied () reply rest))

  settlingCannotComplete : ∀ events after →
    F.Runs F.settling events (F.complete after) → ⊥
  settlingCannotComplete ._ after (F.replied refl reply run) = diagnosticCannotComplete _ after run

  frameReceipt : ∀ before events after →
    F.Runs (F.reading before) events (F.complete after) → Framed before events after
  frameReceipt before ._ after (F.replied refl Line.ioEnded run) =
    ⊥-elim (settlingCannotComplete _ after run)
  frameReceipt before ._ after (F.replied refl (Line.byteRead byte) run) with toℕ byte ≟ 10
  ... | yes lf with run
  ...   | F.returned .(F.complete before) = delimiter byte lf
  ...   | F.replied () reply rest
  frameReceipt before ._ after (F.replied refl (Line.byteRead byte) run) | no notLF =
    ordinary byte notLF _ after (frameReceipt (F.advance before byte notLF) _ after run)
