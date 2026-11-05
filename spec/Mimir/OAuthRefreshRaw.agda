{-# OPTIONS --safe #-}
-- Direct typed Serde decoding retains duplicate known fields. Converting to
-- serde_json::Value first would erase them and admit a different protocol.
module Mimir.OAuthRefreshRaw where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.String using (toList)
open import Mimir.Text using (Text)
open import Mimir.Bits using (Byte)
import Mimir.FloatConversion as Conversion
import Mimir.SerdeSequence as Sequence
import Mimir.SerdeSlots as Slots
import Mimir.SerdeFlow as Flow
import Mimir.SerdeRecord as Record
import Mimir.SerdeDocument as Document
import Mimir.SerdeOption as Option
import Mimir.JudgeStateAtoms as Atoms
import Mimir.JudgeStatePrimitives as P
import Mimir.StructuredValue as V
import Mimir.OAuthCache as Cache
import Mimir.SignedMachine as Machine
import Mimir.Validation as Validation

module Decode (conversion : Conversion.Contract) (clockMaximum : ℕ) where
  private
    module R = Record conversion
    module D = Document conversion
    module O = Option conversion
    module A = Atoms.Parser conversion Machine.disabled

  fields : List Sequence.Field
  fields = P.required (toList "access_token") Text V.asString ∷
    P.required (toList "token_type") Text V.asString ∷
    P.required (toList "expires_in") ℕ (P.uint clockMaximum) ∷
    P.optional (toList "refresh_token") Text V.asString ∷ []

  build : Sequence.Values fields → Cache.Refresh
  build (Sequence.more access (Sequence.more tokenType (Sequence.more expires
    (Sequence.more refresh Sequence.empty)))) = Cache.refresh tokenType access refresh expires

  readers : ℕ → Slots.Readers fields
  readers allowance = A.readText , A.readText , A.readUint clockMaximum , O.read A.readText , tt

  parser : Flow.Parser Cache.Refresh
  parser input = Flow.mapProductive (λ value → build (Slots.toSequence fields value))
    (R.Parser.read Machine.disabled fields readers
      (Validation.fault [] Validation.malformedInput "invalid OAuth refresh response") 128 input)

  parse : List Byte → Cache.AuthError ⊎ Cache.Refresh
  parse input with Flow.Productive.result (D.Parser.read Machine.disabled parser input)
  ... | Flow.ordinary (Flow.F.success value position) = inj₂ value
  ... | Flow.ordinary (Flow.F.failure error) = inj₁ Cache.needsAttention
  ... | Flow.panicked position = inj₁ Cache.needsAttention
