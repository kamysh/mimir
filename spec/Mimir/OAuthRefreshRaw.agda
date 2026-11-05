{-# OPTIONS --safe #-}
-- The standard typed decoder handles raw JSON, including ignored values.
-- Mimir retains its required fields, optional refresh token, integer bound
-- and rejection of repeated known fields at the record/schema boundary.
module Mimir.OAuthRefreshRaw where

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (toList)
open import Mimir.Text using (Text)
open import Mimir.Bits using (Byte)
import Mimir.StandardLibrary as Library
import Mimir.SerdeSequence as Sequence
import Mimir.SerdeStruct as Struct
import Mimir.JudgeStatePrimitives as P
import Mimir.StructuredValue as V
import Mimir.OAuthCache as Cache
import Mimir.Validation as Validation

module Decode (conversion : Library.Contract) (clockMaximum : ℕ) where
  fields : List Sequence.Field
  fields = P.required (toList "access_token") Text V.asString ∷
    P.required (toList "token_type") Text V.asString ∷
    P.required (toList "expires_in") ℕ (P.uint clockMaximum) ∷
    P.optional (toList "refresh_token") Text V.asString ∷ []

  build : Sequence.Values fields → Cache.Refresh
  build (Sequence.more access (Sequence.more tokenType (Sequence.more expires
    (Sequence.more refresh Sequence.empty)))) = Cache.refresh tokenType access refresh expires

  schema : V.Value → Validation.Fault ⊎ Cache.Refresh
  schema raw with Struct.read fields raw
  ... | inj₁ failure = inj₁ (Validation.fault [] Validation.malformedInput "invalid OAuth refresh response")
  ... | inj₂ fields = inj₂ (build fields)

  parse : List Byte → Cache.AuthError ⊎ Cache.Refresh
  parse input with Library.readRecord conversion schema input
  ... | Library.decoded raw value observed = inj₂ value
  ... | Library.syntaxError error = inj₁ Cache.needsAttention
  ... | Library.schemaError error = inj₁ Cache.needsAttention
  ... | Library.decodePanicked message = inj₁ Cache.needsAttention
