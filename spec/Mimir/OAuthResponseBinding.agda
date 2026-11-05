{-# OPTIONS --safe #-}
-- Provider replies are admitted only through the bounded HTTP state machine
-- and the concrete JSON/schema decoder. A decoded token cannot be invented by
-- an unconstrained completion event.
module Mimir.OAuthResponseBinding where

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Mimir.Bits using (Byte)
import Mimir.FloatConversion as Conversion
import Mimir.OAuthRefreshRaw as Raw
import Mimir.OAuthHTTP as HTTP
import Mimir.OAuthWire as Wire
import Mimir.OAuthCache as Cache

module Decode (conversion : Conversion.Contract) (clockMaximum : ℕ) where
  private
    module RawReader = Raw.Decode conversion clockMaximum
  module H = HTTP.Production

  parse : List Byte → Cache.AuthError ⊎ Cache.Refresh
  parse = RawReader.parse

  Allowed : H.State → H.Input → Set
  Allowed (H.decoding buffer) (H.decoded value) = parse (H.B.Buffer.bytes buffer) ≡ inj₂ value
  Allowed (H.decoding buffer) H.malformed = Σ Cache.AuthError
    (λ error → parse (H.B.Buffer.bytes buffer) ≡ inj₁ error)
  Allowed _ (H.decoded _) = ⊥
  Allowed _ H.malformed = ⊥
  Allowed _ _ = ⊤

  data Trace : H.State → List H.Input → H.State → Set where
    empty : ∀ state → Trace state [] state
    more : ∀ before input inputs after → Allowed before input →
      Trace (H.Step.state (H.step before input)) inputs after → Trace before (input ∷ inputs) after

  data Result : H.State → Cache.AuthError ⊎ Cache.Refresh → Set where
    failure : ∀ error → Result (H.failed error) (inj₁ error)
    success : ∀ value valid → Result (H.complete value valid) (inj₂ value)

  record Receipt (reply : Cache.AuthError ⊎ Cache.Refresh) : Set where
    field inputs : List H.Input
          final : H.State
          execution : Trace H.waiting inputs final
          observed : Result final reply
