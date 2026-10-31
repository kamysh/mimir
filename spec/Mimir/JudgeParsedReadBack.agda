{-# OPTIONS --safe #-}
-- Successful executable decoding preserves the original guarded read and its events.
module Mimir.JudgeParsedReadBack where

open import Data.List using ([])
open import Data.Maybe using (just)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
import Mimir.JudgeParsedRead as Parsed
import Mimir.SerdeFlow as Flow
import Mimir.SerdeReadBack as Back

module With (Path Handle NativeError Value : Set) (decode : Flow.Parser Value) where
  private module P = Parsed.With Path Handle NativeError Value decode

  successfulDecoded : ∀ {limit} (raw : P.Raw.Read limit) reply exact value position →
    reply ≡ Flow.ordinary (Flow.F.success value position) →
    Σ (P.Loaded limit) (λ accepted →
      P.decoded raw reply exact ≡ P.returned (inj₂ (just accepted)) ×
      P.Loaded.value accepted ≡ value × P.Loaded.raw accepted ≡ raw)
  successfulDecoded raw reply exact value position refl = P.loaded raw value position exact , refl , refl , refl

  afterRead : ∀ {limit} (raw : P.Raw.Read limit) value →
    Back.Returns decode (P.Raw.Read.bytes raw) value [] →
    Σ (P.Loaded limit) (λ accepted →
      P.afterRead (inj₂ (just raw)) ≡ P.returned (inj₂ (just accepted)) ×
      P.Loaded.value accepted ≡ value × P.Loaded.raw accepted ≡ raw)
  afterRead raw value (Back.returned position observed remaining) = successfulDecoded raw
    (Flow.Productive.result (decode (P.Raw.Read.bytes raw))) refl value
    position observed

  read : ∀ path filePath ancestors limit events (raw : P.Raw.Read limit) value →
    P.FS.Runs (P.Raw.readNamed path filePath ancestors limit) events (inj₂ (just raw)) →
    Back.Returns decode (P.Raw.Read.bytes raw) value [] →
    Σ (P.Loaded limit) (λ accepted →
      P.FS.Runs (P.readNamed path filePath ancestors limit) events (P.returned (inj₂ (just accepted))) ×
      P.Loaded.value accepted ≡ value × P.Loaded.raw accepted ≡ raw)
  read path filePath ancestors limit events raw value execution receipt with afterRead raw value receipt
  ... | accepted , exact , sameValue , sameRaw = accepted ,
    subst
    (P.FS.Runs (P.readNamed path filePath ancestors limit) events)
    exact
    (P.sameEvents path filePath ancestors limit events
     (inj₂ (just raw)) execution)
    , sameValue , sameRaw
