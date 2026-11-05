{-# OPTIONS --safe #-}
-- Compose guarded byte reads with an executable parser. A parser panic is a
-- distinct observation, never converted to the public invalid-report error.
module Mimir.JudgeParsedRead where

open import Data.Empty using (⊥)
open import Data.List using (List)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)
open import Mimir.Bits using (Byte)
import Mimir.JudgeRead as Read
import Mimir.SerdeFlow as Flow
import Mimir.EffectMap as EffectMap

module With (Path Handle NativeError Value : Set) (decode : Flow.Parser Value) where
  module Raw = Read.With Path Handle NativeError (List Byte) ⊥ inj₂
  module FS = Raw.FS
  module Map = EffectMap.Protocol FS.Operation FS.Reply

  record Loaded (limit : Maybe ℕ) : Set where
    constructor loaded
    field
      raw : Raw.Read limit
      value : Value
      position : Flow.F.Cursor (Raw.Read.bytes raw)
      decoded : Flow.Productive.result (decode (Raw.Read.bytes raw)) ≡
        Flow.ordinary (Flow.F.success value position)

  data Outcome (limit : Maybe ℕ) : Set where
    returned : FS.Result (Maybe (Loaded limit)) → Outcome limit
    decoderPanicked : (raw : Raw.Read limit) (position : Flow.F.Cursor (Raw.Read.bytes raw)) →
      Flow.Productive.result (decode (Raw.Read.bytes raw)) ≡ Flow.panicked position → Outcome limit

  decoded : ∀ {limit} (raw : Raw.Read limit) (reply : Flow.Result Value (Raw.Read.bytes raw)) →
    Flow.Productive.result (decode (Raw.Read.bytes raw)) ≡ reply → Outcome limit
  decoded raw (Flow.ordinary (Flow.F.failure error)) exact = returned (inj₁ FS.invalidReport)
  decoded raw (Flow.ordinary (Flow.F.success value position)) exact =
    returned (inj₂ (just (loaded raw value position exact)))
  decoded raw (Flow.panicked position) exact = decoderPanicked raw position exact

  afterRead : ∀ {limit} → FS.Result (Maybe (Raw.Read limit)) → Outcome limit
  afterRead (inj₁ error) = returned (inj₁ error)
  afterRead (inj₂ nothing) = returned (inj₂ nothing)
  afterRead (inj₂ (just raw)) = decoded raw (Flow.Productive.result (decode (Raw.Read.bytes raw))) refl

  readNamed : Path → Path → Maybe (List Path) → (limit : Maybe ℕ) → FS.Script (Outcome limit)
  readNamed path filePath ancestors limit = Map.map afterRead (Raw.readNamed path filePath ancestors limit)

  sameEvents : ∀ path filePath ancestors limit events response →
    FS.Runs (Raw.readNamed path filePath ancestors limit) events response →
    FS.Runs (readNamed path filePath ancestors limit) events (afterRead response)
  sameEvents path filePath ancestors limit events response execution = Map.forward afterRead execution

  noExtraEvents : ∀ path filePath ancestors limit events result →
    FS.Runs (readNamed path filePath ancestors limit) events result →
    Σ (FS.Result (Maybe (Raw.Read limit))) (λ response →
      FS.Runs (Raw.readNamed path filePath ancestors limit) events response × afterRead response ≡ result)
  noExtraEvents path filePath ancestors limit events result execution =
    Map.backward afterRead (Raw.readNamed path filePath ancestors limit) execution

  decodedFailure : ∀ {limit} (raw : Raw.Read limit) reply exact error →
    reply ≡ Flow.ordinary (Flow.F.failure error) →
    decoded raw reply exact ≡ returned (inj₁ FS.invalidReport)
  decodedFailure raw reply exact error refl = refl

  failedDecodeIsInvalid : ∀ {limit} (raw : Raw.Read limit) error →
    (exact : Flow.Productive.result (decode (Raw.Read.bytes raw)) ≡ Flow.ordinary (Flow.F.failure error)) →
    afterRead (inj₂ (just raw)) ≡ returned (inj₁ FS.invalidReport)
  failedDecodeIsInvalid raw error exact =
    decodedFailure raw (Flow.Productive.result (decode (Raw.Read.bytes raw))) refl error exact

  decodedOrigin : ∀ {limit} (raw : Raw.Read limit) reply exact accepted →
    decoded raw reply exact ≡ returned (inj₂ (just accepted)) → Loaded.raw accepted ≡ raw
  decodedOrigin raw (Flow.ordinary (Flow.F.success value position)) exact accepted refl = refl

  successfulReadOrigin : ∀ {limit} (response : FS.Result (Maybe (Raw.Read limit))) accepted →
    afterRead response ≡ returned (inj₂ (just accepted)) →
    response ≡ inj₂ (just (Loaded.raw accepted))
  successfulReadOrigin (inj₂ (just raw)) accepted observed =
    cong (λ raw → inj₂ (just raw))
      (sym (decodedOrigin raw (Flow.Productive.result (decode (Raw.Read.bytes raw))) refl accepted observed))

  successRequiresRawRead : ∀ path filePath ancestors limit events accepted →
    FS.Runs (readNamed path filePath ancestors limit) events (returned (inj₂ (just accepted))) →
    FS.Runs (Raw.readNamed path filePath ancestors limit) events (inj₂ (just (Loaded.raw accepted)))
  successRequiresRawRead path filePath ancestors limit events accepted execution
    with noExtraEvents path filePath ancestors limit events (returned (inj₂ (just accepted))) execution
  ... | response , original , exact =
    subst (FS.Runs (Raw.readNamed path filePath ancestors limit) events)
      (successfulReadOrigin response accepted exact) original
