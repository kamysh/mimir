{-# OPTIONS --safe #-}
-- Entropy acquisition and UUID construction are standard-library operations.
-- Mimir may observe acquisition failure and must never assume UUID freshness.
module Mimir.UUIDV4 where

open import Data.Bool using (Bool; true; false)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Mimir.UUIDGroups using (UUID)
import Mimir.StandardLibrary as Library
import Mimir.Effects as Effects

data Endian : Set where littleEndian bigEndian : Endian

little : Endian → Bool
little littleEndian = true
little bigEndian = false

fromRandom : Library.Contract → Endian → UUID → UUID
fromRandom library endian = Library.Contract.uuidFromRandom library (little endian)

module With (library : Library.Contract) (RandomError : Set) where
  data Request : Set where randomBytes16 : Request

  Reply : Request → Set
  Reply randomBytes16 = RandomError ⊎ UUID
  module P = Effects.Protocol Request Reply

  data Outcome : Set where
    panicked : RandomError → Outcome
    generated : UUID → Outcome

  accept : Endian → Reply randomBytes16 → Outcome
  accept endian (inj₁ error) = panicked error
  accept endian (inj₂ bytes) = generated (fromRandom library endian bytes)

  generate : Endian → P.Script Outcome
  generate endian = P.ask randomBytes16 (λ response → P.done (accept endian response))
