{-# OPTIONS --safe #-}
-- Mimir's two-layer parameter escaping and prepared-statement lifetime.
-- PREPARE failure has no DEALLOCATE; every returned EXECUTE outcome has one.
module Mimir.AgeQueryProtocol where

open import Data.Char using (Char; toℕ; fromℕ)
open import Data.List using (List; []; _∷_; _++_; concatMap)
open import Data.Nat using (ℕ; _+_; _<?_)
open import Data.Nat.DivMod using (_/_; _%_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.String using (toList)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.Effects as Effects

hex : ℕ → Char
hex n with n <? 10
... | yes _ = fromℕ (48 + n)
... | no _ = fromℕ (87 + n)

jsonCharacter : Char → Text
jsonCharacter '\\' = toList "\\\\"
jsonCharacter '"' = toList "\\\""
jsonCharacter '\b' = toList "\\b"
jsonCharacter '\f' = toList "\\f"
jsonCharacter '\n' = toList "\\n"
jsonCharacter '\r' = toList "\\r"
jsonCharacter '\t' = toList "\\t"
jsonCharacter c with toℕ c <? 32
... | yes _ = toList "\\u00" ++ (hex (toℕ c / 16) ∷ hex (toℕ c % 16) ∷ [])
... | no _ = c ∷ []

jsonEscape : Text → Text
jsonEscape = concatMap jsonCharacter

sqlEscape : Text → Text
sqlEscape [] = []
sqlEscape ('\'' ∷ rest) = '\'' ∷ '\'' ∷ sqlEscape rest
sqlEscape (c ∷ rest) = c ∷ sqlEscape rest

module Session (Row : Set) where
  data Message : Set where row : Row → Message; commandComplete : ℕ → Message; other : Message
  data Effect : Set where simpleQuery : ℕ → Text → Effect
  Reply : Effect → Set
  Reply _ = Text ⊎ List Message
  module P = Effects.Protocol Effect Reply
  open P using (Script; done; ask)

  rows : List Message → List Row
  rows [] = []
  rows (row value ∷ rest) = value ∷ rows rest
  rows (commandComplete _ ∷ rest) = rows rest
  rows (other ∷ rest) = rows rest

  afterPrepare : ℕ → Text → Text → Text ⊎ List Message → Script (Text ⊎ List Row)
  afterPrepare connection name parameters (inj₁ error) = done (inj₁ error)
  afterPrepare connection name parameters (inj₂ _) = ask
    (simpleQuery connection (toList "EXECUTE " ++ name ++ toList "('" ++ sqlEscape parameters ++ toList "')"))
    (λ result → ask (simpleQuery connection (toList "DEALLOCATE " ++ name)) (λ _ → finish result))
    where
    finish : Text ⊎ List Message → Script (Text ⊎ List Row)
    finish (inj₁ error) = done (inj₁ error)
    finish (inj₂ messages) = done (inj₂ (rows messages))

  query : ℕ → Text → Text → Text → Script (Text ⊎ List Row)
  query connection name prepare parameters = ask (simpleQuery connection prepare) (afterPrepare connection name parameters)

  execute : ℕ → Text → Text → Text → Script (Text ⊎ ⊤)
  execute connection name prepare parameters = P._>>=_ (query connection name prepare parameters) λ where
    (inj₁ error) → done (inj₁ error)
    (inj₂ _) → done (inj₂ tt)

  failedPreparationStops : ∀ connection name parameters error →
    afterPrepare connection name parameters (inj₁ error) ≡ done (inj₁ error)
  failedPreparationStops connection name parameters error = refl
