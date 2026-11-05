{-# OPTIONS --safe #-}
-- Exact state-path selection precedence and environment requests. Environment
-- values are OS bytes, including present empty and non-UTF-8 strings. A cwd
-- success carries its native absolute-path contract as explicit input evidence.
module Mimir.JudgeStatePath where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; _<?_)
open import Data.Fin using (fromℕ<)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Bits using (Byte)
open import Mimir.UnixPath using (Path; absolute; join)
open import Mimir.UnixPathLaws using (Absolute; joinAbsolute)
open import Mimir.UnixPathParts using (NoParent; noParent?)
import Mimir.Effects as E

byte : (value : ℕ) → True (value <? 256) → Byte
byte value valid = fromℕ< (toWitness valid)

mimir : Path
mimir = byte 109 tt ∷ byte 105 tt ∷ byte 109 tt ∷ byte 105 tt ∷ byte 114 tt ∷ []

localState : Path
localState = byte 46 tt ∷ byte 108 tt ∷ byte 111 tt ∷ byte 99 tt ∷ byte 97 tt ∷ byte 108 tt ∷
  byte 47 tt ∷ byte 115 tt ∷ byte 116 tt ∷ byte 97 tt ∷ byte 116 tt ∷ byte 101 tt ∷ byte 47 tt ∷ mimir

record Resolved : Set where
  constructor resolved
  field path : Path; rooted : Absolute path; noParent : NoParent path

module With (NativeError : Set) where
  data Variable : Set where xdgStateHome home : Variable
  data Operation : Set where environment : Variable → Operation; currentDirectory : Operation

  Reply : Operation → Set
  Reply (environment _) = Maybe Path
  Reply currentDirectory = NativeError ⊎ Σ Path Absolute

  open E.Protocol Operation Reply public

  data Error : Set where xdgRelative homeUnset parentComponent : Error; currentDirectoryFailed : NativeError → Error
  Result = Error ⊎ Resolved

  checkParents : (path : Path) → Absolute path → Result
  checkParents path rooted with noParent? path
  ... | no _ = inj₁ parentComponent
  ... | yes valid = inj₂ (resolved path rooted valid)

  fromCwd : Path → Reply currentDirectory → Script Result
  fromCwd selected (inj₁ error) = done (inj₁ (currentDirectoryFailed error))
  fromCwd selected (inj₂ (cwd , rooted)) =
    done (checkParents (join cwd selected) (joinAbsolute cwd selected rooted))

  absolutize : Path → Script Result
  absolutize selected with absolute selected in observed
  ... | true = done (checkParents selected observed)
  ... | false = ask currentDirectory (fromCwd selected)

  fromHome : Maybe Path → Script Result
  fromHome nothing = done (inj₁ homeUnset)
  fromHome (just base) = absolutize (join base localState)

  fromXdg : Maybe Path → Script Result
  fromXdg nothing = ask (environment home) fromHome
  fromXdg (just base) with absolute base
  ... | false = done (inj₁ xdgRelative)
  ... | true = absolutize (join base mimir)

  resolve : Maybe Path → Script Result
  resolve (just explicit) = absolutize explicit
  resolve nothing = ask (environment xdgStateHome) fromXdg

  explicitPrecedence : ∀ explicit → resolve (just explicit) ≡ absolutize explicit
  explicitPrecedence explicit = refl

  missingHomeStops : ∀ events result → Runs (fromHome nothing) events result →
    events ≡ [] Data.Product.× result ≡ inj₁ homeUnset
  missingHomeStops events result (returned _) = refl , refl

  checkParentsExact : ∀ path rooted result → checkParents path rooted ≡ inj₂ result → Resolved.path result ≡ path
  checkParentsExact path rooted result receipt with noParent? path
  ... | no _ with receipt
  ...   | ()
  checkParentsExact path rooted result receipt | yes valid with receipt
  ... | refl = refl
