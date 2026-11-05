{-# OPTIONS --safe #-}
-- Release policy. Git supplies whether the exact selected commit is already
-- in main's history. Manual branch builds produce build artifacts only.
module Mimir.ReleaseSource where

open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Request : Set where
  pushedVersionTag manualVersionTag manualBranch unsupported : Request

data Decision : Set where refused artifacts release : Decision

data VersionTag : Request → Set where
  pushed : VersionTag pushedVersionTag
  manual : VersionTag manualVersionTag

data Compiles : Decision → Set where
  buildArtifacts : Compiles artifacts
  buildRelease : Compiles release

decide : Request → Bool → Decision
decide pushedVersionTag true = release
decide pushedVersionTag false = refused
decide manualVersionTag true = release
decide manualVersionTag false = refused
decide manualBranch onMain = artifacts
decide unsupported onMain = refused

releaseRequiresMain : ∀ request onMain → decide request onMain ≡ release → onMain ≡ true
releaseRequiresMain pushedVersionTag true accepted = refl
releaseRequiresMain pushedVersionTag false ()
releaseRequiresMain manualVersionTag true accepted = refl
releaseRequiresMain manualVersionTag false ()
releaseRequiresMain manualBranch onMain ()
releaseRequiresMain unsupported onMain ()

automaticBuildRequiresMain : ∀ onMain → Compiles (decide pushedVersionTag onMain) → onMain ≡ true
automaticBuildRequiresMain true build = refl
automaticBuildRequiresMain false ()

offMainTagRefused : ∀ request → VersionTag request → decide request false ≡ refused
offMainTagRefused pushedVersionTag pushed = refl
offMainTagRefused manualVersionTag manual = refl

mainTagReleased : ∀ request → VersionTag request → decide request true ≡ release
mainTagReleased pushedVersionTag pushed = refl
mainTagReleased manualVersionTag manual = refl

releaseRequiresTag : ∀ request onMain → decide request onMain ≡ release → VersionTag request
releaseRequiresTag pushedVersionTag onMain accepted = pushed
releaseRequiresTag manualVersionTag onMain accepted = manual
releaseRequiresTag manualBranch onMain ()
releaseRequiresTag unsupported onMain ()

manualBuildAvailable : ∀ onMain → decide manualBranch onMain ≡ artifacts
manualBuildAvailable onMain = refl

unsupportedRefused : ∀ onMain → decide unsupported onMain ≡ refused
unsupportedRefused onMain = refl
