{-# OPTIONS --safe #-}
-- Observable configuration file protocol. Replies represent actual external
-- outcomes, including partial writes; success is never inferred from an
-- attempted write. TOML syntax and typed configuration validation are separate.
module Mimir.ConfigurationIO where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Platform : Set where unix other : Platform
data Failure : Set where
  alreadyExists directoryFailure permissionFailure createFailure : Failure
  partialWrite missingFile unreadable invalidTOML : Failure

-- The host resolves these requests against the selected path. createExclusive
-- is the create_new/open-with-O_EXCL operation; there is no overwrite effect.
data Effect : Set where
  checkExists makeParents setParent0700 createExclusive0600 : Effect
  createExclusive writeAll readUTF8 decodeTOML : Effect

data Result : Set where success : Result; failed : Failure → Result
data State : Set where
  initial checking making securing creating writing : State
  finished : Result → State

data Input : Set where
  begin exists absent ok error : Input

record Settings : Set where
  constructor settings
  field platform : Platform; hasParent : Bool
open Settings

record Step : Set where
  constructor next
  field state : State; effects : List Effect
open Step

createEffect : Platform → Effect
createEffect unix = createExclusive0600
createEffect other = createExclusive

afterAbsence : Settings → Step
afterAbsence (settings platform true) = next making (makeParents ∷ [])
afterAbsence (settings platform false) = next creating (createEffect platform ∷ [])

afterParents : Platform → Step
afterParents unix = next securing (setParent0700 ∷ [])
afterParents other = next creating (createExclusive ∷ [])

step : Settings → State → Input → Step
step cfg initial begin = next checking (checkExists ∷ [])
step cfg checking exists = next (finished (failed alreadyExists)) []
step cfg checking absent = afterAbsence cfg
step cfg checking error = next (finished (failed unreadable)) []
step cfg making ok = afterParents (platform cfg)
step cfg making error = next (finished (failed directoryFailure)) []
step cfg securing ok = next creating (createEffect (platform cfg) ∷ [])
step cfg securing error = next (finished (failed permissionFailure)) []
-- A race after the existence check still cannot overwrite the file.
step cfg creating exists = next (finished (failed alreadyExists)) []
step cfg creating error = next (finished (failed createFailure)) []
step cfg creating ok = next writing (writeAll ∷ [])
step cfg writing ok = next (finished success) []
step cfg writing error = next (finished (failed partialWrite)) []
step cfg state input = next state []

-- Final states absorb late, duplicate, and irrelevant input.
finishedStable : ∀ cfg result input →
  step cfg (finished result) input ≡ next (finished result) []
finishedStable cfg result input = refl

existingFileUntouched : ∀ cfg →
  step cfg checking exists ≡ next (finished (failed alreadyExists)) []
existingFileUntouched cfg = refl

raceCannotOverwrite : ∀ cfg →
  step cfg creating exists ≡ next (finished (failed alreadyExists)) []
raceCannotOverwrite cfg = refl

-- Successful completion requires a successful write response. This theorem
-- checks every state and every input, not just the successful happy path.
successRequiresWrite : ∀ cfg before input →
  state (step cfg before input) ≡ finished success →
  (before ≡ writing × input ≡ ok) Data.Sum.⊎ (before ≡ finished success)
successRequiresWrite cfg initial begin ()
successRequiresWrite cfg initial exists ()
successRequiresWrite cfg initial absent ()
successRequiresWrite cfg initial ok ()
successRequiresWrite cfg initial error ()
successRequiresWrite cfg checking begin ()
successRequiresWrite cfg checking exists ()
successRequiresWrite (settings platform true) checking absent ()
successRequiresWrite (settings platform false) checking absent ()
successRequiresWrite cfg checking ok ()
successRequiresWrite cfg checking error ()
successRequiresWrite cfg making begin ()
successRequiresWrite cfg making exists ()
successRequiresWrite cfg making absent ()
successRequiresWrite (settings unix parent) making ok ()
successRequiresWrite (settings other parent) making ok ()
successRequiresWrite cfg making error ()
successRequiresWrite cfg securing begin ()
successRequiresWrite cfg securing exists ()
successRequiresWrite cfg securing absent ()
successRequiresWrite cfg securing ok ()
successRequiresWrite cfg securing error ()
successRequiresWrite cfg creating begin ()
successRequiresWrite cfg creating exists ()
successRequiresWrite cfg creating absent ()
successRequiresWrite cfg creating ok ()
successRequiresWrite cfg creating error ()
successRequiresWrite cfg writing begin ()
successRequiresWrite cfg writing exists ()
successRequiresWrite cfg writing absent ()
successRequiresWrite cfg writing ok proof = inj₁ (refl , refl)
successRequiresWrite cfg writing error ()
successRequiresWrite cfg (finished success) input proof = inj₂ refl
successRequiresWrite cfg (finished (failed failure)) input ()

-- Error rendering has no source-text argument. Different secret-bearing
-- contents produce the same externally visible error at the same failure.
renderFailure : Failure → String
renderFailure alreadyExists = "config already exists"
renderFailure directoryFailure = "cannot create config directory"
renderFailure permissionFailure = "cannot set private config permissions"
renderFailure createFailure = "cannot create config"
renderFailure partialWrite = "unable to finish writing config"
renderFailure missingFile = "no config file found; run mimir init"
renderFailure unreadable = "unable to read Mimir config"
renderFailure invalidTOML = "invalid Mimir config TOML"

renderReadFailure : String → Failure → String
renderReadFailure contents failure = renderFailure failure

diagnosticIndependentOfSecrets : ∀ first second failure →
  renderReadFailure first failure ≡ renderReadFailure second failure
diagnosticIndependentOfSecrets first second failure = refl
