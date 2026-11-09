{-# OPTIONS --safe #-}
-- Observable configuration file protocol. Replies represent actual external
-- outcomes; partial writes remain private and success is never inferred from an
-- attempted write. TOML syntax and typed configuration validation are separate.
module Mimir.ConfigurationIO where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (String)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import Data.Unit using (⊤; tt)
import Mimir.Recovery as Recovery

data Platform : Set where unix other : Platform
data Failure : Set where
  alreadyExists directoryFailure permissionFailure createFailure : Failure
  partialWrite fileSync publishFailure directorySync missingFile unreadable invalidTOML : Failure

-- Creation effects operate on an owned temporary file in the same directory.
-- linkTarget uses create-if-absent publication; there is no overwrite effect.
data Effect : Set where
  checkExists makePrivateParents createExclusive0600 : Effect
  createExclusive writeAll syncFile linkTarget syncDirectory readUTF8 decodeTOML : Effect

data Result : Set where success : Result; failed : Failure → Result
data State : Set where
  initial checking making creating writing syncingFile publishing syncingDirectory : State
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
afterAbsence (settings platform true) = next making (makePrivateParents ∷ [])
afterAbsence (settings platform false) = next creating (createEffect platform ∷ [])

afterParents : Platform → Step
afterParents unix = next creating (createExclusive0600 ∷ [])
afterParents other = next creating (createExclusive ∷ [])

step : Settings → State → Input → Step
step cfg initial begin = next checking (checkExists ∷ [])
step cfg checking exists = next (finished (failed alreadyExists)) []
step cfg checking absent = afterAbsence cfg
step cfg checking error = next (finished (failed unreadable)) []
step cfg making ok = afterParents (platform cfg)
step cfg making error = next (finished (failed directoryFailure)) []
-- A temporary-path collision never removes a file owned by somebody else.
step cfg creating exists = next (finished (failed alreadyExists)) []
step cfg creating error = next (finished (failed createFailure)) []
step cfg creating ok = next writing (writeAll ∷ [])
step cfg writing ok = next syncingFile (syncFile ∷ [])
step cfg writing error = next (finished (failed partialWrite)) []
step cfg syncingFile ok = next publishing (linkTarget ∷ [])
step cfg syncingFile error = next (finished (failed fileSync)) []
step cfg publishing exists = next (finished (failed alreadyExists)) []
step cfg publishing error = next (finished (failed publishFailure)) []
step cfg publishing ok = next syncingDirectory (syncDirectory ∷ [])
step cfg syncingDirectory ok = next (finished success) []
step cfg syncingDirectory error = next (finished (failed directorySync)) []
step cfg state input = next state []

-- Final states absorb late, duplicate, and irrelevant input.
finishedStable : ∀ cfg result input →
  step cfg (finished result) input ≡ next (finished result) []
finishedStable cfg result input = refl

existingFileUntouched : ∀ cfg →
  step cfg checking exists ≡ next (finished (failed alreadyExists)) []
existingFileUntouched cfg = refl

raceCannotOverwrite : ∀ cfg →
  step cfg publishing exists ≡ next (finished (failed alreadyExists)) []
raceCannotOverwrite cfg = refl

-- Success requires a complete, synced private file to have been published
-- without replacing the selected target. No write can expose a partial target.
successRequiresPublication : ∀ cfg before input →
  state (step cfg before input) ≡ finished success →
  (before ≡ syncingDirectory × input ≡ ok) Data.Sum.⊎ (before ≡ finished success)
successRequiresPublication cfg initial begin ()
successRequiresPublication cfg initial exists ()
successRequiresPublication cfg initial absent ()
successRequiresPublication cfg initial ok ()
successRequiresPublication cfg initial error ()
successRequiresPublication cfg checking begin ()
successRequiresPublication cfg checking exists ()
successRequiresPublication (settings platform true) checking absent ()
successRequiresPublication (settings platform false) checking absent ()
successRequiresPublication cfg checking ok ()
successRequiresPublication cfg checking error ()
successRequiresPublication cfg making begin ()
successRequiresPublication cfg making exists ()
successRequiresPublication cfg making absent ()
successRequiresPublication (settings unix parent) making ok ()
successRequiresPublication (settings other parent) making ok ()
successRequiresPublication cfg making error ()
successRequiresPublication cfg creating begin ()
successRequiresPublication cfg creating exists ()
successRequiresPublication cfg creating absent ()
successRequiresPublication cfg creating ok ()
successRequiresPublication cfg creating error ()
successRequiresPublication cfg writing begin ()
successRequiresPublication cfg writing exists ()
successRequiresPublication cfg writing absent ()
successRequiresPublication cfg writing ok ()
successRequiresPublication cfg writing error ()
successRequiresPublication cfg syncingFile begin ()
successRequiresPublication cfg syncingFile exists ()
successRequiresPublication cfg syncingFile absent ()
successRequiresPublication cfg syncingFile ok ()
successRequiresPublication cfg syncingFile error ()
successRequiresPublication cfg publishing begin ()
successRequiresPublication cfg publishing exists ()
successRequiresPublication cfg publishing absent ()
successRequiresPublication cfg publishing ok ()
successRequiresPublication cfg publishing error ()
successRequiresPublication cfg syncingDirectory begin ()
successRequiresPublication cfg syncingDirectory exists ()
successRequiresPublication cfg syncingDirectory absent ()
successRequiresPublication cfg syncingDirectory ok proof = inj₁ (refl , refl)
successRequiresPublication cfg syncingDirectory error ()
successRequiresPublication cfg (finished success) input proof = inj₂ refl
successRequiresPublication cfg (finished (failed failure)) input ()

-- Error rendering has no source-text argument. Different secret-bearing
-- contents produce the same externally visible error at the same failure.
renderFailure : Failure → String
renderFailure alreadyExists = "config already exists"
renderFailure directoryFailure = "cannot create config directory"
renderFailure permissionFailure = "cannot set private config permissions"
renderFailure createFailure = "cannot create config"
renderFailure partialWrite = "unable to finish writing config"
renderFailure fileSync = "unable to sync private config"
renderFailure publishFailure = "unable to publish config without replacement"
renderFailure directorySync = "config is complete but directory durability is uncertain; read it back and retry"
renderFailure missingFile = "no config file found; run mimir init"
renderFailure unreadable = "unable to read Mimir config"
renderFailure invalidTOML = "invalid Mimir config TOML"

renderReadFailure : String → Failure → String
renderReadFailure contents failure = renderFailure failure

diagnosticIndependentOfSecrets : ∀ first second failure →
  renderReadFailure first failure ≡ renderReadFailure second failure
diagnosticIndependentOfSecrets first second failure = refl

-- The file payload is a COMPLETE byte sequence prepared and synced privately.
-- Atomic link publication either preserves an existing mapping or installs
-- that whole payload. Other files/settings are retained as an arbitrary frame.
-- Temporary preparation may stop at any point without changing this world.
module Publication (Payload Frame : Set) where
  record World : Set where
    constructor world
    field target : Maybe Payload; others : Frame

  intended : Payload → World → World
  intended requested (world nothing frame) = world (just requested) frame
  intended requested before@(world (just existing) frame) = before

  -- Request matching is separate from file publication: a conflicting complete
  -- file is never replaced merely because a caller asked for different fields.
  existingPreserved : ∀ requested existing frame →
    intended requested (world (just existing) frame) ≡ world (just existing) frame
  existingPreserved requested existing frame = refl

  framePreserved : ∀ requested before →
    World.others (intended requested before) ≡ World.others before
  framePreserved requested (world nothing frame) = refl
  framePreserved requested (world (just existing) frame) = refl

  retryIdempotent : ∀ requested before →
    intended requested (intended requested before) ≡ intended requested before
  retryIdempotent requested (world nothing frame) = refl
  retryIdempotent requested (world (just existing) frame) = refl

  -- Use the shared interruption relation, which includes every script prefix
  -- and a physical publication whose acknowledgement was lost. Preparation
  -- leaves the selected target and other files unchanged; link is atomic.
  data PublicationEffect : Set where preparePrivate publishAbsent : PublicationEffect
  PublicationReply : PublicationEffect → Set
  PublicationReply _ = ⊤

  module Run (requested : Payload) where
    data Atomic : World → PublicationEffect → ⊤ → World → Set where
      prepared : ∀ before → Atomic before preparePrivate tt before
      published : ∀ before → Atomic before publishAbsent tt (intended requested before)
    module X = Recovery.Execution World PublicationEffect PublicationReply Atomic
    module E = X.E

    script : E.Script ⊤
    script = E.ask preparePrivate (λ _ → E.ask publishAbsent (λ _ → E.done tt))

    unchangedIntent : ∀ before effect reply after → Atomic before effect reply after →
      intended requested after ≡ intended requested before
    unchangedIntent before .preparePrivate .tt .before (prepared .before) = refl
    unchangedIntent before .publishAbsent .tt .(intended requested before) (published .before) =
      retryIdempotent requested before

    changesPreserveIntent : ∀ before events after → X.Changes before events after →
      intended requested after ≡ intended requested before
    changesPreserveIntent before .[] .before (X.unchanged .before) = refl
    changesPreserveIntent before _ after (X.changed .before effect reply middle physical rest) =
      trans (changesPreserveIntent middle _ after rest) (unchangedIntent before effect reply middle physical)

    interruptionPreservesIntent : ∀ before after → X.Interrupted script before after →
      intended requested after ≡ intended requested before
    interruptionPreservesIntent before after (X.atPrefix events residual .after prefix physical) =
      changesPreserveIntent before events after physical
    interruptionPreservesIntent before after (X.beforeReply events effect continuation current reply .after prefix physical publication) =
      trans (unchangedIntent current effect reply after publication) (changesPreserveIntent before events current physical)

    completionPublishesCompleteFile : ∀ before after reply → X.Completed script before after reply →
      after ≡ intended requested before
    completionPublishesCompleteFile before .(intended requested before) .tt
      (X.completed _ (E.replied _ _ tt (E.replied _ _ tt (E.returned tt)))
        (X.changed _ _ _ _ (prepared _) (X.changed _ _ _ _ (published _) (X.unchanged _)))) = refl

    completedRetryConverges : ∀ before interrupted after reply →
      X.Interrupted script before interrupted → X.Completed script interrupted after reply →
      after ≡ intended requested before
    completedRetryConverges before interrupted after reply interruption completion =
      trans (completionPublishesCompleteFile interrupted after reply completion)
        (interruptionPreservesIntent before interrupted interruption)

    -- This file-publication certificate is available to application assembly;
    -- the same shared convergence/progress fields are mandatory here too.
    intent : Recovery.Outcome.Intent World ⊤ ⊤
    intent = record
      { intended = λ _ before → intended requested before
      ; expectedReply = λ _ _ → tt }

    recoverable : Recovery.Recoverable World ⊤
    recoverable = record
      { Result = ⊤
      ; Effect = PublicationEffect
      ; Reply = PublicationReply
      ; script = λ _ → script
      ; Atomic = Atomic
      ; intent = intent
      ; converges = λ _ before interrupted after reply interruption completion →
          cong (λ current → current , tt)
            (completedRetryConverges before interrupted after reply interruption completion)
      ; progress = λ _ before → intended requested before , tt ,
          X.completed ((preparePrivate , tt) ∷ (publishAbsent , tt) ∷ [])
            (E.replied preparePrivate _ tt (E.replied publishAbsent _ tt (E.returned tt)))
            (X.changed before preparePrivate tt before (prepared before)
              (X.changed before publishAbsent tt (intended requested before) (published before)
                (X.unchanged (intended requested before)))) }
