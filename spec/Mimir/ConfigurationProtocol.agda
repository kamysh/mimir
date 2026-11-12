{-# OPTIONS --safe #-}
-- Configuration lifecycle with exclusive atomic publication and cleanup.
-- TOML parsing/printing and OS path interpretation remain
-- standard dependency boundaries; schema and override semantics are concrete.
module Mimir.ConfigurationProtocol where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.ConfigurationPath as Path
import Mimir.ConfigurationIO as IO
import Mimir.ConfigurationValues as Values
import Mimir.ConfigurationInput as Input
import Mimir.Unsigned as Unsigned
import Mimir.ConfigurationSchema as Schema
import Mimir.StructuredValue as V
import Mimir.OperationalConfiguration as Operations
import Mimir.Validation as Validation
import Mimir.Effects as Effects

data Content : Set where
  template : Operations.Admitted → Content
  configured : Operations.Admitted → Values.Config → Content

data Failure : Set where
  file : IO.Failure → Failure
  override : Input.Error → Failure
  validation : Validation.Fault → Failure
  editorLaunch : Failure

data Effect : Set where
  defaultOperations : Effect
  exists : Path.Path → Effect
  readUTF8 : Path.Path → Effect
  parseTOML : Text → Effect
  prettyTOML : Values.Config → Effect
  filesystem : Path.Path → Content → IO.Effect → Effect
  replaceConfiguration : Path.Path → Content → Effect
  announceCreated : Path.Path → Effect
  announceEditor announceRestart : Effect
  editor : Text → Path.Path → Effect

Reply : Effect → Set
Reply defaultOperations = IO.Failure ⊎ Operations.Admitted
Reply (exists _) = Bool
Reply (readUTF8 _) = IO.Failure ⊎ Text
Reply (parseTOML _) = IO.Failure ⊎ V.Value
Reply (prettyTOML _) = IO.Failure ⊎ Text
Reply (filesystem _ _ _) = IO.Input
Reply (replaceConfiguration _ _) = IO.Result
Reply (announceCreated _) = ⊤
Reply announceEditor = ⊤
Reply announceRestart = ⊤
-- A child exit status, including nonzero, is a successful status() result.
Reply (editor _ _) = Bool ⊎ ℕ

module P = Effects.Protocol Effect Reply
open P using (Script; done; ask; _>>=_)

module Run (sizeMaximum : ℕ) where
  module Decode = Schema.Decode sizeMaximum

  caseDecoded : Validation.Fault ⊎ Schema.Config → Script (Failure ⊎ Schema.Config)
  caseDecoded (inj₁ fault) = done (inj₁ (validation fault))
  caseDecoded (inj₂ configurationValue) = done (inj₂ configurationValue)

  loadFrom : Path.Path → Script (Failure ⊎ Schema.Config)
  loadFrom path = ask (readUTF8 path) λ where
    (inj₁ _) → done (inj₁ (file IO.unreadable))
    (inj₂ source) → ask (parseTOML source) λ where
      (inj₁ _) → done (inj₁ (file IO.invalidTOML))
      (inj₂ value) → caseDecoded (Decode.decode value)

  load : Path.Path → Script (Failure ⊎ Schema.Config)
  load path = ask (exists path) λ where
    false → done (inj₁ (file IO.missingFile))
    true → loadFrom path

  -- A writer must supply both its native event and the certified atomic
  -- publication. There is no executable partial-write state to resume.
  data WriteRun (writeSettings : IO.Settings) (path : Path.Path) (content : Content) :
    Maybe Content → List P.Event → Maybe Content → IO.Result → Set where
    published : ∀ before reply after →
      IO.Publication content before (IO.resultOf reply) after →
      WriteRun writeSettings path content before
        ((filesystem path content (IO.createEffect (IO.Settings.platform writeSettings)) , reply) ∷ [])
        after (IO.resultOf reply)

  writeReceipt : ∀ writeSettings path content before events after result →
    WriteRun writeSettings path content before events after result →
    IO.Publication content before result after
  writeReceipt writeSettings path content before events after result (published _ reply _ receipt) = receipt

  writeFailureRestoresTarget : ∀ writeSettings path content before events after failure →
    WriteRun writeSettings path content before events after (IO.failed failure) → after ≡ before
  writeFailureRestoresTarget writeSettings path content before events after failure observed =
    IO.Certified.failureLeavesUnchanged Content content before (IO.failed failure) after
      (writeReceipt writeSettings path content before events after (IO.failed failure) observed) (λ ())

  writeSuccessPublishesComplete : ∀ writeSettings path content before events after →
    WriteRun writeSettings path content before events after IO.success → after ≡ just content
  writeSuccessPublishesComplete writeSettings path content before events after observed =
    IO.Certified.successPublishesComplete Content content before IO.success after
      (writeReceipt writeSettings path content before events after IO.success observed) tt

  -- The upgrade prepares a complete validated replacement. TOML rewriting is
  -- external; its write must satisfy this certified publication boundary.
  module Upgrade (path : Path.Path) (content : Content) where
    module Publication = IO.Replacement Content content
    recovery = Publication.recovery

    data Runs : Maybe Content → List P.Event → Maybe Content → IO.Result → Set where
      published : ∀ before result after → Publication.Receipt before result after →
        Runs before ((replaceConfiguration path content , result) ∷ []) after result

    failureRestoresOriginal : ∀ before events after failure →
      Runs before events after (IO.failed failure) → after ≡ before
    failureRestoresOriginal before events after failure (published _ _ _ receipt) =
      Publication.unchanged before (IO.failed failure) after receipt (λ ())

  module Creation (parser : Unsigned.Parser) where
    module Overrides = Input.Read parser sizeMaximum

    data Preparation : Set where
      create : Content → Preparation
      useExisting : Preparation

    -- Creation checks existence before decoding overrides. The actual writer
    -- is the certified WriteRun relation above; it cannot leave a partial file.
    afterCheck : Operations.Admitted → List (String × Text) → Script (Failure ⊎ Content)
    afterCheck operations [] = done (inj₂ (template operations))
    afterCheck operations pairs@(_ ∷ _) with Overrides.create pairs
    ... | inj₁ error = done (inj₁ (override error))
    ... | inj₂ configurationValue = ask (prettyTOML configurationValue) λ where
      (inj₁ error) → done (inj₁ (file error))
      (inj₂ _) → done (inj₂ (configured operations configurationValue))

    prepareAbsent : List (String × Text) → Script (Failure ⊎ Preparation)
    prepareAbsent pairs = ask defaultOperations λ where
      (inj₁ error) → done (inj₁ (file error))
      (inj₂ operations) → afterCheck operations pairs >>= λ where
        (inj₁ error) → done (inj₁ error)
        (inj₂ content) → done (inj₂ (create content))

    afterExists : Path.Path → List (String × Text) → Bool → Script (Failure ⊎ Preparation)
    afterExists path [] true = done (inj₂ useExisting)
    afterExists path (_ ∷ _) true = done (inj₁ (file IO.alreadyExists))
    afterExists path pairs false = prepareAbsent pairs

    prepare : Path.Path → List (String × Text) → Script (Failure ⊎ Preparation)
    prepare path pairs = ask (exists path) (afterExists path pairs)

    selectEditor : Maybe Text → Text
    selectEditor nothing = toList "vi"
    selectEditor (just value) = value

    editExisting : Path.Path → Maybe Text → Script (Failure ⊎ ⊤)
    editExisting path editorValue = ask announceEditor λ _ →
      ask (editor (selectEditor editorValue) path) λ where
        (inj₁ _) → done (inj₁ editorLaunch)
        (inj₂ _) → ask announceRestart λ _ → done (inj₂ tt)

    afterCreation : Path.Path → Content → Maybe Text → Script (Failure ⊎ ⊤)
    afterCreation path (configured _ _) editorValue = ask (announceCreated path) λ _ →
      ask announceRestart λ _ → done (inj₂ tt)
    afterCreation path (template _) editorValue = ask (announceCreated path) λ _ → editExisting path editorValue


    -- Full create command, including early rejection, atomic publication and
    -- editor exit handling. The joined trace retains every actual filesystem
    -- response; failed writes never reach the editor or success announcements.
    data Created (writeSettings : IO.Settings) (path : Path.Path)
      (pairs : List (String × Text)) (editorValue : Maybe Text) :
      List P.Event → Failure ⊎ ⊤ → Set where
      preparationFailed : ∀ events failure → P.Runs (prepare path pairs) events (inj₁ failure) →
        Created writeSettings path pairs editorValue events (inj₁ failure)
      existingOpened : ∀ prepared editing result →
        P.Runs (prepare path pairs) prepared (inj₂ useExisting) →
        P.Runs (editExisting path editorValue) editing result →
        Created writeSettings path pairs editorValue (prepared Data.List.++ editing) result
      writeFailed : ∀ prepared content written failure before after →
        P.Runs (prepare path pairs) prepared (inj₂ (create content)) →
        WriteRun writeSettings path content before written after (IO.failed failure) →
        Created writeSettings path pairs editorValue (prepared Data.List.++ written) (inj₁ (file failure))
      afterWrite : ∀ prepared content written announcements result before after →
        P.Runs (prepare path pairs) prepared (inj₂ (create content)) →
        WriteRun writeSettings path content before written after IO.success →
        P.Runs (afterCreation path content editorValue) announcements result →
        Created writeSettings path pairs editorValue (prepared Data.List.++ written Data.List.++ announcements) result
