{-# OPTIONS --safe #-}
-- Configuration lifecycle, including failures between file creation and a
-- completed write. TOML parsing/printing and OS path interpretation remain
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
Reply (announceCreated _) = ⊤
Reply announceEditor = ⊤
Reply announceRestart = ⊤
-- A child exit status, including nonzero, is a successful status() result.
Reply (editor _ _) = Bool ⊎ ℕ

module P = Effects.Protocol Effect Reply
open P using (Script; done; ask; _>>=_)

module Run (sizeMaximum : ℕ) where
  module Decode = Schema.Decode sizeMaximum
  module Overrides = Input.Read sizeMaximum

  caseDecoded : Validation.Fault ⊎ Schema.Config → Script (Failure ⊎ Schema.Config)
  caseDecoded (inj₁ fault) = done (inj₁ (validation fault))
  caseDecoded (inj₂ config) = done (inj₂ config)

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

  -- IO's finite transition system owns write ordering. A driver may execute
  -- only the effect emitted by that system, with this path and this content.
  record FileState : Set where
    constructor writing
    field state : IO.State; pending : List IO.Effect

  initialWrite : IO.Settings → FileState
  initialWrite settings with IO.afterAbsence settings
  ... | IO.next state effects = writing state effects

  advanceWrite : IO.Settings → FileState → IO.Input → FileState
  advanceWrite settings (writing state pending) reply with IO.step settings state reply
  ... | IO.next next effects = writing next effects

  data WriteRun (settings : IO.Settings) (path : Path.Path) (content : Content) :
    FileState → List P.Event → IO.Result → Set where
    finished : ∀ result → WriteRun settings path content (writing (IO.finished result) []) [] result
    response : ∀ state effect reply events result →
      WriteRun settings path content (advanceWrite settings (writing state (effect ∷ [])) reply) events result →
      WriteRun settings path content (writing state (effect ∷ []))
        ((filesystem path content effect , reply) ∷ events) result

  -- Creation checks existence before decoding overrides. The actual writer
  -- is the WriteRun relation above, preserving O_EXCL and partial-write states.
  afterCheck : Operations.Admitted → List (String × Text) → Script (Failure ⊎ Content)
  afterCheck operations [] = done (inj₂ (template operations))
  afterCheck operations pairs@(_ ∷ _) with Overrides.create pairs
  ... | inj₁ error = done (inj₁ (override error))
  ... | inj₂ config = ask (prettyTOML config) λ where
    (inj₁ error) → done (inj₁ (file error))
    (inj₂ _) → done (inj₂ (configured operations config))

  prepare : Path.Path → List (String × Text) → Script (Failure ⊎ Content)
  prepare path pairs = ask (exists path) λ where
    true → done (inj₁ (file IO.alreadyExists))
    false → ask defaultOperations λ where
      (inj₁ error) → done (inj₁ (file error))
      (inj₂ operations) → afterCheck operations pairs

  selectEditor : Maybe Text → Text
  selectEditor nothing = toList "vi"
  selectEditor (just value) = value

  afterCreation : Path.Path → Content → Maybe Text → Script (Failure ⊎ ⊤)
  afterCreation path (configured _ _) editorValue = ask (announceCreated path) λ _ →
    ask announceRestart λ _ → done (inj₂ tt)
  afterCreation path (template _) editorValue = ask (announceCreated path) λ _ →
    ask announceEditor λ _ → ask (editor (selectEditor editorValue) path) λ where
      (inj₁ _) → done (inj₁ editorLaunch)
      (inj₂ _) → ask announceRestart λ _ → done (inj₂ tt)


  -- Full create command, including early failure, partial file creation and
  -- editor exit handling. The joined trace retains every actual filesystem
  -- response; failed writes never reach the editor or success announcements.
  data Created (settings : IO.Settings) (path : Path.Path)
    (pairs : List (String × Text)) (editorValue : Maybe Text) :
    List P.Event → Failure ⊎ ⊤ → Set where
    preparationFailed : ∀ events failure → P.Runs (prepare path pairs) events (inj₁ failure) →
      Created settings path pairs editorValue events (inj₁ failure)
    writeFailed : ∀ prepared content written failure →
      P.Runs (prepare path pairs) prepared (inj₂ content) →
      WriteRun settings path content (initialWrite settings) written (IO.failed failure) →
      Created settings path pairs editorValue (prepared Data.List.++ written) (inj₁ (file failure))
    afterWrite : ∀ prepared content written announcements result →
      P.Runs (prepare path pairs) prepared (inj₂ content) →
      WriteRun settings path content (initialWrite settings) written IO.success →
      P.Runs (afterCreation path content editorValue) announcements result →
      Created settings path pairs editorValue (prepared Data.List.++ written Data.List.++ announcements) result
