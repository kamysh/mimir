{-# OPTIONS --safe #-}
-- Configuration lifecycle: complete private publication and explicit-field
-- readback on retries. Existing valid settings are never overwritten. TOML parsing/printing and OS path interpretation remain
-- standard dependency boundaries; schema and override semantics are concrete.
module Mimir.ConfigurationProtocol where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)
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
  alreadyConfigured : Schema.Config → Content

data Failure : Set where
  file : IO.Failure → Failure
  override : Input.Error → Failure
  validation : Validation.Fault → Failure
  editorLaunch conflictingSettings : Failure

-- Matching is about the fields explicitly named by this request. A custom
-- field omitted from that request does not become a conflict with a default.
-- Values remain typed; neither rendering nor parsing is part of this view.
data FieldValue : Set where
  textField : Text → FieldValue
  optionalTextField : Maybe Text → FieldValue
  portField : ℕ → FieldValue
  modeField : Values.Mode → FieldValue
  backendField : Maybe Values.Backend → FieldValue
  retiredField : FieldValue

embeddingBackend : Maybe Values.Embeddings → Maybe Values.Backend
embeddingBackend nothing = nothing
embeddingBackend (just value) = just (Values.Embeddings.backend value)
embeddingModel : Maybe Values.Embeddings → Maybe Text
embeddingModel nothing = nothing
embeddingModel (just value) = just (Values.Embeddings.model value)
embeddingKey : Maybe Values.Embeddings → Maybe Text
embeddingKey nothing = nothing
embeddingKey (just value) = Values.Embeddings.apiKey value
embeddingCache : Maybe Values.Embeddings → Maybe Text
embeddingCache nothing = nothing
embeddingCache (just value) = Values.Embeddings.cacheDirectory value

fieldValue : Input.Key → Values.Config → FieldValue
fieldValue Input.hostKey cfg = textField (Values.Database.host (Values.Config.db cfg))
fieldValue Input.portKey cfg = portField (Values.Database.port (Values.Config.db cfg))
fieldValue Input.databaseKey cfg = textField (Values.Database.dbname (Values.Config.db cfg))
fieldValue Input.userKey cfg = textField (Values.Database.user (Values.Config.db cfg))
fieldValue Input.passwordKey cfg = optionalTextField (Values.Database.password (Values.Config.db cfg))
fieldValue Input.passfileKey cfg = optionalTextField (Values.Database.pgpassfile (Values.Config.db cfg))
fieldValue Input.modeKey cfg = modeField (Values.Database.mode (Values.Config.db cfg))
fieldValue Input.rootKey cfg = optionalTextField (Values.Database.rootCertificate (Values.Config.db cfg))
fieldValue Input.certificateKey cfg = optionalTextField (Values.Database.clientCertificate (Values.Config.db cfg))
fieldValue Input.clientKeyKey cfg = optionalTextField (Values.Database.clientKey (Values.Config.db cfg))
fieldValue Input.backendKey cfg = backendField (embeddingBackend (Values.Config.embed cfg))
fieldValue Input.modelKey cfg = optionalTextField (embeddingModel (Values.Config.embed cfg))
fieldValue Input.apiKeyKey cfg = optionalTextField (embeddingKey (Values.Config.embed cfg))
fieldValue Input.batchKey cfg = retiredField
fieldValue Input.cacheKey cfg = optionalTextField (embeddingCache (Values.Config.embed cfg))

namedField : String → Values.Config → Maybe FieldValue
namedField name cfg with Input.lookup name Input.keys
... | nothing = nothing
... | just key = just (fieldValue key cfg)

explicitFields : List (String × Text) → Values.Config → List (Maybe FieldValue)
explicitFields pairs cfg = map (λ pair → namedField (Data.Product.proj₁ pair) cfg) pairs

data Effect : Set where
  defaultOperations : Effect
  exists : Path.Path → Effect
  readUTF8 : Path.Path → Effect
  parseTOML : Text → Effect
  prettyTOML : Values.Config → Effect
  filesystem : Path.Path → Content → IO.Effect → Effect
  sameFields : List (String × Text) → Values.Config → Values.Config → Effect
  announceCreated announceAlreadyConfigured : Path.Path → Effect
  announceEditor announceRestart : Effect
  editor : Text → Path.Path → Effect

Reply : Effect → Set
Reply defaultOperations = IO.Failure ⊎ Operations.Admitted
Reply (exists _) = Bool
Reply (readUTF8 _) = IO.Failure ⊎ Text
Reply (parseTOML _) = IO.Failure ⊎ V.Value
Reply (prettyTOML _) = IO.Failure ⊎ Text
Reply (filesystem _ _ _) = IO.Input
Reply (sameFields pairs old proposed) = Dec (explicitFields pairs old ≡ explicitFields pairs proposed)
Reply (announceCreated _) = ⊤
Reply (announceAlreadyConfigured _) = ⊤
Reply announceEditor = ⊤
Reply announceRestart = ⊤
-- A child exit status, including nonzero, is a successful status() result.
Reply (editor _ _) = Bool ⊎ ℕ

module P = Effects.Protocol Effect Reply
open P using (Script; done; ask; _>>=_)

module Run where
  module Decode = Schema.Decode

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

  -- IO's finite transition system owns write ordering. A driver may execute
  -- only the effect emitted by that system, with this path and this content.
  record FileState : Set where
    constructor writing
    field state : IO.State; pending : List IO.Effect

  initialWrite : IO.Settings → FileState
  initialWrite writeSettings with IO.afterAbsence writeSettings
  ... | IO.next state effects = writing state effects

  advanceWrite : IO.Settings → FileState → IO.Input → FileState
  advanceWrite writeSettings (writing state pending) reply with IO.step writeSettings state reply
  ... | IO.next next effects = writing next effects

  data WriteRun (writeSettings : IO.Settings) (path : Path.Path) (content : Content) :
    FileState → List P.Event → IO.Result → Set where
    finished : ∀ result → WriteRun writeSettings path content (writing (IO.finished result) []) [] result
    response : ∀ state effect reply events result →
      WriteRun writeSettings path content (advanceWrite writeSettings (writing state (effect ∷ [])) reply) events result →
      WriteRun writeSettings path content (writing state (effect ∷ []))
        ((filesystem path content effect , reply) ∷ events) result

  data NewContent : Content → Set where
    template : ∀ operations → NewContent (template operations)
    configured : ∀ operations config → NewContent (configured operations config)

  module Creation (parser : Unsigned.Parser) where
    module Overrides = Input.Read parser

    -- New files are prepared privately and linked into an absent target.
    -- A retry reads/validates the existing complete file and compares only
    -- explicit overrides, applied to that file rather than to defaults.
    afterCheck : Operations.Admitted → List (String × Text) → Script (Failure ⊎ Content)
    afterCheck operations [] = done (inj₂ (template operations))
    afterCheck operations pairs@(_ ∷ _) with Overrides.create pairs
    ... | inj₁ error = done (inj₁ (override error))
    ... | inj₂ configurationValue = ask (prettyTOML configurationValue) λ where
      (inj₁ error) → done (inj₁ (file error))
      (inj₂ _) → done (inj₂ (configured operations configurationValue))

    compareExisting : Schema.Config → List (String × Text) → Script (Failure ⊎ Content)
    compareExisting current pairs with Overrides.create pairs
    ... | inj₁ error = done (inj₁ (override error))
    ... | inj₂ proposed = ask (sameFields pairs (Schema.Config.core current) proposed) λ where
      (yes same) → done (inj₂ (alreadyConfigured current))
      (no different) → done (inj₁ conflictingSettings)

    -- A file published from this request matches on retry even when its
    -- unrelated sections are retained as opaque values. No override is
    -- reapplied to existing settings to establish that fact.
    createdSettingsMatch : ∀ pairs operations cfg llm judge email retirement →
      Overrides.create pairs ≡ inj₂ cfg →
      P.Runs (compareExisting (Schema.config operations cfg llm judge email retirement) pairs)
        ((sameFields pairs cfg cfg , yes refl) ∷ [])
        (inj₂ (alreadyConfigured (Schema.config operations cfg llm judge email retirement)))
    createdSettingsMatch pairs operations cfg llm judge email retirement created rewrite created =
      P.replied _ _ (yes refl) (P.returned _)

    readExisting : Path.Path → List (String × Text) → Script (Failure ⊎ Content)
    readExisting path pairs = loadFrom path >>= λ where
      (inj₁ error) → done (inj₁ error)
      (inj₂ current) → compareExisting current pairs

    existing : Path.Path → List (String × Text) → Script (Failure ⊎ Content)
    existing path [] = done (inj₁ (file IO.alreadyExists))
    existing path pairs@(_ ∷ _) = readExisting path pairs

    prepare : Path.Path → List (String × Text) → Script (Failure ⊎ Content)
    prepare path pairs = ask (exists path) λ where
      true → existing path pairs
      false → ask defaultOperations λ where
        (inj₁ error) → done (inj₁ (file error))
        (inj₂ operations) → afterCheck operations pairs

    selectEditor : Maybe Text → Text
    selectEditor nothing = toList "vi"
    selectEditor (just value) = value

    afterCreation : Path.Path → Content → Maybe Text → Script (Failure ⊎ ⊤)
    afterCreation path (alreadyConfigured current) editorValue =
      ask (announceAlreadyConfigured path) λ _ → done (inj₂ tt)
    afterCreation path (configured _ _) editorValue = ask (announceCreated path) λ _ →
      ask announceRestart λ _ → done (inj₂ tt)
    afterCreation path (template _) editorValue = ask (announceCreated path) λ _ →
      ask announceEditor λ _ → ask (editor (selectEditor editorValue) path) λ where
        (inj₁ _) → done (inj₁ editorLaunch)
        (inj₂ _) → ask announceRestart λ _ → done (inj₂ tt)


    -- Full create command, including early failure, complete publication and
    -- editor exit handling. The joined trace retains every actual filesystem
    -- response; failed writes never reach the editor or success announcements.
    data Created (writeSettings : IO.Settings) (path : Path.Path)
      (pairs : List (String × Text)) (editorValue : Maybe Text) :
      List P.Event → Failure ⊎ ⊤ → Set where
      existingReady : ∀ prepared current announcements result →
        P.Runs (prepare path pairs) prepared (inj₂ (alreadyConfigured current)) →
        P.Runs (afterCreation path (alreadyConfigured current) editorValue) announcements result →
        Created writeSettings path pairs editorValue (prepared Data.List.++ announcements) result
      racedExisting : ∀ prepared content written checked current announcements result →
        NewContent content →
        P.Runs (prepare path pairs) prepared (inj₂ content) →
        WriteRun writeSettings path content (initialWrite writeSettings) written (IO.failed IO.alreadyExists) →
        P.Runs (readExisting path pairs) checked (inj₂ (alreadyConfigured current)) →
        P.Runs (afterCreation path (alreadyConfigured current) editorValue) announcements result →
        Created writeSettings path pairs editorValue
          (prepared Data.List.++ written Data.List.++ checked Data.List.++ announcements) result
      preparationFailed : ∀ events failure → P.Runs (prepare path pairs) events (inj₁ failure) →
        Created writeSettings path pairs editorValue events (inj₁ failure)
      writeFailed : ∀ prepared content written failure → NewContent content →
        P.Runs (prepare path pairs) prepared (inj₂ content) →
        WriteRun writeSettings path content (initialWrite writeSettings) written (IO.failed failure) →
        Created writeSettings path pairs editorValue (prepared Data.List.++ written) (inj₁ (file failure))
      afterWrite : ∀ prepared content written announcements result → NewContent content →
        P.Runs (prepare path pairs) prepared (inj₂ content) →
        WriteRun writeSettings path content (initialWrite writeSettings) written IO.success →
        P.Runs (afterCreation path content editorValue) announcements result →
        Created writeSettings path pairs editorValue (prepared Data.List.++ written Data.List.++ announcements) result
