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
import Mimir.Recovery as Recovery
import Data.Empty
import Data.List.Relation.Unary.All
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
  editableExisting : Content

data Failure : Set where
  file : IO.Failure → Failure
  override : Input.Error → Failure
  validation : Validation.Fault → Failure
  editorLaunch conflictingSettings : Failure
  editorUnsuccessful : Text → Failure

-- This is the actual std::process::ExitStatus observation, not an inferred
-- status from attempting to launch a child. The failure description also
-- retains signal/abnormal termination on platforms without an exit code.
data EditorStatus : Set where
  editorSucceeded : EditorStatus
  editorFailed : Text → EditorStatus

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
  existingFile : Path.Path → Effect
  announceCreated announceAlreadyConfigured : Path.Path → Effect
  announceOpeningExisting : Path.Path → Effect
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
Reply (existingFile _) = IO.Failure ⊎ ⊤
Reply (announceCreated _) = ⊤
Reply (announceAlreadyConfigured _) = ⊤
Reply (announceOpeningExisting _) = ⊤
Reply announceEditor = ⊤
Reply announceRestart = ⊤
Reply (editor _ _) = Bool ⊎ EditorStatus

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
    existing path [] = ask (existingFile path) λ where
      (inj₁ failure) → done (inj₁ (file failure))
      (inj₂ tt) → done (inj₂ editableExisting)
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

    afterEditor : Bool ⊎ EditorStatus → Script (Failure ⊎ ⊤)
    afterEditor (inj₁ _) = done (inj₁ editorLaunch)
    afterEditor (inj₂ editorSucceeded) = ask announceRestart λ _ → done (inj₂ tt)
    afterEditor (inj₂ (editorFailed status)) = done (inj₁ (editorUnsuccessful status))

    editorSession : Path.Path → Maybe Text → Script (Failure ⊎ ⊤)
    editorSession path editorValue = ask announceEditor λ _ →
      ask (editor (selectEditor editorValue) path) afterEditor

    afterCreation : Path.Path → Content → Maybe Text → Script (Failure ⊎ ⊤)
    afterCreation path (alreadyConfigured current) editorValue =
      ask (announceAlreadyConfigured path) λ _ → done (inj₂ tt)
    afterCreation path editableExisting editorValue = ask (announceOpeningExisting path) λ _ →
      editorSession path editorValue
    afterCreation path (configured _ _) editorValue = ask (announceCreated path) λ _ →
      ask announceRestart λ _ → done (inj₂ tt)
    afterCreation path (template _) editorValue = ask (announceCreated path) λ _ →
      editorSession path editorValue

    EditorOutcome : Bool ⊎ EditorStatus → Failure ⊎ ⊤ → Set
    EditorOutcome (inj₁ _) result = result ≡ inj₁ editorLaunch
    EditorOutcome (inj₂ editorSucceeded) result = result ≡ inj₂ tt
    EditorOutcome (inj₂ (editorFailed status)) result = result ≡ inj₁ (editorUnsuccessful status)

    -- Existing-file editing never reports completion merely from launching
    -- the editor. Every completed run contains its actual child result.
    existingEditorObserved : ∀ path editorValue events result →
      P.Runs (afterCreation path editableExisting editorValue) events result →
      Data.Product.Σ (Bool ⊎ EditorStatus) (λ observed → Data.Product.Σ (List P.Event) (λ rest →
        events ≡ ((announceOpeningExisting path , tt) ∷ (announceEditor , tt) ∷
          (editor (selectEditor editorValue) path , observed) ∷ rest) × EditorOutcome observed result))
    existingEditorObserved path editorValue ._ ._
      (P.replied _ _ tt (P.replied _ _ tt (P.replied _ _ (inj₁ failed) (P.returned _)))) =
      inj₁ failed , [] , refl , refl
    existingEditorObserved path editorValue ._ ._
      (P.replied _ _ tt (P.replied _ _ tt (P.replied _ _ (inj₂ editorSucceeded) (P.replied _ _ tt (P.returned _))))) =
      inj₂ editorSucceeded , (announceRestart , tt) ∷ [] , refl , refl
    existingEditorObserved path editorValue ._ ._
      (P.replied _ _ tt (P.replied _ _ tt (P.replied _ _ (inj₂ (editorFailed status)) (P.returned _)))) =
      inj₂ (editorFailed status) , [] , refl , refl


    -- Full create command, including early failure, complete publication and
    -- editor exit handling. The joined trace retains every actual filesystem
    -- response; failed writes never reach the editor or success announcements.
    data Created (writeSettings : IO.Settings) (path : Path.Path)
      (pairs : List (String × Text)) (editorValue : Maybe Text) :
      List P.Event → Failure ⊎ ⊤ → Set where
      editingExisting : ∀ prepared announcements result →
        P.Runs (prepare path pairs) prepared (inj₂ editableExisting) →
        P.Runs (afterCreation path editableExisting editorValue) announcements result →
        Created writeSettings path pairs editorValue (prepared Data.List.++ announcements) result
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
      racedEditor : ∀ prepared content written checked announcements result →
        NewContent content →
        P.Runs (prepare path pairs) prepared (inj₂ content) →
        WriteRun writeSettings path content (initialWrite writeSettings) written (IO.failed IO.alreadyExists) →
        P.Runs (existing path pairs) checked (inj₂ editableExisting) →
        P.Runs (afterCreation path editableExisting editorValue) announcements result →
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

-- Init readiness is a concrete filesystem operation. The source bytes
-- and their typed configuration are observations of the existing TOML boundary;
-- this model does not implement or prove a parser/formatter. Other files are an
-- arbitrary frame and are preserved by every Mimir publication.
module Initialization (Frame : Set) (parser : Unsigned.Parser)
  (compareFields : ∀ pairs old desired → Dec (explicitFields pairs old ≡ explicitFields pairs desired)) where
  module Overrides = Input.Read parser
  data Request : Set where
    explicit : (String × Text) × List (String × Text) → Request
    interactive : Request
  Input = Request
  pairs : Input → List (String × Text)
  pairs (explicit (first , rest)) = first ∷ rest
  pairs interactive = []

  data File : Set where
    invalidFile : Text → Failure → File
    validFile : Text → Schema.Config → File
  module Storage = IO.Publication File Frame
  World = Storage.World

  record Metadata : Set where
    constructor metadata
    field operations : Operations.Admitted; source : Text

  preparedFile : Metadata → Values.Config → File
  preparedFile observed cfg = validFile (Metadata.source observed)
    (Schema.config (Metadata.operations observed) cfg nothing nothing nothing nothing)

  data Result : Set where
    ready : File → Result
    needsDecision : Failure → Result

  matchingExisting : Input → Values.Config → File → Result
  matchingExisting input desired document@(invalidFile _ failure) = needsDecision failure
  matchingExisting input desired document@(validFile source current)
    with compareFields (pairs input) (Schema.Config.core current) desired
  ... | yes same = ready document
  ... | no different = needsDecision conflictingSettings

  existing : Input → Values.Config → File → Result
  existing interactive desired document = ready document
  existing input@(explicit _) desired document = matchingExisting input desired document

  chosenOutcome : Metadata → Input → Values.Config → World → World × Result
  chosenOutcome observed input desired before with Storage.World.target before
  ... | nothing = Storage.intended (preparedFile observed desired) before , ready (preparedFile observed desired)
  ... | just current = before , existing input desired current

  outcome : Metadata → Input → World → World × Result
  outcome observed input before with Overrides.create (pairs input)
  ... | inj₁ error = before , needsDecision (override error)
  ... | inj₂ desired = chosenOutcome observed input desired before

  data CommandEffect : Set where
    inspect : CommandEffect
    defaults : CommandEffect
    encode : Operations.Admitted → Values.Config → CommandEffect
    preparePrivate linkAbsent : File → CommandEffect
    syncParent : CommandEffect
    announceReady : File → CommandEffect
  CommandReply : CommandEffect → Set
  CommandReply inspect = Maybe File
  CommandReply defaults = Operations.Admitted
  CommandReply (encode _ _) = Text
  CommandReply _ = ⊤
  module E = Effects.Protocol CommandEffect CommandReply

  announce : File → E.Script Result
  announce document = E.ask syncParent (λ _ → E.ask (announceReady document) (λ _ → E.done (ready document)))
  checkedExisting : Input → Values.Config → File → E.Script Result
  checkedExisting input desired current with existing input desired current
  ... | ready document = announce document
  ... | needsDecision failure = E.done (needsDecision failure)
  afterInspect : Input → Values.Config → Maybe File → E.Script Result
  afterInspect input desired (just current) = checkedExisting input desired current
  afterInspect input desired nothing = E.ask defaults (λ operations → E.ask (encode operations desired) (λ source →
    let document = preparedFile (metadata operations source) desired in
    E.ask (preparePrivate document) (λ _ → E.ask (linkAbsent document) (λ _ → announce document))))
  script : Input → E.Script Result
  script input with Overrides.create (pairs input)
  ... | inj₁ error = E.done (needsDecision (override error))
  ... | inj₂ desired = E.ask inspect (afterInspect input desired)

  -- Failed reads/private writes/syncs interrupt this script. They cannot be
  -- fabricated successful receipts. A successful link is the same complete
  -- create-if-absent publication certified by ConfigurationIO.Publication.
  data Atomic : World → (effect : CommandEffect) → CommandReply effect → World → Set where
    inspected : ∀ before → Atomic before inspect (Storage.World.target before) before
    suppliedDefaults : ∀ before operations → Atomic before defaults operations before
    encoded : ∀ before operations desired source → Atomic before (encode operations desired) source before
    privatelyPrepared : ∀ before document → Atomic before (preparePrivate document) tt before
    linked : ∀ before document → Atomic before (linkAbsent document) tt (Storage.intended document before)
    synced : ∀ before → Atomic before syncParent tt before
    announced : ∀ before document → Atomic before (announceReady document) tt before
  module X = Recovery.Execution World CommandEffect CommandReply Atomic

  Goal : Input → World → World → Result → Set
  Goal input before after reply = Data.Product.Σ Metadata (λ observed → (after , reply) ≡ outcome observed input before)

  -- Only a complete publication changes this world. If another complete file
  -- already occupies the path it wins; if our file won, its requested fields
  -- match directly on every later retry, independent of fresh host metadata.
  outcomeAfterLink : ∀ wanted input before observed cfg →
    Overrides.create (pairs input) ≡ inj₂ cfg →
    Data.Product.Σ Metadata (λ original →
      outcome wanted input (Storage.intended (preparedFile observed cfg) before) ≡ outcome original input before)
  outcomeAfterLink wanted interactive (Storage.world nothing frame) observed .Values.defaultConfig refl =
    observed , refl
  outcomeAfterLink wanted input@(explicit _) (Storage.world nothing frame) observed cfg accepted
    rewrite accepted with compareFields (pairs input) cfg cfg
  ... | yes same = observed , refl
  ... | no different = Data.Empty.⊥-elim (different refl)
  outcomeAfterLink wanted input (Storage.world (just current) frame) observed cfg accepted
    rewrite accepted = wanted , refl

  data Owned (input : Input) : CommandEffect → Set where
    inspectOwned : Owned input inspect
    defaultsOwned : Owned input defaults
    encodeOwned : ∀ operations cfg → Owned input (encode operations cfg)
    privateOwned : ∀ document → Owned input (preparePrivate document)
    linkOwned : ∀ observed cfg → Overrides.create (pairs input) ≡ inj₂ cfg →
      Owned input (linkAbsent (preparedFile observed cfg))
    syncOwned : Owned input syncParent
    announceOwned : ∀ document → Owned input (announceReady document)

  data Scoped (input : Input) : E.Script Result → Set where
    returned : ∀ value → Scoped input (E.done value)
    asked : ∀ effect continuation → Owned input effect →
      (∀ reply → Scoped input (continuation reply)) → Scoped input (E.ask effect continuation)

  announceScoped : ∀ input document → Scoped input (announce document)
  announceScoped input document = asked _ _ syncOwned (λ _ →
    asked _ _ (announceOwned document) (λ _ → returned _))
  existingScoped : ∀ input desired document → Scoped input (checkedExisting input desired document)
  existingScoped input desired document with existing input desired document
  ... | ready selected = announceScoped input selected
  ... | needsDecision failure = returned _
  inspectScoped : ∀ input desired → Overrides.create (pairs input) ≡ inj₂ desired →
    ∀ selected → Scoped input (afterInspect input desired selected)
  inspectScoped input desired accepted (just current) = existingScoped input desired current
  inspectScoped input desired accepted nothing = asked _ _ defaultsOwned (λ operations →
    asked _ _ (encodeOwned operations desired) (λ source →
      asked _ _ (privateOwned _) (λ _ →
        asked _ _ (linkOwned (metadata operations source) desired accepted) (λ _ → announceScoped input _))))
  scriptScoped : ∀ input → Scoped input (script input)
  scriptScoped input with Overrides.create (pairs input) in accepted
  ... | inj₁ error = returned _
  ... | inj₂ desired = asked _ _ inspectOwned (inspectScoped input desired accepted)

  prefixScoped : ∀ input program events residual → Scoped input program → E.Prefix program events residual →
    Data.List.Relation.Unary.All.All (λ event → Owned input (Data.Product.proj₁ event)) events × Scoped input residual
  prefixScoped input program [] .program scoped (E.stopped _) = Data.List.Relation.Unary.All.[] , scoped
  prefixScoped input .(E.ask effect continuation) .((effect , reply) ∷ events) residual
    (asked effect continuation own later) (E.replied _ _ reply {events} rest)
    with prefixScoped input (continuation reply) events residual (later reply) rest
  ... | owners , scoped = Data.List.Relation.Unary.All._∷_ own owners , scoped
  activeOwned : ∀ input effect continuation → Scoped input (E.ask effect continuation) → Owned input effect
  activeOwned input effect continuation (asked .effect .continuation own later) = own

  Invariant : Input → World → World → Set
  Invariant input initial current = ∀ wanted → Data.Product.Σ Metadata (λ original →
    outcome wanted input current ≡ outcome original input initial)
  atomicInvariant : ∀ input initial before after effect reply → Owned input effect →
    Atomic before effect reply after → Invariant input initial before → Invariant input initial after
  atomicInvariant input initial before .before .inspect ._ inspectOwned (inspected .before) old = old
  atomicInvariant input initial before .before .defaults operations defaultsOwned (suppliedDefaults .before .operations) old = old
  atomicInvariant input initial before .before .(encode operations cfg) source (encodeOwned operations cfg) (encoded .before .operations .cfg .source) old = old
  atomicInvariant input initial before .before .(preparePrivate document) .tt (privateOwned document) (privatelyPrepared .before .document) old = old
  atomicInvariant input initial before ._ .(linkAbsent (preparedFile observed cfg)) .tt (linkOwned observed cfg accepted)
    (linked .before ._) old wanted with outcomeAfterLink wanted input before observed cfg accepted
  ... | previous , same with old previous
  ... | original , retained = original , Relation.Binary.PropositionalEquality.trans same retained
  atomicInvariant input initial before .before .syncParent .tt syncOwned (synced .before) old = old
  atomicInvariant input initial before .before .(announceReady document) .tt (announceOwned document) (announced .before .document) old = old

  changesInvariant : ∀ input initial before events after →
    Data.List.Relation.Unary.All.All (λ event → Owned input (Data.Product.proj₁ event)) events →
    X.Changes before events after → Invariant input initial before → Invariant input initial after
  changesInvariant input initial before [] .before Data.List.Relation.Unary.All.[] (X.unchanged _) old = old
  changesInvariant input initial before ((effect , reply) ∷ events) after
    (Data.List.Relation.Unary.All._∷_ own owners) (X.changed _ _ _ middle physical rest) old =
    changesInvariant input initial middle events after owners rest
      (atomicInvariant input initial before middle effect reply own physical old)

  interruptedInvariant : ∀ input initial current → X.Interrupted (script input) initial current → Invariant input initial current
  interruptedInvariant input initial current (X.atPrefix events residual .current prefix physical) =
    changesInvariant input initial initial events current
      (Data.Product.proj₁ (prefixScoped input (script input) events residual (scriptScoped input) prefix)) physical
      (λ observed → observed , refl)
  interruptedInvariant input initial after
    (X.beforeReply events effect continuation current reply .after prefix physical active)
    with prefixScoped input (script input) events (E.ask effect continuation) (scriptScoped input) prefix
  ... | owners , residual = atomicInvariant input initial current after effect reply
    (activeOwned input effect continuation residual) active
    (changesInvariant input initial initial events current owners physical (λ observed → observed , refl))

  -- Availability builds a successful physical execution. Actual receipts
  -- still admit every observed defaults/serialization value on each attempt.
  module Execution (available : World → Metadata) where
    announceObservation : ∀ document before after reply events →
      E.Runs (announce document) events reply → X.Changes before events after →
      (after , reply) ≡ (before , ready document)
    announceObservation document before .before .(ready document) ._
      (E.replied _ _ tt (E.replied _ _ tt (E.returned _)))
      (X.changed _ _ _ _ (synced _) (X.changed _ _ _ _ (announced _ _) (X.unchanged _))) = refl

    existingObservation : ∀ input desired document before after reply events →
      E.Runs (checkedExisting input desired document) events reply → X.Changes before events after →
      (after , reply) ≡ (before , existing input desired document)
    existingObservation input desired document before after reply events execution physical
      with existing input desired document
    ... | ready selected = announceObservation selected before after reply events execution physical
    existingObservation input desired document before .before .(needsDecision failure) .[]
      (E.returned _) (X.unchanged _) | needsDecision failure = refl

    readObservation : ∀ input desired →
      ∀ before after reply events → E.Runs (afterInspect input desired (Storage.World.target before)) events reply →
      X.Changes before events after → Data.Product.Σ Metadata (λ observed →
        (after , reply) ≡ chosenOutcome observed input desired before)
    readObservation input desired before@(Storage.world (just current) frame) after reply events execution physical =
      available before , existingObservation input desired current before after reply events execution physical
    readObservation input desired before@(Storage.world nothing frame) after reply ._
      (E.replied _ _ operations (E.replied _ _ source (E.replied _ _ tt (E.replied _ _ tt execution))))
      (X.changed _ _ _ _ (suppliedDefaults _ _) (X.changed _ _ _ _ (encoded _ _ _ _)
        (X.changed _ _ _ _ (privatelyPrepared _ _) (X.changed _ _ _ _ (linked _ _) physical))))
      = metadata operations source , announceObservation _ _ after reply _ execution physical

    completedObservation : ∀ input before after reply → X.Completed (script input) before after reply →
      Goal input before after reply
    completedObservation input before after reply complete with Overrides.create (pairs input) in accepted
    ... | inj₁ error with complete
    ... | X.completed .[] (E.returned _) (X.unchanged _) = available before , refl
    completedObservation input before after reply complete | inj₂ desired with complete
    ... | X.completed _ (E.replied _ _ .(Storage.World.target before) execution)
      (X.changed _ _ _ .before (inspected .before) physical) =
      readObservation input desired before after reply _ execution physical

    announceProgress : ∀ document before → X.Completed (announce document) before before (ready document)
    announceProgress document before = X.completed
      ((syncParent , tt) ∷ (announceReady document , tt) ∷ [])
      (E.replied _ _ tt (E.replied _ _ tt (E.returned _)))
      (X.changed _ _ _ _ (synced _) (X.changed _ _ _ _ (announced _ _) (X.unchanged _)))
    existingProgress : ∀ input desired document before →
      X.Completed (checkedExisting input desired document) before before (existing input desired document)
    existingProgress input desired document before with existing input desired document
    ... | ready selected = announceProgress selected before
    ... | needsDecision failure = X.completed [] (E.returned _) (X.unchanged _)

    readProgress : ∀ input desired before → Data.Product.Σ World (λ after → Data.Product.Σ Result (λ reply →
      X.Completed (afterInspect input desired (Storage.World.target before)) before after reply))
    readProgress input desired before@(Storage.world (just current) frame) =
      before , existing input desired current , existingProgress input desired current before
    readProgress input desired before@(Storage.world nothing frame) =
      Storage.intended document before , ready document , X.completed
        ((defaults , Metadata.operations observed) ∷ (encode (Metadata.operations observed) desired , Metadata.source observed) ∷
         (preparePrivate document , tt) ∷ (linkAbsent document , tt) ∷
         (syncParent , tt) ∷ (announceReady document , tt) ∷ [])
        (E.replied _ _ _ (E.replied _ _ _ (E.replied _ _ tt (E.replied _ _ tt
          (E.replied _ _ tt (E.replied _ _ tt (E.returned _)))))))
        (X.changed _ _ _ _ (suppliedDefaults _ _) (X.changed _ _ _ _ (encoded _ _ _ _)
          (X.changed _ _ _ _ (privatelyPrepared _ _) (X.changed _ _ _ _ (linked _ _)
            (X.changed _ _ _ _ (synced _) (X.changed _ _ _ _ (announced _ _) (X.unchanged _)))))))
      where
      observed = available before
      document = preparedFile observed desired

    progress : ∀ input before → Data.Product.Σ World (λ after → Data.Product.Σ Result (λ reply →
      X.Completed (script input) before after reply))
    progress input before with Overrides.create (pairs input)
    ... | inj₁ error = before , needsDecision (override error) , X.completed [] (E.returned _) (X.unchanged _)
    ... | inj₂ desired with readProgress input desired before
    ... | after , reply , X.completed events execution physical = after , reply , X.completed
      ((inspect , Storage.World.target before) ∷ events) (E.replied _ _ _ execution)
      (X.changed _ _ _ _ (inspected _) physical)

    converges : ∀ input initial interrupted after reply → X.Interrupted (script input) initial interrupted →
      X.Completed (script input) interrupted after reply → Goal input initial after reply
    converges input initial interrupted after reply cut completion
      with completedObservation input interrupted after reply completion
    ... | observed , completedOutcome with interruptedInvariant input initial interrupted cut observed
    ... | original , retained = original , Relation.Binary.PropositionalEquality.trans completedOutcome retained

    operation : Recovery.RecoverableFor World Input Result Goal
    operation = record
      { Effect = CommandEffect; Reply = CommandReply; script = script; Atomic = Atomic
      ; progress = progress; converges = converges }
