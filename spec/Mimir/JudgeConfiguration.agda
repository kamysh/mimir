{-# OPTIONS --safe #-}
-- Optional judge configuration: strict typed sections, ordered semantic checks,
-- and Unix path/ownership guards. Core startup does not invoke this protocol.
module Mimir.JudgeConfiguration where

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_)
open import Data.List using (List; []; _∷_; length; reverse)
open import Data.Bool.ListAction using (all; any)
open import Data.Maybe using (Maybe; just; nothing; is-just; is-nothing)
open import Data.Nat using (ℕ; _≤?_)
open import Data.Fin using (_≟_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.String using (String; toList)
open import Relation.Nullary using (does; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.RecordDecoding using (readArray)
open import Mimir.PublicInput
open import Mimir.LearningWire using (recordOf)
import Mimir.StructuredValue as V
import Mimir.Validation as Validation
import Mimir.Binary64 as Binary
import Mimir.StandardLibrary as Conversion
import Mimir.ApplicationFloat as Float
open import Data.Float.Base using (_<ᵇ_)
import Mimir.UnixPath as Path
import Mimir.UnixPathParts as Parts
import Mimir.UnixPathParent as Parents
import Mimir.UnixMetadata as Metadata
import Mimir.BitMaskClear as Mask
import Mimir.ConfigurationSchema as Core
import Mimir.NotificationConfig as Email
import Mimir.NotificationConfigurationWire as EmailWire
import Mimir.Effects as Effects

infixl 1 _>>=_
_>>=_ : ∀ {E A B : Set} → E ⊎ A → (A → E ⊎ B) → E ⊎ B
inj₁ error >>= next = inj₁ error
inj₂ value >>= next = next value

positive : Binary.Number → Bool
positive (Binary.nonfinite _ _) = false
positive (Binary.finite n) = 0.0 <ᵇ Float.finite n

data Backend : Set where claudeCode codex commandMode api : Backend
data Provider : Set where openai anthropic openrouter deepseek zai gemini compatible : Provider
data Effort : Set where minimal low medium high xhigh : Effort

record Judge : Set where
  constructor judgeSettings
  field project : Maybe Text; mcpCommand : Text; mcpArgs : List Text

record Llm : Set where
  constructor llmSettings
  field backend : Backend; model : Text; effort : Maybe Effort
        provider : Maybe Provider
        apiKey baseURL command : Maybe Text; args : List Text

record Runtime : Set where
  constructor runtime
  field core : Core.Config; judge : Judge; llm : Llm; email : Email.Config

backend = enum (("claude-code" , claudeCode) ∷ ("codex" , codex) ∷ ("command" , commandMode) ∷ ("api" , api) ∷ [])
provider = enum (("openai" , openai) ∷ ("anthropic" , anthropic) ∷ ("openrouter" , openrouter) ∷
  ("deepseek" , deepseek) ∷ ("zai" , zai) ∷ ("gemini" , gemini) ∷ ("openai-compatible" , compatible) ∷ [])
effort = enum (("minimal" , minimal) ∷ ("low" , low) ∷ ("medium" , medium) ∷ ("high" , high) ∷ ("xhigh" , xhigh) ∷ [])

module Decode (conversion : Conversion.Contract) (sizeMaximum : ℕ) where
  module Num = Numbers conversion
  module E = EmailWire.Decode sizeMaximum

  judge : V.Value → Validation.Fault ⊎ Judge
  judge raw with view raw (toList "batch_size")
  ... | just _ = inj₁ (Validation.fault (Validation.key "batch_size" ∷ []) Validation.unsupportedCombination
    "judge.batch_size is obsolete; run mimir config upgrade to remove it, then mimir config check")
  ... | nothing = recordOf ("project" ∷ "mcp_command" ∷ "mcp_args" ∷ []) (λ fields →
    optional "project" V.asString fields >>= λ project →
    defaulted "mcp_command" (toList "mimir-mcp") V.asString fields >>= λ cmd →
    defaulted "mcp_args" [] (readArray V.asString) fields >>= λ args → inj₂ (judgeSettings project cmd args)) raw

  llm : V.Value → Validation.Fault ⊎ Llm
  llm = recordOf ("backend" ∷ "model" ∷ "reasoning_effort" ∷ "provider" ∷ "api_key" ∷ "base_url" ∷ "command" ∷ "args" ∷ [])
    (λ fields → required "backend" backend fields >>= λ b → required "model" V.asString fields >>= λ model →
      optional "reasoning_effort" effort fields >>= λ effort →
      optional "provider" provider fields >>= λ p →
      optional "api_key" V.asString fields >>= λ key → optional "base_url" V.asString fields >>= λ url →
      optional "command" V.asString fields >>= λ cmd → defaulted "args" [] (readArray V.asString) fields >>= λ args →
      inj₂ (llmSettings b model effort p key url cmd args))

  section : ∀ {A : Set} → String → (V.Value → Validation.Fault ⊎ A) → Maybe V.Value → Text ⊎ A
  section name decode nothing = inj₁ (toList "missing runtime section")
  section name decode (just raw) with decode raw
  ... | inj₁ _ = inj₁ (toList "invalid runtime section structure")
  ... | inj₂ value = inj₂ value

  email : Maybe V.Value → Text ⊎ Email.Config
  email nothing = inj₂ Email.defaults
  email (just raw) = section "email" E.decode (just raw)

  sections : Core.Config → Text ⊎ Runtime
  sections core = section "judge" judge (Core.Config.judge core) >>= λ j →
    section "llm" llm (Core.Config.llm core) >>= λ l → email (Core.Config.email core) >>= λ e →
    inj₂ (runtime core j l e)

-- URL parsing and IP loopback recognition are the URL/network libraries'
-- contracts; Mimir owns the scheme and credential/query/fragment decisions.
record URL : Set where
  field https http loopback hasHost emptyUsername noPassword noQuery noFragment : Bool
record Libraries : Set where
  field path : Text → Path.Path; url : Text → Maybe URL

clean : Text → Bool
clean text = does (Email.trimmed? text)

between : ℕ → ℕ → ℕ → Bool
between lower upper value = does (lower ≤? value) ∧ does (value ≤? upper)

ensure : Bool → String → Text ⊎ ⊤
ensure true _ = inj₂ tt
ensure false detail = inj₁ (toList detail)

optionalCheck : ∀ {A : Set} → (A → Text ⊎ ⊤) → Maybe A → Text ⊎ ⊤
optionalCheck check nothing = inj₂ tt
optionalCheck check (just value) = check value

arguments : List Text → Text ⊎ ⊤
arguments args = ensure (all clean args) "invalid argument"

fileName : Path.Path → Bool
fileName path with reverse (Path.components path)
... | Path.normal _ ∷ _ = true
... | _ = false

plainCommand : Path.Path → Bool
plainCommand path with Path.components path
... | Path.normal _ ∷ [] = true
... | _ = false

module Validate (libraries : Libraries) where
  absoluteCommand : Text → Bool
  absoluteCommand text = Path.absolute (Libraries.path libraries text) ∧ fileName (Libraries.path libraries text)

  endpoint : Text → Text ⊎ ⊤
  endpoint raw with Libraries.url libraries raw
  ... | nothing = inj₁ (toList "invalid llm.base_url")
  ... | just url = ensure (URL.hasHost url) "invalid llm.base_url" >>= λ _ →
    ensure (URL.https url ∨ (URL.http url ∧ URL.loopback url)) "llm.base_url requires HTTPS except on loopback" >>= λ _ →
    ensure (URL.emptyUsername url ∧ URL.noPassword url ∧ URL.noQuery url ∧ URL.noFragment url)
      "llm.base_url must not contain credentials, query, or fragment"

  judge : Judge → Text ⊎ ⊤
  judge j =
    optionalCheck (λ p → ensure (clean p) "invalid judge.project") (Judge.project j) >>= λ _ →
    ensure (clean (Judge.mcpCommand j)) "invalid judge.mcp_command" >>= λ _ →
    ensure (plainCommand (Libraries.path libraries (Judge.mcpCommand j)) ∨ absoluteCommand (Judge.mcpCommand j))
      "judge.mcp_command must be an absolute path or command name" >>= λ _ → arguments (Judge.mcpArgs j)

  harness : Llm → Text ⊎ ⊤
  harness l = ensure (is-nothing (Llm.provider l) ∧ is-nothing (Llm.apiKey l) ∧ is-nothing (Llm.baseURL l) ∧
    is-nothing (Llm.command l) ∧ does (length (Llm.args l) ≤? 0)) "harness backend cannot use API or command settings"

  commandBackend : Llm → Maybe Text → Text ⊎ ⊤
  commandBackend l nothing = inj₁ (toList "llm.command is required")
  commandBackend l (just cmd) = ensure (clean cmd) "invalid llm.command" >>= λ _ →
    ensure (absoluteCommand cmd) "llm.command must be absolute" >>= λ _ →
    ensure (is-nothing (Llm.provider l) ∧ is-nothing (Llm.apiKey l) ∧ is-nothing (Llm.baseURL l))
      "command backend cannot use API settings"

  providerEndpoint : Provider → Llm → Text ⊎ ⊤
  providerEndpoint compatible l = ensure (is-just (Llm.baseURL l)) "llm.base_url is required for openai-compatible"
  providerEndpoint _ l = inj₂ tt

  apiBackend : Llm → Maybe Provider → Maybe Text → Text ⊎ ⊤
  apiBackend l nothing _ = inj₁ (toList "llm.provider is required")
  apiBackend l (just p) nothing = inj₁ (toList "llm.api_key is required")
  apiBackend l (just p) (just key) = ensure (clean key) "invalid llm.api_key" >>= λ _ →
    ensure (is-nothing (Llm.command l) ∧ does (length (Llm.args l) ≤? 0))
      "API backend cannot use command settings" >>= λ _ → providerEndpoint p l

  specific : Llm → Backend → Text ⊎ ⊤
  specific l claudeCode = harness l
  specific l codex = harness l
  specific l commandMode = commandBackend l (Llm.command l)
  specific l api = apiBackend l (Llm.provider l) (Llm.apiKey l)

  codexOnly : Backend → Bool
  codexOnly codex = true
  codexOnly _ = false

  llm : Llm → Text ⊎ ⊤
  llm l = ensure (clean (Llm.model l)) "invalid llm.model" >>= λ _ →
    arguments (Llm.args l) >>= λ _ →
    optionalCheck endpoint (Llm.baseURL l) >>= λ _ →
    ensure (is-nothing (Llm.effort l) ∨ codexOnly (Llm.backend l)) "llm.reasoning_effort is Codex only" >>= λ _ →
    specific l (Llm.backend l)

  validate : Runtime → Text ⊎ ⊤
  validate r = judge (Runtime.judge r) >>= λ _ → llm (Runtime.llm r) >>= λ _ →
    email (Email.validate (Runtime.email r))
    where
    email : Validation.Checked (Email.Valid (Runtime.email r)) → Text ⊎ ⊤
    email (Validation.rejected fault _) = inj₁ (Validation.Fault.explanation fault)
    email (Validation.accepted _) = inj₂ tt

  record Admitted : Set where
    constructor admitted
    field settings : Runtime; valid : validate settings ≡ inj₂ tt

-- Existing Unix policy permits a non-private file only beneath at least one
-- owned private ancestor. Every ancestor must still pass the write guard.
configAccess : Metadata.UserId → Metadata.Metadata → List Metadata.Metadata → Bool
configAccess owner file parents = does (Metadata.regular? (Metadata.Metadata.kind file)) ∧
  does (Metadata.Metadata.owner file ≟ owner) ∧ all (λ p → does (Metadata.parent? p)) parents ∧
  (does (Mask.clear? (Metadata.Metadata.mode file) Metadata.privateMask) ∨
   any (λ p → does (Metadata.ownedPrivate? owner p)) parents)

module Load (conversion : Conversion.Contract) (sizeMaximum : ℕ) (libraries : Libraries)
  (unix : Bool) (owner : Metadata.UserId) where
  module D = Decode conversion sizeMaximum
  module Check = Validate libraries

  data Effect : Set where
    cwd : Effect
    lstat : Path.Path → Effect
    coreLoad : Path.Path → Effect
  Reply : Effect → Set
  Reply cwd = Text ⊎ Path.Path
  Reply (lstat path) = Text ⊎ Metadata.Metadata
  Reply (coreLoad path) = Text ⊎ Core.Config
  module P = Effects.Protocol Effect Reply
  open P using (Script; ask; done)

  record Loaded : Set where
    constructor loaded
    field path : Path.Path; configuration : Check.Admitted

  Result = Text ⊎ Loaded

  admit : Path.Path → Runtime → Script Result
  admit path settings with Check.validate settings in checked
  ... | inj₁ error = done (inj₁ error)
  ... | inj₂ tt = done (inj₂ (loaded path (Check.admitted settings checked)))

  afterCore : (path : Path.Path) → Reply (coreLoad path) → Script Result
  afterCore path (inj₁ _) = done (inj₁ (toList "unable to load config"))
  afterCore path (inj₂ core) with D.sections core
  ... | inj₁ detail = done (inj₁ detail)
  ... | inj₂ settings = admit path settings

  inspect : Path.Path → Metadata.Metadata → List Path.Path → List Metadata.Metadata → Script Result
  inspect path file [] parents with configAccess owner file parents
  ... | false = done (inj₁ (toList "invalid config permissions"))
  ... | true = ask (coreLoad path) (afterCore path)
  inspect path file (parent ∷ rest) parents = ask (lstat parent) (λ where
    (inj₁ _) → done (inj₁ (toList "unable to inspect config path"))
    (inj₂ observedMetadata) → next observedMetadata)
    where
    next : Metadata.Metadata → Script Result
    next observedMetadata with Metadata.directory? (Metadata.Metadata.kind observedMetadata)
    ... | no _ = done (inj₁ (toList "config parent is not a directory"))
    ... | yes _ = inspect path file rest (observedMetadata ∷ parents)

  -- Ancestry enumerates the selected path itself first; the caller supplies
  -- the standard-library ancestor list through its existing checked function.
  file : Path.Path → List Path.Path → Script Result
  file path parents = ask (lstat path) (λ where
    (inj₁ _) → done (inj₁ (toList "unable to inspect config path"))
    (inj₂ observedMetadata) → next observedMetadata)
    where
    next : Metadata.Metadata → Script Result
    next observedMetadata with Metadata.regular? (Metadata.Metadata.kind observedMetadata)
    ... | no _ = done (inj₁ (toList "config must be a regular file"))
    ... | yes _ = inspect path observedMetadata parents []

  resolved : Path.Path → Script Result
  resolved path with Parts.noParent? path | not (not unix)
  ... | no _ | _ = done (inj₁ (toList "config path must not contain '..'"))
  ... | yes _ | false = done (inj₁ (toList "judge config permissions require Unix"))
  ... | yes _ | true = file path (Data.List.drop 1 (Parents.ancestors path))

  absolutize : Path.Path → Script Result
  absolutize path with Path.absolute path
  ... | true = resolved path
  ... | false = ask cwd λ where
    (inj₁ _) → done (inj₁ (toList "unable to resolve config path"))
    (inj₂ current) → resolved (Path.join current path)

  start : Maybe Path.Path → Path.Path → Script Result
  start nothing configured = absolutize configured
  start (just explicit) configured = absolutize explicit
