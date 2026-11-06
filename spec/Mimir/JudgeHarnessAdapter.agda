{-# OPTIONS --safe #-}
-- Existing text-only Claude Code/Codex/custom-command adapter. This describes
-- Mimir's private reviewer subprocess, not the interactive agent harness.
module Mimir.JudgeHarnessAdapter where

open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Bool.ListAction using (all)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_; _≤?_; _*_)
open import Data.Integer using (ℤ)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String; toList)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (does; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text; byteLength)
open import Mimir.Bits using (Byte)
open import Mimir.RecordDecoding using (_>>=_; readArray)
open import Mimir.PublicInput using (required; view)
open import Mimir.LearningWire using (recordOf)
import Mimir.Validation as Validation
import Mimir.StandardLibrary as Conversion
import Mimir.StructuredValue as V
import Mimir.PublicEncoding as Encoding
import Mimir.JudgeConfiguration as Config
import Mimir.JudgeRevision as Revision
import Mimir.JudgeJSON as JSONDependency
import Mimir.JudgePrompt as Prompt
import Mimir.JudgeProcess as Process
import Mimir.ReviewObservation as Observation
import Mimir.ExperienceSchema as Experience
import Mimir.SourceFailure as Source
import Mimir.Effects as Effects
import Mimir.Binary64 as Binary
import Mimir.DiagnosticText as Diagnostic

record Libraries : Set where
  field display : Revision.Display
        utf8 : List Byte → Maybe Text
        encode : Text → List Byte
        contains : Text → Text → Bool
        integer : ℤ → Text

record Adapter : Set where
  constructor adapter
  field selectedID : Maybe ℕ; history : List V.Value; checked : Bool; pending : List (Text × Text)

initial : Adapter
initial = adapter nothing [] false []

same : Maybe ℕ → ℕ → Bool
same nothing identity = false
same (just previous) identity = does (previous ≟ identity)

willCallModel : Adapter → ℕ → Bool
willCallModel state identity with same (Adapter.selectedID state) identity | Adapter.pending state
... | false | _ = true
... | true | [] = true
... | true | _ ∷ _ = false

historyFeedback : Maybe V.Value → List V.Value
historyFeedback nothing = []
historyFeedback (just result) = Encoding.object (("tool_results" , V.array
  (Encoding.object (("result" , result) ∷ []) ∷ [])) ∷ []) ∷ []

prepare : Adapter → ℕ → Maybe V.Value → Adapter
prepare before identity last = record reset { history = Adapter.history reset ++ feedback }
  where
  reset : Adapter
  reset with same (Adapter.selectedID before) identity
  ... | true = before
  ... | false = record before { selectedID = just identity ; history = [] ; pending = [] }
  feedback = historyFeedback last

schema : V.Value
schema = Encoding.object
  (("type" , V.string (toList "object")) ∷ ("additionalProperties" , V.boolean false) ∷
   ("properties" , Encoding.object (("calls" , Encoding.object
      (("type" , V.string (toList "array")) ∷
       ("items" , Encoding.object (("type" , V.string (toList "object")) ∷
         ("additionalProperties" , V.boolean false) ∷ ("properties" , Encoding.object
           (("name" , Encoding.object (("type" , V.string (toList "string")) ∷ [])) ∷
            ("arguments_json" , Encoding.object (("type" , V.string (toList "string")) ∷ [])) ∷ [])) ∷
         ("required" , V.array (V.string (toList "name") ∷ V.string (toList "arguments_json") ∷ [])) ∷ [])) ∷ [])) ∷ [])) ∷
   ("required" , V.array (V.string (toList "calls") ∷ [])) ∷ [])

requiredFlags : Config.Backend → List Text
requiredFlags Config.codex = map toList
  ("--ignore-user-config" ∷ "--ignore-rules" ∷ "--ephemeral" ∷ "--sandbox" ∷ "--output-schema" ∷
   "--output-last-message" ∷ "--json" ∷ "--skip-git-repo-check" ∷ "--model" ∷ "--config" ∷ [])
requiredFlags Config.claudeCode = map toList
  ("--print" ∷ "--restricted" ∷ "--tools" ∷ "--strict-mcp-config" ∷ "--mcp-config" ∷
   "--disable-slash-commands" ∷ "--no-session-persistence" ∷ "--output-format" ∷ "--json-schema" ∷
   "--permission-mode" ∷ "--permission-prompts" ∷ "--settings" ∷ "--model" ∷ [])
requiredFlags _ = []

effortText : Config.Effort → Text
effortText Config.minimal = toList "minimal"
effortText Config.low = toList "low"
effortText Config.medium = toList "medium"
effortText Config.high = toList "high"
effortText Config.xhigh = toList "xhigh"

module Run (conversion : Conversion.Contract) (format : Encoding.Formatting) (libraries : Libraries)
  (config : Config.Llm) (program : Text) (selected : Observation.Snapshot) (tools : List V.Value) where
  module Encode = Encoding.Encode format
  module JSON = JSONDependency conversion
  display = Libraries.display libraries
  json = Revision.Display.json display
  encode = Revision.Display.bytes display
  source = Observation.Snapshot.experience selected
  identity = Experience.Experience.identity source

  record Result : Set where
    constructor result
    field state : Adapter; answer : Revision.Error ⊎ Revision.Action

  record ProcessReceipt (request : Process.Spawn) : Set where
    constructor processReceipt
    field outcome : Process.Result
          events : List (Maybe Process.P.Event)
          executed : Process.Trace (Process.start request) events (Process.finished outcome)

  record ProcessCancellation (owner : Maybe ℕ) : Set where
    field events : List Process.P.Event
          executed : Process.P.Runs (Process.cancelOwned owner) events
            (Process.finished (inj₁ (Process.nativeFailure (toList "cancelled"))))

  data Effect : Set where
    remember : Adapter → Effect -- synchronous mutation of the adapter fields
    rootExists createRoot700 rootMetadata : Effect
    newUUID : Effect
    createRun700 removeRun : Text → Effect
    writeNew600NoFollowCloseExec : Text → List Byte → Effect
    runProcess : Process.Spawn → Effect
    openAnswerNoFollowCloseExec : Text → Effect
    answerMetadata readAnswerBytes : ℕ → Effect
    dropPendingIO : Effect -- drop the awaited library future and its owned file/pipe guards
    cancelProcess : Maybe ℕ → Effect
    -- Wait for an already-started filesystem call, without issuing it again.
    -- An unavailable result still acknowledges that the call has settled.
    awaitFilesystem : ℕ → Effect → Effect
  Reply : Effect → Set
  Reply (remember _) = ⊤
  Reply rootExists = Bool
  Reply createRoot700 = Text ⊎ ⊤
  Reply rootMetadata = Text ⊎ (Bool × Bool) -- is_dir(), lstat is_symlink()
  Reply newUUID = ℕ
  Reply (createRun700 _) = Text ⊎ ⊤
  Reply (removeRun _) = ⊤ -- best-effort RunDir::drop
  Reply (writeNew600NoFollowCloseExec _ _) = Text ⊎ ⊤
  Reply (runProcess request) = ProcessReceipt request
  Reply (openAnswerNoFollowCloseExec _) = Text ⊎ ℕ
  Reply (answerMetadata _) = Text ⊎ (Bool × ℕ) -- regular file and size
  Reply (readAnswerBytes _) = Text ⊎ List Byte -- take(MAX_ANSWER+1).read_to_end
  Reply dropPendingIO = ⊤
  Reply (cancelProcess owner) = ProcessCancellation owner
  Reply (awaitFilesystem job effect) = Text ⊎ Reply effect
  module P = Effects.Protocol Effect Reply
  open P using (Script; ask; done) renaming (_>>=_ to _then_)

  failure : Adapter → Text → Script Result
  failure state detail = done (result state (inj₁ (Revision.error detail nothing)))

  processFailure : Process.Failure → Revision.Error
  processFailure (Process.nativeFailure detail) = Revision.error detail nothing
  processFailure (Process.unsuccessfulExit status stderr) = Revision.error
    (toList "harness exited with " ++ status ++ toList ": " ++
      Diagnostic.bounded 512 (Conversion.Contract.lossyUTF8 conversion stderr)) nothing

  process : Process.Spawn → Script (Revision.Error ⊎ List Byte)
  process request = ask (runProcess request) (λ receipt → done (convert (ProcessReceipt.outcome receipt)))
    where
    convert : Process.Result → Revision.Error ⊎ List Byte
    convert (inj₁ failureValue) = inj₁ (processFailure failureValue)
    convert (inj₂ output) = inj₂ output

  helpArgs : Config.Backend → List Text
  helpArgs Config.codex = map toList ("exec" ∷ "--help" ∷ [])
  helpArgs _ = toList "--help" ∷ []

  check : Text → Adapter → Script (Revision.Error ⊎ Adapter)
  check work state with Adapter.checked state | Config.Llm.backend config
  ... | true | _ = done (inj₂ state)
  ... | false | Config.commandMode = done (inj₂ state)
  ... | false | kind = process (Process.spawnSpec program (helpArgs kind) work []) then (λ where
      (inj₁ failureValue) → done (inj₁ failureValue)
      (inj₂ output) → inspect output)
    where
    inspect : List Byte → Script (Revision.Error ⊎ Adapter)
    inspect output with Libraries.utf8 libraries output
    ... | nothing = done (inj₁ (Revision.error (toList "invalid harness help") nothing))
    ... | just help with all (Libraries.contains libraries help) (requiredFlags kind)
    ...   | false = done (inj₁ (Revision.error (toList "installed harness lacks required isolation or output flags") nothing))
    ...   | true = ask (remember (record state { checked = true }))
        (λ _ → done (inj₂ (record state { checked = true })))

  instructions : Text
  instructions = toList "Review only this pinned experience. Use the supplied tools through calls; do not execute tools yourself. " ++
    Prompt.guidance json source ++ toList " The host enforces project " ++ Experience.Experience.project source ++
    toList ", experience " ++ Encoding.Formatting.uuidText format identity ++ toList ", source revision " ++
    Libraries.integer libraries (Observation.Snapshot.revision selected) ++ toList ", and review revision " ++
    Libraries.integer libraries (Observation.Snapshot.reviewRevision selected) ++ toList ". Return an empty calls array only when you have finished."

  payload : Adapter → V.Value
  payload state = Encoding.object (("instructions" , V.string instructions) ∷ ("experience" , Encode.snapshot selected) ∷
    ("tools" , V.array tools) ∷ ("history" , V.array (Adapter.history state)) ∷ ("response_schema" , schema) ∷
    ("protocol" , V.string (toList "Return one JSON object matching response_schema. Calls are executed in array order, and each receives a result. arguments_json is a JSON object encoded as a string. Never execute tools directly.")) ∷ [])

  codexEffort : Maybe Config.Effort → List Text
  codexEffort nothing = []
  codexEffort (just effort) = toList "-c" ∷ (toList "model_reasoning_effort=\"" ++ effortText effort ++ toList "\"") ∷ []

  args : Text → Config.Backend → List Text
  args work Config.commandMode = Config.Llm.args config
  args work Config.api = [] -- rejected by constructor below
  args work Config.codex = map toList
    ("exec" ∷ "--json" ∷ "--ignore-user-config" ∷ "--ignore-rules" ∷ "--ephemeral" ∷
     "--skip-git-repo-check" ∷ "--sandbox" ∷ "read-only" ∷ "--model" ∷ []) ++
    (Config.Llm.model config ∷ []) ++ codexEffort (Config.Llm.effort config) ++ map toList
    ("-c" ∷ "approval_policy=\"never\"" ∷ "-c" ∷ "features.shell_tool=false" ∷ "-c" ∷ "features.hooks=false" ∷
     "-c" ∷ "features.apps=false" ∷ "-c" ∷ "features.plugins=false" ∷ "-c" ∷ "features.skill_search=false" ∷
     "-c" ∷ "web_search=\"disabled\"" ∷ "-c" ∷ "mcp_servers={}" ∷ "-c" ∷ "project_doc_max_bytes=0" ∷
     "--output-schema" ∷ []) ++ ((work ++ toList "/schema.json") ∷ toList "--output-last-message" ∷
       (work ++ toList "/answer.json") ∷ toList "-" ∷ [])
  args work Config.claudeCode = toList "--print" ∷ toList "--model" ∷ Config.Llm.model config ∷
    (map toList ("--restricted" ∷ "--tools" ∷ "" ∷ "--permission-mode" ∷ "dontAsk" ∷
     "--permission-prompts" ∷ "none" ∷ "--settings" ∷ "{\"disableAllHooks\":true}" ∷
     "--disable-slash-commands" ∷ "--mcp-config" ∷ []) ++ ((work ++ toList "/mcp.json") ∷
     (map toList ("--strict-mcp-config" ∷ "--no-session-persistence" ∷ "--output-format" ∷ "json" ∷ "--json-schema" ∷ []) ++
       (json schema ∷ []))))
  writeArgs : Text → Config.Backend → Script (Revision.Error ⊎ ⊤)
  writeArgs work Config.claudeCode = ask (writeNew600NoFollowCloseExec (work ++ toList "/mcp.json")
    (Libraries.encode libraries (toList "{\"mcpServers\":{}}"))) (done ∘ convert)
    where
    open import Function using (_∘_)
    convert : Text ⊎ ⊤ → Revision.Error ⊎ ⊤
    convert (inj₁ detail) = inj₁ (Revision.error detail nothing)
    convert (inj₂ tt) = inj₂ tt
  writeArgs work Config.codex = ask (writeNew600NoFollowCloseExec (work ++ toList "/schema.json") (encode schema)) λ where
    (inj₁ detail) → done (inj₁ (Revision.error detail nothing))
    (inj₂ tt) → done (inj₂ tt)
  writeArgs work Config.commandMode = done (inj₂ tt)
  writeArgs work Config.api = done (inj₁ (Revision.error (toList "API backend is not a harness") nothing))

  readAnswer : Text → Script (Revision.Error ⊎ List Byte)
  readAnswer work = ask (openAnswerNoFollowCloseExec (work ++ toList "/answer.json")) (λ where
    (inj₁ detail) → done (inj₁ (Revision.error detail nothing))
    (inj₂ handle) → ask (answerMetadata handle) (metadata handle))
    where
    metadata : ℕ → Text ⊎ (Bool × ℕ) → Script (Revision.Error ⊎ List Byte)
    metadata handle (inj₁ detail) = done (inj₁ (Revision.error detail nothing))
    metadata handle (inj₂ (regular , size)) with regular
    ... | false = done (inj₁ (Revision.error (toList "invalid harness answer") nothing))
    ... | true = ask (readAnswerBytes handle) (λ where
      (inj₁ detail) → done (inj₁ (Revision.error detail nothing))
      (inj₂ bytes) → checked bytes)
      where
      checked : List Byte → Script (Revision.Error ⊎ List Byte)
      checked bytes = done (inj₂ bytes)

  claudeFallback : V.Value → Revision.Error ⊎ V.Value
  claudeFallback wrapper with required "result" V.asString (view wrapper)
  ... | inj₁ _ = inj₁ (Revision.error (toList "Claude result missing") nothing)
  ... | inj₂ text = JSON.text (toList "invalid Claude structured result") text

  unwrapClaude : V.Value → Revision.Error ⊎ V.Value
  unwrapClaude wrapper with view wrapper (toList "is_error")
  ... | just (V.boolean false) with view wrapper (toList "structured_output")
  ...   | nothing = claudeFallback wrapper
  ...   | just V.null = claudeFallback wrapper
  ...   | just value = inj₂ value
  unwrapClaude _ | _ = inj₁ (Revision.error (toList "Claude reported failure") nothing)

  unwrap : Text → Config.Backend → List Byte → Script (Revision.Error ⊎ V.Value)
  unwrap work Config.codex stdout = readAnswer work then λ where
    (inj₁ failureValue) → done (inj₁ failureValue)
    (inj₂ bytes) → done (JSON.read (toList "invalid Codex structured result") bytes)
  unwrap work Config.commandMode stdout = done (JSON.read (toList "invalid command result") stdout)
  unwrap work Config.api stdout = done (inj₁ (Revision.error (toList "API backend is not a harness") nothing))
  unwrap work Config.claudeCode stdout with JSON.read (toList "invalid Claude result") stdout
  ... | inj₁ failureValue = done (inj₁ failureValue)
  ... | inj₂ wrapper = done (unwrapClaude wrapper)

  call : V.Value → Validation.Fault ⊎ (Text × Text)
  call = recordOf ("name" ∷ "arguments_json" ∷ []) (λ fields → required "name" V.asString fields >>= λ name →
    required "arguments_json" V.asString fields >>= λ arguments → inj₂ (name , arguments))

  calls : V.Value → Validation.Fault ⊎ List (Text × Text)
  calls = recordOf ("calls" ∷ []) (required "calls" (readArray call))

  action : Text × Text → Revision.Error ⊎ Revision.Action
  action (name , arguments) with JSON.text (toList "invalid harness tool arguments") arguments
  ... | inj₂ value = inj₂ (Revision.tool name value)
  ... | inj₁ failureValue with Revision.Error.source failureValue
  ...   | just source = inj₂ (Revision.malformedTool name source)
  ...   | nothing = inj₁ failureValue

  yield : Adapter → Script Result
  yield state with Adapter.pending state
  ... | [] = done (result state (inj₂ Revision.modelDone))
  ... | current ∷ rest = ask (remember updated) (λ _ → done (result updated (action current)))
    where updated = record state { pending = rest }

  afterReply : Adapter → Revision.Error ⊎ V.Value → Script Result
  afterReply state (inj₁ failureValue) = done (result state (inj₁ failureValue))
  afterReply state (inj₂ reply) with calls reply
  ... | inj₁ fault = done (result state (inj₁ (Revision.error (Source.display captured) (just captured))))
    where captured = Source.Current.input conversion (toList "invalid harness reply") (encode reply) (Revision.Display.fault display fault)
  ... | inj₂ requests = ask (remember updated) (λ _ → yield updated)
    where updated = record state { history = Adapter.history state ++
            (Encoding.object (("assistant" , reply) ∷ []) ∷ []) ; pending = requests }

  invoke : Text → Adapter → Script Result
  invoke work state = writeArgs work (Config.Llm.backend config) then λ where
      (inj₁ failureValue) → done (result state (inj₁ failureValue))
      (inj₂ tt) → process (Process.spawnSpec program (args work (Config.Llm.backend config)) work
        (encode (payload state))) then λ where
          (inj₁ failureValue) → done (result state (inj₁ failureValue))
          (inj₂ stdout) → unwrap work (Config.Llm.backend config) stdout then afterReply state

  inDirectory : Text → Adapter → Script Result
  inDirectory work state = (check work state then λ where
    (inj₁ failureValue) → done (result state (inj₁ failureValue))
    (inj₂ checked) → invoke work checked) then λ outcome →
      ask (removeRun work) (λ _ → done outcome)

  create : Adapter → Script Result
  create state = ask newUUID (λ id → ask (createRun700 (path id)) λ where
    (inj₁ detail) → failure state detail
    (inj₂ tt) → inDirectory (path id) state)
    where path = λ id → toList "/var/tmp/mimir/judge-" ++ Encoding.Formatting.uuidText format id

  inspectRoot : Adapter → Script Result
  inspectRoot state = ask rootMetadata (λ where
    (inj₁ detail) → failure state detail
    (inj₂ (directory , symlink)) → admit (directory ∧ not symlink))
    where
    admit : Bool → Script Result
    admit false = failure state (toList "unsafe harness temp root")
    admit true = create state

  start : Adapter → Maybe V.Value → Script Result
  start state last with Adapter.pending updated
    where updated = prepare state identity last
  ... | _ ∷ _ = ask (remember updated) (λ _ → yield updated)
    where updated = prepare state identity last
  ... | [] = ask (remember updated) (λ _ → ask rootExists (λ where
    true → inspectRoot updated
    false → ask createRoot700 λ where
      (inj₁ detail) → failure updated detail
      (inj₂ tt) → inspectRoot updated))
    where updated = prepare state identity last

  observedState : Adapter → List P.Event → Adapter
  observedState state [] = state
  observedState state ((remember updated , _) ∷ events) = observedState updated events
  observedState state (_ ∷ events) = observedState state events

  -- A checkpoint is backed by the actual adapter prefix. The nested child
  -- has its own spawn/wait trace while runProcess has not yet returned.
  data FileJob : Effect → Set where
    creatingRoot : FileJob createRoot700
    creatingRun : ∀ path → FileJob (createRun700 path)
    writingFile : ∀ path bytes → FileJob (writeNew600NoFollowCloseExec path bytes)
    removingRun : ∀ path → FileJob (removeRun path)
    openingAnswer : ∀ path → FileJob (openAnswerNoFollowCloseExec path)
    inspectingAnswer : ∀ handle → FileJob (answerMetadata handle)
    readingAnswer : ∀ handle → FileJob (readAnswerBytes handle)

  data Checkpoint (before : Adapter) (last : Maybe V.Value) : Set where
    scriptPoint : ∀ events residual → P.Prefix (start before last) events residual → Checkpoint before last
    processPoint : ∀ events request continuation →
      P.Prefix (start before last) events (ask (runProcess request) continuation) →
      ∀ childEvents childState → Process.Trace (Process.start request) childEvents childState → Checkpoint before last
    filesystemPoint : ∀ events (job : ℕ) effect continuation → FileJob effect →
      P.Prefix (start before last) events (ask effect continuation) → Checkpoint before last

  checkpointEvents : ∀ {before last} → Checkpoint before last → List P.Event
  checkpointEvents (scriptPoint events residual prefix) = events
  checkpointEvents (processPoint events request continuation prefix childEvents childState childPrefix) = events
  checkpointEvents (filesystemPoint events job effect continuation kind prefix) = events

  checkpointOwner : ∀ {before last} → Checkpoint before last → Maybe ℕ
  checkpointOwner (scriptPoint events residual prefix) = nothing
  checkpointOwner (processPoint events request continuation prefix childEvents childState childPrefix) =
    Process.ownerAfter nothing childEvents
  checkpointOwner (filesystemPoint events job effect continuation kind prefix) = nothing

  directoryAfter : Maybe Text → List P.Event → Maybe Text
  directoryAfter owned [] = owned
  directoryAfter owned ((createRun700 path , inj₂ tt) ∷ events) = directoryAfter (just path) events
  directoryAfter owned ((removeRun path , tt) ∷ events) = directoryAfter nothing events
  directoryAfter owned (_ ∷ events) = directoryAfter owned events

  removeOwnedDirectory : Maybe Text → Script ⊤
  removeOwnedDirectory nothing = done tt
  removeOwnedDirectory (just path) = ask (removeRun path) (λ _ → done tt)

  settleCheckpoint : ∀ {before last} → Checkpoint before last → Script (List P.Event)
  settleCheckpoint (filesystemPoint events job effect continuation kind prefix) = ask (awaitFilesystem job effect) λ where
    (inj₁ error) → done events
    (inj₂ reply) → done (events ++ ((effect , reply) ∷ []))
  settleCheckpoint point = done (checkpointEvents point)

  cancelCheckpoint : ∀ {before last} → Checkpoint before last → Script ⊤
  cancelCheckpoint point = settleCheckpoint point then λ settled →
    ask dropPendingIO (λ _ → ask (cancelProcess (checkpointOwner point)) (λ _ →
      removeOwnedDirectory (directoryAfter nothing settled)))

construct : Config.Llm → Text ⊎ Text
construct config with Config.Llm.backend config
... | Config.claudeCode = inj₂ (toList "claude")
... | Config.codex = inj₂ (toList "codex")
... | Config.api = inj₁ (toList "API backend is not a harness")
... | Config.commandMode with Config.Llm.command config
...   | nothing = inj₁ (toList "missing command")
...   | just program = inj₂ program
