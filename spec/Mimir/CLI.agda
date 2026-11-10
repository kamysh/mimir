{-# OPTIONS --safe #-}
-- Clap supplies typed arguments according to this command surface. Application
-- dispatch, defaults, command-specific reads and output selection are Mimir
-- behavior. Terminal alignment/float formatting is a standard formatter boundary.
module Mimir.CLI where

open import Data.Bool using (Bool; true; false; not; _∧_)
open import Data.Float.Base using (Float; _<ᵇ_)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≟_; _≤?_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.String using (String; toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (does; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import Mimir.Text using (Text)
import Mimir.ConfigurationPath as Path
import Mimir.PublicEncoding as Encoding
import Mimir.PublicInput as Input
import Mimir.GraphReadProtocol as Read
import Mimir.CandidateGraph as Graph
import Mimir.LearningCandidates as Candidates
import Mimir.RetrievalRanking as Ranking
import Mimir.StructuredValue as V
import Mimir.Validation as Validation
import Mimir.StandardLibrary as Library
import Mimir.McpErrors as Errors
import Mimir.GraphNumerics as Numeric
import Mimir.GraphRecords as Records
import Mimir.ApplicationStore as Store
import Mimir.StorageSemantics as Stored
import Mimir.InferenceStorageBinding as InferenceStore
import Mimir.PosteriorComputation as Posterior
import Mimir.Recovery as Recovery
import Mimir.OperationControls as Controls
import Mimir.ToolCatalog as Tools
module Correction = Errors.AgentCorrection
open import Mimir.RecordDecoding using (_>>=_; mapResult)

data JudgeCommand : Set where
  diagnose : Maybe Path.Path → Maybe Path.Path → JudgeCommand
  checkConfig : Maybe Path.Path → JudgeCommand
  run : Maybe Path.Path → Maybe Path.Path → JudgeCommand
  watch : Maybe Path.Path → Maybe Path.Path → JudgeCommand
  status : Maybe Path.Path → JudgeCommand
  diagnostics : Maybe Path.Path → Bool → Maybe ℕ → JudgeCommand

data HookCommand : Set where prompt pretooluse : HookCommand; stop : Maybe Text → HookCommand; setProject : Text → HookCommand

data ServiceCommand : Set where
  stats : ServiceCommand
  list patterns : Maybe Text → Ranking.Selection → ServiceCommand
  query : Text → Ranking.Selection → Bool → Maybe Text → Maybe Candidates.Memory → ServiceCommand
  evidenceAdd : Text → Text → Float → ServiceCommand -- chunk, belief, weight
  evidenceList deleteBelief deletePattern : Text → ServiceCommand
  forget : Text → ServiceCommand
  decay : Float → Maybe Text → ServiceCommand
  contradictions : Maybe Text → ServiceCommand
  sweep : Float → Maybe Text → ServiceCommand
  docLoad : Text → Maybe Text → ServiceCommand
  docQuery : Text → Maybe Text → Ranking.Selection → ServiceCommand
  docClear : Text → ServiceCommand
  intervene : Text → Float → ServiceCommand

data OperationCommand : Set where
  reserve : Text → OperationCommand
  outcome cancel : OperationCommand

data ConfigurationCommand : Set where
  check : Maybe Path.Path → ConfigurationCommand
  upgrade : Maybe Path.Path → Maybe Path.Path → ConfigurationCommand

data Command : Set where
  control : OperationCommand → Command
  configuration : ConfigurationCommand → Command
  init : List (String × Text) → Command
  service : ServiceCommand → Command
  reembed : Command
  hook : HookCommand → Command
  judge : JudgeCommand → Command

-- The DB entry accepts this closed command family. Offline configuration,
-- hook and judge dispatch remain their existing separate application paths.
data DatabaseCommand : Command → Set where
  serviceCase : ∀ command → DatabaseCommand (service command)
  controlCase : ∀ command → DatabaseCommand (control command)
  backfillCase : DatabaseCommand reembed

databaseCommand : (command : Command) → Maybe (DatabaseCommand command)
databaseCommand (service command) = just (serviceCase command)
databaseCommand (control command) = just (controlCase command)
databaseCommand reembed = just backfillCase
databaseCommand (configuration _) = nothing
databaseCommand (init _) = nothing
databaseCommand (hook _) = nothing
databaseCommand (judge _) = nothing

operationLeafName : OperationCommand → String
operationLeafName (reserve _) = "operation reserve"
operationLeafName outcome = "operation outcome"
operationLeafName cancel = "operation cancel"

-- The global option belongs to the actual invocation, including commands
-- which forbid it. Keep its submitted spelling until pure UUID admission.
record Invocation : Set where
  constructor invocation
  field
    command : Command
    operationToken : Maybe Text

serviceWrites : ServiceCommand → Bool
serviceWrites stats = false
serviceWrites (list _ _) = false
serviceWrites (patterns _ _) = false
serviceWrites (query _ _ _ _ _) = false
serviceWrites (evidenceAdd _ _ _) = true
serviceWrites (evidenceList _) = false
serviceWrites (deleteBelief _) = true
serviceWrites (deletePattern _) = true
serviceWrites (forget _) = true
serviceWrites (decay _ _) = true
serviceWrites (contradictions _) = false
serviceWrites (sweep _ _) = true
serviceWrites (docLoad _ _) = true
serviceWrites (docQuery _ _ _) = false
serviceWrites (docClear _) = true
serviceWrites (intervene _ _) = false

needsToken : Command → Bool
needsToken (control (reserve _)) = false
needsToken (control outcome) = true
needsToken (control cancel) = true
needsToken (service command) = serviceWrites command
needsToken reembed = true
needsToken (configuration _) = false
needsToken (init _) = false
needsToken (hook _) = false
needsToken (judge _) = false

Token : Bool → Set
Token true = ℕ
Token false = ⊤

missingToken : Correction.Claim
missingToken = Correction.claim (Correction.item Correction.arguments
  (Validation.fault (Validation.key "operation_token" ∷ []) Validation.missingField
    "This command requires the original PostgreSQL-issued operation token before any business work starts.")
  (toList "--operation-token UUID returned by mimir operation reserve REQUEST_KEY.")
  (toList "Reserve this intended action first and keep its key and token. After a lost reply, repeat the original reservation key, then retry this exact command with its original token. Do not invent a UUID.")) []

unexpectedToken : Correction.Claim
unexpectedToken = Correction.claim (Correction.item Correction.arguments
  (Validation.fault (Validation.key "operation_token" ∷ []) Validation.unsupportedCombination
    "This command does not use an operation token.")
  (toList "Omit --operation-token for this command.")
  (toList "Use operation outcome to inspect a token, or supply it to the intended business write. Check the command help; do not silently change the requested action.")) []

tokenSyntax : Library.Contract → Maybe Text → Correction.Claim ⊎ ⊤
tokenSyntax library nothing = inj₂ tt
tokenSyntax library (just raw) with Input.readUUID library (V.string raw)
... | inj₁ _ = inj₁ (Correction.claim (Correction.uuidItem (Validation.key "operation_token" ∷ [])) [])
... | inj₂ _ = inj₂ tt

readToken : Library.Contract → (required : Bool) → Maybe Text → Correction.Claim ⊎ Token required
readToken library true nothing = inj₁ missingToken
readToken library false nothing = inj₂ tt
readToken library required (just raw) with Input.readUUID library (V.string raw)
... | inj₁ _ = inj₁ (Correction.claim (Correction.uuidItem (Validation.key "operation_token" ∷ [])) [])
readToken library true (just raw) | inj₂ token = inj₂ token
readToken library false (just raw) | inj₂ _ = inj₁ unexpectedToken

record Defaults : Set where
  field listLimit queryLimit documentLimit : Ranking.Selection
        queryEvidence : Bool
        decayFactor threshold evidenceWeight : Float

defaults : Defaults
defaults = record { listLimit = nothing; queryLimit = nothing; documentLimit = nothing
  ; queryEvidence = false; decayFactor = 0.99; threshold = 0.3; evidenceWeight = 1.0 }

-- Pure admission precedes configuration and database access for every service
-- command. Collect independent field problems instead of choosing replacements.
uuidIssues : Library.Contract → String → Text → List Correction.Item
uuidIssues conversion fieldName value with Input.readUUID conversion (V.string value)
... | inj₁ _ = Correction.uuidItem (Validation.key fieldName ∷ []) ∷ []
... | inj₂ _ = []

probabilityIssues : String → Float → List Correction.Item
probabilityIssues fieldName value with Numeric.probability value
... | true = []
... | false = Correction.item Correction.arguments
  (Validation.fault (Validation.key fieldName ∷ []) Validation.invalidNumber
    "The supplied value must be finite and between 0 and 1 inclusive.")
  (toList "A finite number between 0 and 1 inclusive.")
  (toList "Correct the value using the intended request. If it is unknown, ask the user; do not clamp it or invent a replacement.") ∷ []

requestIssues : Library.Contract → ServiceCommand → List Correction.Item
requestIssues conversion (deleteBelief id) = uuidIssues conversion "id" id
requestIssues conversion (deletePattern id) = uuidIssues conversion "id" id
requestIssues conversion (intervene id value) = uuidIssues conversion "id" id ++ probabilityIssues "value" value
requestIssues conversion (evidenceAdd chunk belief weight) = uuidIssues conversion "chunk_id" chunk ++
  uuidIssues conversion "belief_id" belief ++ probabilityIssues "weight" weight
requestIssues conversion (evidenceList belief) = uuidIssues conversion "belief_id" belief
requestIssues conversion (decay factor project) = probabilityIssues "factor" factor
requestIssues conversion (sweep threshold project) = probabilityIssues "threshold" threshold
requestIssues conversion _ = []

-- The native parser first reports command-field problems, then applies the
-- global operation option policy. Both decisions precede configuration/DB I/O.
commandIssues : Library.Contract → Command → List Correction.Item
commandIssues library (service command) = requestIssues library command
commandIssues library (control (reserve key)) with Controls.admitRequestKey key
... | inj₂ _ = []
... | inj₁ detail = Correction.item Correction.arguments detail
  (toList "A stable nonblank key identifying this intended action.")
  (toList "Repeat the original key after a lost reply. Ask the user if the intended action is uncertain; do not reserve replacement work to bypass a problem.") ∷ []
commandIssues library (control outcome) = []
commandIssues library (control cancel) = []
commandIssues library (configuration _) = []
commandIssues library (init _) = []
commandIssues library reembed = []
commandIssues library (hook _) = []
commandIssues library (judge _) = []

record Admitted (library : Library.Contract) (call : Invocation) : Set where
  field
    noCommandIssues : commandIssues library (Invocation.command call) ≡ []
    token : Token (needsToken (Invocation.command call))
    tokenRead : readToken library (needsToken (Invocation.command call)) (Invocation.operationToken call) ≡ inj₂ token

admitParsed : ∀ library call → Correction.Claim ⊎ Admitted library call
admitParsed library call with commandIssues library (Invocation.command call) in issues
... | first ∷ rest = inj₁ (Correction.claim first rest)
... | [] with readToken library (needsToken (Invocation.command call)) (Invocation.operationToken call) in read
... | inj₁ detail = inj₁ detail
... | inj₂ token = inj₂ record { noCommandIssues = issues; token = token; tokenRead = read }

admit : ∀ library call → Correction.Claim ⊎ Admitted library call
admit library call with tokenSyntax library (Invocation.operationToken call)
... | inj₁ detail = inj₁ detail
... | inj₂ tt = admitParsed library call

invalidTokenCannotBeAdmitted : ∀ library call detail →
  readToken library (needsToken (Invocation.command call)) (Invocation.operationToken call) ≡ inj₁ detail →
  Admitted library call → ⊥
invalidTokenCannotBeAdmitted library call detail invalid accepted with
  Relation.Binary.PropositionalEquality.trans (Relation.Binary.PropositionalEquality.sym (Admitted.tokenRead accepted)) invalid
... | ()

-- Native CLI bindings use typed argument values, including numeric defaults.
-- Project is added only when supplied; no implicit null is inserted. The
-- global token is excluded from the immutable business arguments.
record WriteCall : Set where
  constructor writeCall
  field
    tool : Tools.Tool
    writerRole : Tools.kind tool ≡ Tools.businessWrite
    arguments : V.Value

-- These are private read routes, not alternate business-write entry points.
-- In particular listBeliefs is an all-matches read, not an MCP page request.
data ReadCall : Set where
  graphRead : Read.Request → ReadCall
  relevantRead : Text → Ranking.Selection → Maybe Text → Maybe Candidates.Memory → Bool → ReadCall
  evidenceRead : ℕ → ReadCall
  documentRead : Text → Maybe Text → Ranking.Selection → ReadCall

-- Every service command selects one concrete checked write or read path.
-- There is no unhandled-command branch that could report successful no work.
data ServicePlan : Set where
  writeService : WriteCall → ServicePlan
  readService : ReadCall → ServicePlan
  statisticsService : ServicePlan
  contradictionsService : Maybe Text → ServicePlan
  interventionService : ℕ → Float → ServicePlan

planNeedsToken : ServicePlan → Bool
planNeedsToken (writeService _) = true
planNeedsToken (readService _) = false
planNeedsToken statisticsService = false
planNeedsToken (contradictionsService _) = false
planNeedsToken (interventionService _ _) = false

module Arguments (format : Encoding.Formatting) where
  module Encode = Encoding.Encode format

  projectObject : Maybe Text → List (String × V.Value) → V.Value
  projectObject nothing fields = Encoding.object fields
  projectObject (just project) fields = Encoding.object (fields ++ ("project" , V.string project) ∷ [])

  serviceRoute : Library.Contract → ServiceCommand → Validation.Fault ⊎ ServicePlan
  serviceRoute library stats = inj₂ statisticsService
  serviceRoute library (list project limit) = inj₂ (readService (graphRead (Read.listBeliefs project nothing)))
  serviceRoute library (patterns project limit) = inj₂ (readService (graphRead (Read.listPatterns project)))
  serviceRoute library (query text limit evidence project prefer) = inj₂ (readService (relevantRead text limit project prefer evidence))
  serviceRoute library (evidenceAdd chunk belief weight) = inj₂ (writeService (writeCall Tools.addEvidence refl
    (Encoding.object (("chunk_id" , V.string chunk) ∷ ("belief_id" , V.string belief) ∷ ("weight" , Encode.real weight) ∷ []))))
  serviceRoute library (evidenceList belief) = mapResult (λ id → readService (evidenceRead id)) (Input.readUUID library (V.string belief))
  serviceRoute library (deleteBelief id) = inj₂ (writeService (writeCall Tools.deleteBelief refl (Encoding.object (("id" , V.string id) ∷ []))))
  serviceRoute library (deletePattern id) = inj₂ (writeService (writeCall Tools.deletePattern refl (Encoding.object (("id" , V.string id) ∷ []))))
  serviceRoute library (forget project) = inj₂ (writeService (writeCall Tools.deleteProject refl (Encoding.object (("project" , V.string project) ∷ []))))
  serviceRoute library (decay factor project) = inj₂ (writeService (writeCall Tools.decayAll refl (projectObject project (("decay_factor" , Encode.real factor) ∷ []))))
  serviceRoute library (contradictions project) = inj₂ (contradictionsService project)
  serviceRoute library (sweep threshold project) = inj₂ (writeService (writeCall Tools.sweepExpiredDefeated refl (projectObject project (("prob_threshold" , Encode.real threshold) ∷ []))))
  serviceRoute library (docLoad path project) = inj₂ (writeService (writeCall Tools.loadDocument refl (projectObject project (("path" , V.string path) ∷ []))))
  serviceRoute library (docQuery text project limit) = inj₂ (readService (documentRead text project limit))
  serviceRoute library (docClear path) = inj₂ (writeService (writeCall Tools.clearDocument refl (Encoding.object (("path" , V.string path) ∷ []))))
  serviceRoute library (intervene id value) = mapResult (λ identity → interventionService identity value) (Input.readUUID library (V.string id))

  -- Argument construction and the global option gate agree on EVERY route.
  -- A newly added command cannot silently select a write without its token.
  selectedServiceTokenPolicy : ∀ library command plan →
    serviceRoute library command ≡ inj₂ plan → serviceWrites command ≡ planNeedsToken plan
  selectedServiceTokenPolicy library stats plan refl = refl
  selectedServiceTokenPolicy library (list project limit) plan refl = refl
  selectedServiceTokenPolicy library (patterns project limit) plan refl = refl
  selectedServiceTokenPolicy library (query text limit evidence project prefer) plan refl = refl
  selectedServiceTokenPolicy library (evidenceAdd chunk belief weight) plan refl = refl
  selectedServiceTokenPolicy library (deleteBelief id) plan refl = refl
  selectedServiceTokenPolicy library (deletePattern id) plan refl = refl
  selectedServiceTokenPolicy library (forget project) plan refl = refl
  selectedServiceTokenPolicy library (decay factor project) plan refl = refl
  selectedServiceTokenPolicy library (contradictions project) plan refl = refl
  selectedServiceTokenPolicy library (sweep threshold project) plan refl = refl
  selectedServiceTokenPolicy library (docLoad path project) plan refl = refl
  selectedServiceTokenPolicy library (docQuery text project limit) plan refl = refl
  selectedServiceTokenPolicy library (docClear path) plan refl = refl
  selectedServiceTokenPolicy library (evidenceList belief) plan accepted with Input.readUUID library (V.string belief)
  ... | inj₁ error with accepted
  ... | ()
  selectedServiceTokenPolicy library (evidenceList belief) plan accepted | inj₂ identity with accepted
  ... | refl = refl
  selectedServiceTokenPolicy library (intervene id value) plan accepted with Input.readUUID library (V.string id)
  ... | inj₁ error with accepted
  ... | ()
  selectedServiceTokenPolicy library (intervene id value) plan accepted | inj₂ identity with accepted
  ... | refl = refl

  controlTool : OperationCommand → Tools.Tool
  controlTool (reserve _) = Tools.reserveOperation
  controlTool outcome = Tools.operationOutcome
  controlTool cancel = Tools.cancelOperation

  tokenObject : Maybe Text → V.Value
  tokenObject nothing = Encoding.object []
  tokenObject (just token) = Encoding.object (("operation_token" , V.string token) ∷ [])

  controlArguments : OperationCommand → Maybe Text → V.Value
  controlArguments (reserve key) token = Encoding.object (("request_key" , V.string key) ∷ [])
  controlArguments outcome token = tokenObject token
  controlArguments cancel token = tokenObject token

  -- This field is transport data. The checked public decoder removes it
  -- before comparing or storing the original business binding.
  withToken : Text → V.Value → V.Value
  withToken token (V.object fields) = V.object ((toList "operation_token" , V.string token) ∷ fields)
  withToken token raw = raw

  tokenDoesNotChangeBusinessArguments : ∀ token fields →
    Input.withoutField (toList "operation_token") (withToken token (V.object fields)) ≡
    Input.withoutField (toList "operation_token") (V.object fields)
  tokenDoesNotChangeBusinessArguments token fields = refl

listRows : Ranking.Selection → List Graph.BeliefValues → List Graph.BeliefValues
listRows limit rows = Ranking.cap limit (Ranking.sort
  (λ a b → not (Graph.BeliefValues.probability a <ᵇ Graph.BeliefValues.probability b)) rows)

patternRows : Ranking.Selection → List Graph.PatternValues → List Graph.PatternValues
patternRows limit rows = Ranking.cap limit (Ranking.sort
  (λ a b → not (Graph.PatternValues.successRate a <ᵇ Graph.PatternValues.successRate b)) rows)

pair : ℕ × ℕ → ℕ × ℕ
pair (a , b) with a ≤? b
... | yes _ = a , b
... | no _ = b , a

pairMember : ℕ × ℕ → List (ℕ × ℕ) → Bool
pairMember value [] = false
pairMember (a , b) ((c , d) ∷ rest) with does (a ≟ c) ∧ does (b ≟ d)
... | true = true
... | false = pairMember (a , b) rest

-- UUID canonical strings have the same ordering as the represented 128-bit
-- integer. Preserve first occurrence when removing symmetric duplicates.
deduplicate : List (ℕ × ℕ) → List (ℕ × ℕ)
deduplicate = go []
  where
  go : List (ℕ × ℕ) → List (ℕ × ℕ) → List (ℕ × ℕ)
  go seen [] = []
  go seen (value ∷ rest) with pairMember (pair value) seen
  ... | true = go seen rest
  ... | false = pair value ∷ go (pair value ∷ seen) rest

data Parsed : Set where
  help version : Parsed
  invalid : Correction.Claim → Parsed
  parsedCommand : Invocation → Parsed

parseExit : Parsed → Maybe ℕ
parseExit help = just 0
parseExit version = just 0
parseExit (invalid _) = just 0
parseExit (parsedCommand _) = nothing

-- CLI details are part of the same observation as the count, pair selection or
-- numerical calculation. Their content comes from that world, never later reads.
module DatabaseObservations (databaseSum : List Float → Float) (calculator : Posterior.Calculator) where
  module Project = InferenceStore.InterventionRecovery databaseSum calculator
  module N = Project.N

  data Request : Set where
    readStats : Request
    readContradictions : Maybe Text → Request
    readIntervention : ℕ → Float → Request

  PairDetail = ℕ × ℕ × Maybe Graph.BeliefValues × Maybe Graph.BeliefValues
  ProjectionDetail = ℕ × Float × Maybe Graph.BeliefValues

  data Result : Set where
    counts : Read.Statistics → Result
    pairs : List PairDetail → Result
    projection : N.Result → List ProjectionDetail → Result

  contradictionDetails : Maybe Text → Store.World → List PairDetail
  contradictionDetails scope before = map details (deduplicate
    (Numeric.activeContradictions (Records.listBeliefs scope nothing (Store.beliefs before))
      (Stored.contradictions scope before)))
    where
    details : ℕ × ℕ → PairDetail
    details (first , second) = first , second , Ranking.lookup first (Store.beliefs before) ,
      Ranking.lookup second (Store.beliefs before)

  projectionDetails : Store.World → N.Result → List ProjectionDetail
  projectionDetails before (N.calculated updates) = map
    (λ { (identity , value) → identity , value , Ranking.lookup identity (Store.beliefs before) }) updates
  projectionDetails before _ = []

  answer : Request → Store.World → Result
  answer readStats before = counts (Read.statisticsAnswer before)
  answer (readContradictions scope) before = pairs (contradictionDetails scope before)
  answer (readIntervention identity value) before = projection result (projectionDetails before result)
    where result = Project.answer (Project.input identity value) before

  Goal : Request → Store.World → Store.World → Result → Set
  Goal readStats before after (counts value) = after ≡ before × value ≡ Read.statisticsAnswer before
  Goal (readContradictions scope) before after (pairs rows) = after ≡ before × rows ≡ contradictionDetails scope before
  Goal (readIntervention identity value) before after (projection result rows) =
    Project.Goal (Project.input identity value) before after result × rows ≡ projectionDetails before result
  Goal _ _ _ _ = ⊥

  meaning : ∀ input before → Goal input before before (answer input before)
  meaning readStats before = refl , refl
  meaning (readContradictions scope) before = refl , refl
  meaning (readIntervention identity value) before =
    (λ time → Project.answerMeetsGoal time (Project.input identity value) before) , refl

  module ReadOnly = Recovery.ReadOnly answer
  module R = ReadOnly.Checked

  completedMeetsGoal : ∀ input before after reply → R.X.Completed (R.script input) before after reply →
    Goal input before after reply
  completedMeetsGoal input before after reply complete with R.completedMeetsIntent input before after reply complete
  ... | refl = meaning input before

  completedPreservesWholeWorld : ∀ input before after reply → R.X.Completed (R.script input) before after reply → after ≡ before
  completedPreservesWholeWorld input before after reply complete = cong proj₁ (R.completedMeetsIntent input before after reply complete)

  operation : Recovery.RecoverableFor Store.World Request Result Goal
  operation = record
    { Effect = R.Effect; Reply = R.Reply; script = R.script; Atomic = R.Atomic
    ; progress = R.progress
    ; converges = λ input before interrupted after reply interruption complete →
        subst (λ initial → Goal input initial after reply)
          (ReadOnly.interruptedPreservesAllState input before interrupted interruption)
          (completedMeetsGoal input interrupted after reply complete)
    }

  Success : Result → Set
  Success (counts _) = ⊤
  Success (pairs _) = ⊤
  Success (projection result _) = Project.Success result
