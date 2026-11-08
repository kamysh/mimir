{-# OPTIONS --safe #-}
-- Clap supplies typed arguments according to this command surface. Application
-- dispatch, defaults, command-specific reads and output selection are Mimir
-- behavior. Terminal alignment/float formatting is a standard formatter boundary.
module Mimir.CLI where

open import Data.Bool using (Bool; true; false; not; _∧_)
open import Data.Float.Base using (Float; _<ᵇ_)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≟_; _≤?_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.String using (String; toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (does; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.ConfigurationPath as Path
import Mimir.PublicRequest as Public
import Mimir.PublicEncoding as Encoding
import Mimir.PublicInput as Input
import Mimir.ApplicationProtocol as Application
import Mimir.ApplicationOutput as Output
import Mimir.GraphReadProtocol as Read
import Mimir.GraphDeletion as Delete
import Mimir.InferenceProtocol as Inference
import Mimir.CandidateGraph as Graph
import Mimir.LearningCandidates as Candidates
import Mimir.RetrievalRanking as Ranking
import Mimir.StructuredValue as V
import Mimir.Effects as Effects
import Mimir.Validation as Validation
import Mimir.StandardLibrary as Library
import Mimir.McpErrors as Errors
import Mimir.GraphNumerics as Numeric
module Correction = Errors.AgentCorrection
open import Mimir.RecordDecoding using (_>>=_; mapResult)

data JudgeCommand : Set where
  diagnose : Maybe Path.Path → Maybe Path.Path → JudgeCommand
  checkConfig : Maybe Path.Path → JudgeCommand
  run : Maybe Path.Path → Maybe Path.Path → JudgeCommand
  watch : Maybe Path.Path → Maybe Path.Path → ℕ → ℕ → JudgeCommand
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

data ConfigurationCommand : Set where
  check : Maybe Path.Path → ConfigurationCommand
  upgrade : Maybe Path.Path → Maybe Path.Path → ConfigurationCommand

data Command : Set where
  configuration : ConfigurationCommand → Command
  init : List (String × Text) → Command
  service : ServiceCommand → Command
  reembed : Command
  hook : HookCommand → Command
  judge : JudgeCommand → Command

record Defaults : Set where
  field listLimit queryLimit documentLimit : Ranking.Selection
        watchInterval watchFailures : ℕ
        queryEvidence : Bool
        decayFactor threshold evidenceWeight : Float

defaults : Defaults
defaults = record { listLimit = nothing; queryLimit = nothing; documentLimit = nothing; watchInterval = 300; watchFailures = 3
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
requestIssues conversion _ = []

request : Library.Contract → ServiceCommand → Validation.Fault ⊎ Public.Request
request conversion stats = inj₂ (Public.read Read.stats)
request conversion (list project limit) = inj₂ (Public.read (Read.listBeliefs project nothing))
request conversion (patterns project limit) = inj₂ (Public.read (Read.listPatterns project))
request conversion (query text limit evidence project prefer) = inj₂ (Public.relevant text limit project prefer evidence nothing)
request conversion (evidenceAdd chunk belief weight) = Input.readUUID conversion (V.string chunk) >>= λ chunkID →
  Input.readUUID conversion (V.string belief) >>= λ beliefID → inj₂ (Public.addEvidence beliefID chunkID weight)
request conversion (evidenceList belief) = mapResult Public.evidence (Input.readUUID conversion (V.string belief))
request conversion (deleteBelief id) = mapResult (Public.delete Delete.belief) (Input.readUUID conversion (V.string id))
request conversion (deletePattern id) = mapResult (Public.delete Delete.patternNode) (Input.readUUID conversion (V.string id))
request conversion (forget project) = inj₂ (Public.deleteProject project)
request conversion (decay factor project) = inj₂ (Public.inference (Inference.decay project factor))
request conversion (contradictions project) = inj₂ (Public.inference (Inference.contradictions project))
request conversion (sweep threshold project) = inj₂ (Public.sweepConfigured project threshold)
request conversion (docLoad path project) = inj₂ (Public.loadDocument path project)
request conversion (docQuery text project limit) = inj₂ (Public.queryDocument text project limit)
request conversion (docClear path) = inj₂ (Public.clearDocument path)
request conversion (intervene id value) = mapResult (λ target → Public.inference (Inference.intervention target value)) (Input.readUUID conversion (V.string id))

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
  parsedCommand : Command → Parsed

parseExit : Parsed → Maybe ℕ
parseExit help = just 0
parseExit version = just 0
parseExit (invalid _) = just 0
parseExit (parsedCommand _) = nothing

module Run (conversion : Library.Contract) (environment : Application.Environment) (format : Encoding.Formatting) where
  module A = Application.Run environment
  module O = Output.Project environment format

  data Failure : Set where
    connection : Text → Failure
    operation : A.Result → Failure
    output : Text → Failure

  -- Payloads are fully selected application data. A renderer preserves their
  -- complete text, applies terminal layout, and never performs a database read.
  data Line : Set where
    inputDecision : Correction.Claim → Line
    configurationDecision : Application.Correction.Claim → Line
    commandOutput : ServiceCommand → A.Result → Line
    emptyIntervention emptyContradictions : Line
    intervention : ℕ → Float → Maybe Graph.BeliefValues → Line
    contradiction : ℕ → ℕ → Maybe Graph.BeliefValues → Maybe Graph.BeliefValues → Line

  data Effect : Set where
    connect : Effect
    execute : Public.Request → Effect
    print : Line → Effect

  Reply : Effect → Set
  Reply connect = Text ⊎ ⊤
  Reply (execute _) = A.Result
  Reply (print _) = Text ⊎ ⊤
  module P = Effects.Protocol Effect Reply
  open P using (Script; done; ask) renaming (_>>=_ to _then_)

  emit : Line → Script (Failure ⊎ ⊤)
  emit line = ask (print line) λ where
    (inj₁ error) → done (inj₁ (output error))
    (inj₂ tt) → done (inj₂ tt)

  fetch : ℕ → Script (Failure ⊎ Maybe Graph.BeliefValues)
  fetch id = ask (execute (Public.read (Read.getBelief id))) λ where
    (A.readResult (Read.beliefResult value)) → done (inj₂ value)
    result → done (inj₁ (operation result))

  interventions : List (ℕ × Float) → Script (Failure ⊎ ⊤)
  interventions [] = done (inj₂ tt)
  interventions ((id , probability) ∷ rest) = fetch id then λ where
    (inj₁ error) → done (inj₁ error)
    (inj₂ belief) → emit (intervention id probability belief) then λ where
      (inj₁ error) → done (inj₁ error)
      (inj₂ tt) → interventions rest

  contradictionsOutput : List (ℕ × ℕ) → Script (Failure ⊎ ⊤)
  contradictionsOutput [] = done (inj₂ tt)
  contradictionsOutput ((a , b) ∷ rest) = fetch a then λ where
    (inj₁ error) → done (inj₁ error)
    (inj₂ first) → fetch b then λ where
      (inj₁ error) → done (inj₁ error)
      (inj₂ second) → emit (contradiction a b first second) then λ where
        (inj₁ error) → done (inj₁ error)
        (inj₂ tt) → contradictionsOutput rest

  projectResult : ServiceCommand → A.Result → A.Result
  projectResult (list _ limit) (A.readResult (Read.beliefList rows)) = A.readResult (Read.beliefList (listRows limit rows))
  projectResult (patterns _ limit) (A.readResult (Read.patternList rows)) = A.readResult (Read.patternList (patternRows limit rows))
  projectResult command value = value

  success : ServiceCommand → A.Result → Script (Failure ⊎ ⊤)
  success (intervene _ _) (A.inferred (Inference.projected [] _)) = emit emptyIntervention
  success (intervene _ _) (A.inferred (Inference.projected values@(_ ∷ _) _)) = interventions values
  success (contradictions _) (A.inferred (Inference.pairs [])) = emit emptyContradictions
  success (contradictions _) (A.inferred (Inference.pairs values@(_ ∷ _))) = contradictionsOutput (deduplicate values)
  success command value = emit (commandOutput command (projectResult command value))

  after : ServiceCommand → A.Result → Script (Failure ⊎ ⊤)
  after command value with O.project value
  ... | O.failure cause = done (inj₁ (operation cause))
  ... | O.decision report = emit (configurationDecision report)
  ... | O.success _ = success command value

  dispatch : ServiceCommand → Script (Failure ⊎ ⊤)
  dispatch command with request conversion command
  ... | inj₁ error = emit (inputDecision (Correction.claim
      (Correction.item Correction.arguments error
        (toList "Arguments accepted by this Mimir command.")
        (toList "Correct the reported fields and rerun the command. If a required value is unknown, ask the user instead of guessing.")) []))
  ... | inj₂ request with A.admission request
  ...   | inj₁ detail = emit (configurationDecision (Application.configurationCorrection detail))
  ...   | inj₂ tt = ask (execute request) (after command)

  connectThen : ServiceCommand → Script (Failure ⊎ ⊤)
  connectThen command = ask connect λ where
    (inj₁ error) → done (inj₁ (connection error))
    (inj₂ tt) → dispatch command

  start : ServiceCommand → Script (Failure ⊎ ⊤)
  start command with requestIssues conversion command
  ... | [] = connectThen command
  ... | first ∷ rest = emit (inputDecision (Correction.claim first rest))

  invalidPreflightOnlyPrintsCorrection : ∀ command first rest →
    requestIssues conversion command ≡ first ∷ rest →
    start command ≡ emit (inputDecision (Correction.claim first rest))
  invalidPreflightOnlyPrintsCorrection command first rest problems rewrite problems = refl

  invalidPreflightCannotConnect : ∀ command first rest events outcome →
    requestIssues conversion command ≡ first ∷ rest →
    P.Runs (start command) events outcome →
    Σ (Reply (print (inputDecision (Correction.claim first rest))))
      (λ reply → events ≡ ((print (inputDecision (Correction.claim first rest)) , reply) ∷ []))
  invalidPreflightCannotConnect command first rest events outcome problems execution rewrite problems with execution
  ... | P.replied _ _ (inj₁ error) (P.returned _) = inj₁ error , refl
  ... | P.replied _ _ (inj₂ tt) (P.returned _) = inj₂ tt , refl

  exit : Failure ⊎ ⊤ → ℕ
  exit (inj₁ _) = 1
  exit (inj₂ tt) = 0

  -- Every service-effect receipt must have a complete concrete application
  -- execution. This supplies the execution boundary, not an opaque handler.
  data Executed : Public.Request → A.Result → Set where
    application : ∀ request events result → A.Runs (A.start request) events result → Executed request result

  data Receipt : (effect : Effect) → Reply effect → Set where
    connected : ∀ response → Receipt connect response
    printed : ∀ line response → Receipt (print line) response
    executed : ∀ request response → Executed request response → Receipt (execute request) response

  data Runs : Script (Failure ⊎ ⊤) → List P.Event → Failure ⊎ ⊤ → Set where
    returned : ∀ result → Runs (done result) [] result
    responded : ∀ effect continuation reply events result → Receipt effect reply →
      Runs (continuation reply) events result → Runs (ask effect continuation) ((effect , reply) ∷ events) result
