{-# OPTIONS --safe #-}
-- Clap supplies typed arguments according to this command surface. Application
-- dispatch, defaults, command-specific reads and output selection are Mimir
-- behavior. Terminal alignment/float formatting is a standard formatter boundary.
module Mimir.CLI where

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_)
open import Data.Float.Base using (Float; _<ᵇ_)
open import Data.List using (List; []; _∷_; _++_; map; take; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≟_; _≤?_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; toList)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (does; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text; trim)
open import Mimir.UUIDGroups using (UUID; _≟UUID_)
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
open import Mimir.RecordDecoding using (_>>=_; mapResult)

data JudgeCommand : Set where
  diagnose : Maybe Path.Path → Maybe Path.Path → JudgeCommand
  checkConfig : Maybe Path.Path → JudgeCommand
  run : Maybe Path.Path → Maybe Path.Path → JudgeCommand
  watch : Maybe Path.Path → Maybe Path.Path → JudgeCommand
  status : Maybe Path.Path → JudgeCommand
  diagnostics : Maybe Path.Path → Bool → Maybe UUID → JudgeCommand

data HookCommand : Set where prompt pretooluse : HookCommand; stop : Maybe Text → HookCommand; setProject : Text → HookCommand

data ServiceCommand : Set where
  stats : ServiceCommand
  list patterns : Maybe Text → Maybe ℕ → ServiceCommand
  query : Text → Maybe ℕ → Bool → Maybe Text → Maybe Candidates.Memory → ServiceCommand
  evidenceAdd : Text → Text → Float → ServiceCommand -- chunk, belief, weight
  evidenceList deleteBelief deletePattern : Text → ServiceCommand
  forget : Text → ServiceCommand
  decay : Float → Maybe Text → ServiceCommand
  contradictions : Maybe Text → ServiceCommand
  sweep : Float → Maybe Text → ServiceCommand
  docLoad : Text → Maybe Text → ServiceCommand
  docQuery : Text → Maybe Text → Maybe ℕ → ServiceCommand
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

-- UUID arguments of these commands are parsed before configuration/database
-- access. Evidence UUIDs are parsed after connection, as in the native command.
validateBeforeConnect : ServiceCommand → Bool
validateBeforeConnect (deleteBelief _) = true
validateBeforeConnect (deletePattern _) = true
validateBeforeConnect (intervene _ _) = true
validateBeforeConnect _ = false

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

listRows : Maybe ℕ → List Graph.BeliefValues → List Graph.BeliefValues
listRows limit rows = Ranking.cap limit (Ranking.sort
  (λ a b → not (Graph.BeliefValues.probability a <ᵇ Graph.BeliefValues.probability b)) rows)

patternRows : Maybe ℕ → List Graph.PatternValues → List Graph.PatternValues
patternRows limit rows = Ranking.cap limit (Ranking.sort
  (λ a b → not (Graph.PatternValues.successRate a <ᵇ Graph.PatternValues.successRate b)) rows)

pairMember : UUID × UUID → List (UUID × UUID) → Bool
pairMember value [] = false
pairMember (a , b) ((c , d) ∷ rest) with
  (does (a ≟UUID c) ∧ does (b ≟UUID d)) ∨ (does (a ≟UUID d) ∧ does (b ≟UUID c))
... | true = true
... | false = pairMember (a , b) rest

-- Preserve first occurrence when removing symmetric duplicates.
deduplicate : List (UUID × UUID) → List (UUID × UUID)
deduplicate = go []
  where
  go : List (UUID × UUID) → List (UUID × UUID) → List (UUID × UUID)
  go seen [] = []
  go seen (value ∷ rest) with pairMember value seen
  ... | true = go seen rest
  ... | false = value ∷ go (value ∷ seen) rest

data Parsed : Set where
  help version : Parsed
  invalid : Bool → Parsed -- first OS argument is exactly "judge"
  parsedCommand : Command → Parsed

parseExit : Parsed → Maybe ℕ
parseExit help = just 0
parseExit version = just 0
parseExit (invalid _) = just 2
parseExit (parsedCommand _) = nothing

module Run (conversion : Library.Contract) (environment : Application.Environment) (format : Encoding.Formatting) where
  module A = Application.Run environment using (Result; inferred; readResult)
  module O = Output.Project environment format using (project; failure; success)

  data Failure : Set where
    connection : Text → Failure
    arguments : Validation.Fault → Failure
    operation : A.Result → Failure
    output : Text → Failure

  -- Payloads contain complete selected application data. Rendering must not
  -- truncate them or perform another database read.
  data Line : Set where
    commandOutput : ServiceCommand → A.Result → Line
    emptyIntervention emptyContradictions : Line
    intervention : UUID → Float → Maybe Graph.BeliefValues → Line
    contradiction : UUID → UUID → Maybe Graph.BeliefValues → Maybe Graph.BeliefValues → Line

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

  fetch : UUID → Script (Failure ⊎ Maybe Graph.BeliefValues)
  fetch id = ask (execute (Public.read (Read.getBelief id))) λ where
    (A.readResult (Read.beliefResult value)) → done (inj₂ value)
    result → done (inj₁ (operation result))

  interventions : List (UUID × Float) → Script (Failure ⊎ ⊤)
  interventions [] = done (inj₂ tt)
  interventions ((id , probability) ∷ rest) = fetch id then λ where
    (inj₁ error) → done (inj₁ error)
    (inj₂ belief) → emit (intervention id probability belief) then λ where
      (inj₁ error) → done (inj₁ error)
      (inj₂ tt) → interventions rest

  contradictionsOutput : List (UUID × UUID) → Script (Failure ⊎ ⊤)
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
  ... | O.success _ = success command value

  dispatch : ServiceCommand → Script (Failure ⊎ ⊤)
  dispatch command with request conversion command
  ... | inj₁ error = done (inj₁ (arguments error))
  ... | inj₂ request = ask (execute request) (after command)

  connectThen : ServiceCommand → Script (Failure ⊎ ⊤)
  connectThen command = ask connect λ where
    (inj₁ error) → done (inj₁ (connection error))
    (inj₂ tt) → dispatch command

  start : ServiceCommand → Script (Failure ⊎ ⊤)
  start command with validateBeforeConnect command
  ... | false = connectThen command
  ... | true with request conversion command
  ...   | inj₁ error = done (inj₁ (arguments error))
  ...   | inj₂ _ = connectThen command

  exit : Failure ⊎ ⊤ → ℕ
  exit (inj₁ _) = 1
  exit (inj₂ tt) = 0
