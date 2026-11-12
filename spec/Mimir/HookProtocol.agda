{-# OPTIONS --safe #-}
-- Existing optional CLI hooks. This specification neither installs nor enables
-- a hook. Prompt/pretool scope comes only from the explicit session side file;
-- the legacy Stop command separately implements its current cwd fallback.
module Mimir.HookProtocol where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text; trim)
import Mimir.CLI as CLI
import Mimir.StructuredValue as V
import Mimir.PublicInput as Input
import Mimir.PublicRequest as Public
import Mimir.ApplicationProtocol as Application
import Mimir.GraphReadProtocol as Read
import Mimir.CandidateGraph as Graph
import Mimir.LearningCandidates as Candidates
import Mimir.Effects as Effects
import Mimir.RetrievalProtocol as Retrieval

member : Text → V.Value → Maybe V.Value
member name (V.object fields) = V.Object.normalize fields name
member name _ = nothing

string : Text → V.Value → Maybe Text
string name value with member name value
... | just (V.string text) = just text
... | _ = nothing

active : V.Value → Bool
active value with member (toList "stop_hook_active") value
... | just (V.boolean true) = true
... | _ = false

nonempty : Maybe Text → Maybe Text
nonempty nothing = nothing
nonempty (just text) with trim text
... | [] = nothing
... | clean@(_ ∷ _) = just clean

first : Maybe Text → Maybe Text → Maybe Text
first (just text) _ = just text
first nothing later = later

query : CLI.HookCommand → V.Value → Maybe Text
query CLI.prompt value = nonempty (string (toList "prompt") value)
query CLI.pretooluse value with member (toList "tool_input") value
... | nothing = nothing
... | just input = nonempty (first (string (toList "file_path") input)
    (first (string (toList "path") input) (string (toList "command") input)))
query _ value = nothing

sessionFile : Text → Text
sessionFile id = toList "mimir-session-project-" ++ id

data Message : Set where
  promptContext pretoolContext : Retrieval.Report Graph.BeliefValues → Message
  unconsolidated : List Graph.BeliefValues → Message
  preexisting : Text → List Graph.BeliefValues → Message

module Run (environment : Application.Environment) where
  module A = Application.Run environment using (Result; readResult; relevantResult)

  data Effect : Set where
    stdinUTF8 : Effect
    parseJSON : Text → Effect
    sessionEnvironment : Effect
    readSessionFile : Text → Effect -- selected under std::env::temp_dir()
    writeSessionFile : Text → Text → Effect
    gitTopLevel : Effect
    currentDirectory : Effect
    connect : Effect
    execute : Public.Request → Effect
    stdout stderr : Message → Effect

  Reply : Effect → Set
  Reply stdinUTF8 = Text ⊎ Text
  Reply (parseJSON _) = Text ⊎ V.Value
  Reply sessionEnvironment = Maybe Text -- missing/non-Unicode is None
  Reply (readSessionFile _) = Text ⊎ Text
  Reply (writeSessionFile _ _) = Text ⊎ ⊤
  -- OS path basename/lossy display is a standard path operation. Git reply is
  -- outer Maybe distinguishes command/decode failure from a successful path
  -- having no basename (e.g. root); only outer failure falls back to cwd.
  Reply gitTopLevel = Maybe (Maybe Text)
  Reply currentDirectory = Maybe Text
  Reply connect = Text ⊎ ⊤
  Reply (execute _) = A.Result
  Reply (stdout _) = ⊤
  Reply (stderr _) = ⊤

  module P = Effects.Protocol Effect Reply
  open P using (Script; done; ask; _>>=_)

  sessionScope : V.Value → Script (Maybe Text)
  sessionScope value with string (toList "session_id") value
  ... | nothing = done nothing
  ... | just id = ask (readSessionFile (sessionFile id)) λ where
    (inj₁ _) → done nothing
    (inj₂ text) → done (nonempty (just text))

  -- Basename extraction itself is dependency-owned, but the choice between
  -- explicit project, successful git result and cwd is application policy.
  stopScope : Maybe Text → Script (Maybe Text)
  stopScope (just project) = done (just project)
  stopScope nothing = ask gitTopLevel λ where
    (just project) → done project
    nothing → ask currentDirectory done

  message : CLI.HookCommand → Retrieval.Report Graph.BeliefValues → Message
  message CLI.prompt = promptContext
  message _ = pretoolContext

  deliver : CLI.HookCommand → Retrieval.Report Graph.BeliefValues → Script ℕ
  deliver kind (Retrieval.report _ [] Retrieval.performed) = done 0
  deliver kind (Retrieval.report _ [] Retrieval.noEligibleBeliefs) = done 0
  deliver kind result = ask (stdout (message kind result)) (λ _ → done 0)

  inject : CLI.HookCommand → Text → Maybe Text → Script ℕ
  inject kind text scope = ask connect λ where
    (inj₁ _) → done 0
    (inj₂ tt) → ask (execute (Public.relevant text nothing scope nothing false nothing)) λ where
      (A.relevantResult result) → deliver kind result
      _ → done 0

  stop : Maybe Text → V.Value → Script ℕ
  stop project value with active value
  ... | true = done 0
  ... | false = stopScope project >>= λ scope → ask connect λ where
    (inj₁ _) → done 0
    (inj₂ tt) → ask (execute (Public.read (Read.listBeliefs scope (just Candidates.working)))) λ where
      (A.readResult (Read.beliefList [])) → done 0
      (A.readResult (Read.beliefList beliefs@(_ ∷ _))) → ask (stderr (unconsolidated beliefs)) (λ _ → done 2)
      _ → done 0

  parsed : CLI.HookCommand → V.Value → Script ℕ
  parsed (CLI.stop project) value = stop project value
  parsed kind value with query kind value
  ... | nothing = done 0
  ... | just text = sessionScope value >>= inject kind text

  setProject : Text → Script ℕ
  setProject name = ask sessionEnvironment λ where
    nothing → done 0
    (just id) → ask (writeSessionFile (sessionFile id) name) λ _ → ask connect λ where
      (inj₁ _) → done 0
      (inj₂ tt) → ask (execute (Public.read (Read.listBeliefs (just name) (just Candidates.working)))) λ where
        (A.readResult (Read.beliefList [])) → done 0
        (A.readResult (Read.beliefList beliefs@(_ ∷ _))) → ask (stdout (preexisting name beliefs)) (λ _ → done 0)
        _ → done 0

  start : CLI.HookCommand → Script ℕ
  start (CLI.setProject name) = setProject name
  start kind = ask stdinUTF8 λ where
    (inj₁ _) → done 0
    (inj₂ input) → ask (parseJSON input) λ where
      (inj₁ _) → done 0
      (inj₂ value) → parsed kind value
