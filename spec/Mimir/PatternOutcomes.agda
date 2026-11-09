{-# OPTIONS --safe #-}
-- Outcomes use current experience versions in the requested project. Retrieval
-- does not mutate activation counts or create an observation.
module Mimir.PatternOutcomes where

open import Data.Float.Base using (Float; fromℕ; _+_; _÷_)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _≟_)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
open import Mimir.ExperienceSchema using (Experience; success; failure; unknown)
open import Mimir.SourceSchema using (agentReport; toolResult; userFeedback)
import Data.Empty
import Mimir.LearningStore as Store
import Mimir.ExperienceRead as Read
import Mimir.ReviewObservation as Observation
import Mimir.CandidateGraph as Graph
import Mimir.CandidateProvenance as Provenance

record Counts : Set where
  constructor counts
  field successes failures unknowns : ℕ

observe : Experience → Counts → Counts
observe e c with Experience.provenance e | Experience.outcome e
... | agentReport | _ = counts (Counts.successes c) (Counts.failures c) (suc (Counts.unknowns c))
... | toolResult | unknown = counts (Counts.successes c) (Counts.failures c) (suc (Counts.unknowns c))
... | userFeedback | unknown = counts (Counts.successes c) (Counts.failures c) (suc (Counts.unknowns c))
... | toolResult | success = counts (suc (Counts.successes c)) (Counts.failures c) (Counts.unknowns c)
... | userFeedback | success = counts (suc (Counts.successes c)) (Counts.failures c) (Counts.unknowns c)
... | toolResult | failure = counts (Counts.successes c) (suc (Counts.failures c)) (Counts.unknowns c)
... | userFeedback | failure = counts (Counts.successes c) (suc (Counts.failures c)) (Counts.unknowns c)

accumulate : Text → ℕ → List Read.Row → Counts → Counts
accumulate project id [] c = c
accumulate project id (r ∷ rs) c with Experience.project e ≟Text project
  where e = Observation.Snapshot.experience (Read.Row.snapshot r)
... | no foreign = accumulate project id rs c
... | yes same with Experience.patternID (Observation.Snapshot.experience (Read.Row.snapshot r))
...   | nothing = accumulate project id rs c
...   | just patternID with patternID ≟ id
...     | no different = accumulate project id rs c
...     | yes matches = accumulate project id rs
  (observe (Observation.Snapshot.experience (Read.Row.snapshot r)) c)

probability : Counts → Float
probability c = (1.0 + fromℕ (Counts.successes c)) ÷
  ((2.0 + fromℕ (Counts.successes c)) + fromℕ (Counts.failures c))

record Result : Set where
  constructor result
  field patternValue : Graph.PatternValues; observations : Counts; observedSuccessProbability : Float
        candidateProvenance : Maybe Provenance.Provenance

query : Text → Graph.PatternValues → Store.World → Result
query project p w = result p c (probability c) (Provenance.get (Graph.PatternValues.identity p) w)
  where c = accumulate project (Graph.PatternValues.identity p) (Store.World.current w) (counts 0 0 0)

read : Text → Graph.PatternValues → Store.World → Store.World × Result
read project p w = w , query project p w

retrievalPreservesStore : ∀ project p w → proj₁ (read project p w) ≡ w
retrievalPreservesStore project p w = refl

reportedSuccessIsUnknown : ∀ e c → Experience.provenance e ≡ agentReport →
  observe e c ≡ counts (Counts.successes c) (Counts.failures c) (suc (Counts.unknowns c))
reportedSuccessIsUnknown e c report rewrite report with Experience.outcome e
... | success = refl
... | failure = refl
... | unknown = refl

-- A stored claim and an unknown measurement never become measured success
-- or measured failure merely because retrieval displayed the procedure.
unknownOutcomeCannotBeMeasured : ∀ e c → Experience.outcome e ≡ unknown →
  observe e c ≡ counts (Counts.successes c) (Counts.failures c) (suc (Counts.unknowns c))
unknownOutcomeCannotBeMeasured e c unknownOutcome rewrite unknownOutcome
  with Experience.provenance e
... | agentReport = refl
... | toolResult = refl
... | userFeedback = refl

otherProjectCannotCount : ∀ project id entry rows c →
  (Experience.project (Observation.Snapshot.experience (Read.Row.snapshot entry)) ≡ project → Data.Empty.⊥) →
  accumulate project id (entry ∷ rows) c ≡ accumulate project id rows c
otherProjectCannotCount project id entry rows c foreign
  with Experience.project (Observation.Snapshot.experience (Read.Row.snapshot entry)) ≟Text project
... | no different = refl
... | yes same = Data.Empty.⊥-elim (foreign same)
