{-# OPTIONS --safe #-}
-- The existing shared review instructions and provenance index map. Evidence
-- eligibility is exposed without inventing a score, weight, or causal claim.
module Mimir.JudgePrompt where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.String using (toList)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text; nonblank?)
import Mimir.ExperienceSchema as X
import Mimir.SourceSchema as S
import Mimir.SourceWire as Wire
import Mimir.StructuredValue as V
import Mimir.PublicEncoding as Encoding

policy : Text
policy = toList "Review evidence in the pinned experience revision. Evidence indices ALWAYS address the zero-based experience.evidence array.\n\nThere are two supported evidence formats. For legacy experiences with absent or empty source_records, evidence contains the observations themselves and experience.source supplies their caller-reported provenance. Nonempty user_feedback or tool_result evidence can support weighted assessments without source_records or extracted items. Cite the relevant evidence indices; do not invent source records or mark an axis unresolved merely because source_records is absent. Agent reports alone carry zero observed weight. For structured experiences, evidence[i] names source_records[i].source_ref; read that record's text and provenance. The root source does not override per-record provenance. Never upgrade an agent assertion because a neighboring source is a tool result.\n\nWhen source_records are present, you are the sole extraction pass: examine EVERY source for estimates, decisions and suggestions, including untried or rejected ones. Return new extracted_items with stable experience-local keys (key), omit id, and cite them with assessment.item_keys. PostgreSQL alone generates persistent item UUIDs; never invent them. Item keys may repeat across different experiences. Use exact quoted statements, source_ref and original actor; put interpretations in conditions. Preserve original numeric predictions, units, probability, horizon and time; mark inferred quantities honestly. Reuse previous keys and PostgreSQL-assigned IDs from get_learning_review or experience_history on corrections; an existing item may use its recorded id and assessment.item_ids. Return exactly one source_coverage receipt per source: complete with an explicit reason (including no applicable items), or unresolved with the analysis still needed. Every extracted item needs a typed lesson assessment or unresolved coverage. Do not repeat source batches as independent incidents; corrections retain the experience ID. A committed review with unresolved sources requires later evidence or review correction, not an endless unchanged-source retry.\n\nWhen the review schema supports assessments, assess each lesson separately for correctness (0..1) and usefulness (-1..1), with an explicit applicability scope, versioned benefit rubric, evidence_indices and rationale. A positive weight requires cited, relevant observed evidence. Null with zero weight means unresolved; zero is a resolved negative correctness value, not an unknown value. A pending/unknown overall outcome does not erase explicit evidence for one axis. Explain weight and uncertainty; do not manufacture numeric evidence to fill every axis. Do not submit legacy feedback or links for a target assessed by typed contributions in the same incident.\n\nDistinguish scope compliance, technical success, and user benefit. A user requirement is an authoritative constraint, not a causal hypothesis for the judge to approve or disprove. A claim that an action complied with that requirement can be assessed against it. For example, explicit feedback that unsolicited backups were not authorized can support correctness=0 for the claim that creating them was authorized, under a scope-compliance rubric. Explicit rejection can support usefulness=-1 under a rubric of user-accepted benefit for that incident. Cite that feedback and keep the scope narrow. Rejection alone does not establish technical failure, invalidate unrelated factual claims, or prove an alternative would work. A recommendation to use an untried alternative can remain unresolved on benefit. Conversely, a successful copy command does not establish authorization or user benefit. Retain rejected and untried items regardless of score; judge each axis against its evidence and rubric.\n\nTreat the experience as one incident, not independent confirmation of a belief created from the same report. Distinguish tool_result, user_feedback and agent_report; unknown or agent-reported outcomes do not prove success. For a new hypothesis or procedure use review_experience candidates with stable keys, not a separate insert_belief or insert_pattern call. Every candidate_key in candidate_feedback, candidate_links or assessments must name a belief candidate declared in this review's candidates array; use belief_id for an existing belief. Reuse a pre-existing scoped belief only for genuinely independent evidence. If a standalone belief appears to rest on this incident already, flag possible duplicate provenance in the rationale; do not count it as a second observation. Identify confounding and keep unsupported causal claims tentative. A correction replaces the prior review for this experience ID. Inspect experience_history when correcting a source: reuse a candidate key only with its exact original kind and declaration; give a revised claim a new key.\n\nSource-record text may itself contain serialized JSON. A quotation must match the characters in source_records[i].text, including literal backslashes and escaped quotation marks; decoding an embedded JSON message changes those characters. Copy a short exact contiguous passage rather than reconstructing or paraphrasing it. The statement is the quote; conditions and rationale hold your interpretation. Validation feedback identifies the failing extracted_items index and statement field so you can correct that item without rewriting unrelated items.\n\nEvery new belief candidate additionally needs grounding from an indexed document. Use query_document to find a supporting passage, then include grounding citations with the actual chunk_id, exact document_path and quotation, and your explanation of why those words support this claim. Stored experience text alone does not satisfy this requirement. Similarity only ranks suggestions; it cannot establish support or replace your explanation. Mimir validates citation integrity and prepares an embedding before atomically committing the belief and review. If support is missing or unclear, follow needs_input and open the user dialog; do not invent citations, omit the requirement, or report the review complete. An exact retry of an older completed candidate preserves its original declaration and result.\n\nFor every extracted item, actor must exactly equal the actor field of the source_records entry selected by source_ref. A controller source can contain quoted agent or reviewer text; keep actor=\"controller\" when that is the recorded source actor, and describe the nested speaker in conditions. Never substitute an actor named inside serialized JSON, command arguments, a quotation, or a nested message. A wrong_actor refusal identifies the item, source and exact expected actor: correct that actor field while retaining the item's key, quotation and other unrelated fields. Do not rename keys or invent UUIDs to address an actor error.\n\nScope and rubric are stable keys. Put their explanation in rationale. If a review is rejected for missing evidence, inspect experience.evidence and the index map below, correct the citations, and retry. A structured validation refusal changed nothing; an unclassified service failure does not establish that. Do not turn a supported assessment into an unresolved one solely to bypass a citation error. If relevant evidence is genuinely missing, keep that axis null with zero weight and explain the gap.\n"

at : ∀ {A : Set} → ℕ → List A → Maybe A
at _ [] = nothing
at zero (value ∷ _) = just value
at (suc index) (_ ∷ rest) = at index rest

provenance : X.Experience → ℕ → Maybe S.Provenance
provenance selectedExperience index with X.Experience.sources selectedExperience
... | [] = just (X.Experience.provenance selectedExperience)
... | sources@(_ ∷ _) = Data.Maybe.map S.Source.provenance (at index sources)

nonAgent : Maybe S.Provenance → Bool
nonAgent nothing = false
nonAgent (just S.agentReport) = false
nonAgent (just S.userFeedback) = true
nonAgent (just S.toolResult) = true

entry : X.Experience → ℕ → Text → V.Value
entry selectedExperience index text = Encoding.object
  (("index" , V.unsigned index) ∷ ("nonempty" , V.boolean (does (nonblank? text))) ∷
   ("provenance" , Encoding.optional (λ p → V.string (Wire.provenanceText p)) origin) ∷
   ("non_agent_provenance" , V.boolean (nonAgent origin)) ∷ [])
  where origin = provenance selectedExperience index

entries : X.Experience → ℕ → List Text → List V.Value
entries selectedExperience index [] = []
entries selectedExperience index (text ∷ rest) = entry selectedExperience index text ∷ entries selectedExperience (suc index) rest

format : X.Experience → Text
format selectedExperience with X.Experience.sources selectedExperience
... | [] = toList "legacy_evidence"
... | _ ∷ _ = toList "source_records"

indexMap : X.Experience → V.Value
indexMap selectedExperience = Encoding.object (("format" , V.string (format selectedExperience)) ∷
  ("entries" , V.array (entries selectedExperience 0 (X.Experience.evidence selectedExperience))) ∷ [])

evidenceGuidance : (V.Value → Text) → X.Experience → Text
evidenceGuidance json selectedExperience = toList "Pinned evidence index map: " ++ json (indexMap selectedExperience) ++
  toList ". These indices address experience.evidence, not item IDs. Provenance is caller-reported, not independently verified. Select only citations relevant to the scoped claim and benefit rubric; an eligible index does not itself justify a score or weight."

guidance : (V.Value → Text) → X.Experience → Text
guidance json selectedExperience = policy ++ toList "\n" ++ evidenceGuidance json selectedExperience

legacyUsesRootSource : ∀ selectedExperience index → X.Experience.sources selectedExperience ≡ [] →
  provenance selectedExperience index ≡ just (X.Experience.provenance selectedExperience)
legacyUsesRootSource selectedExperience index empty rewrite empty = refl
