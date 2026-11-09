{-# OPTIONS --safe #-}
-- Upgrade edits operational metadata and removes retired application limits; unrelated payload and
-- comments are preserved by the TOML document editor. No fallback on malformed
-- input and no downgrade of a future format. Publication uses the existing
-- owned-temporary-file, fsync, rename protocol; no backup is produced.
module Mimir.ConfigurationUpgrade where

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Data.String using (String; toList)
open import Data.Unit using (⊤; tt)
open import Mimir.Text using (Text)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.StructuredValue as V
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≟_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
open import Mimir.Validation using (Fault)
import Mimir.OperationalConfiguration as O
import Mimir.PublicInput as Input
import Mimir.Recovery as Recovery
import Mimir.AtomicFile as AtomicFile

-- Only these obsolete application budgets are removed. Other settings retain
-- their values and order, including model/provider credentials.
llmKeys judgeKeys emailKeys embeddingKeys : List String
llmKeys = "timeout_seconds" ∷ "max_calls" ∷ "max_output_tokens" ∷ "max_budget_usd" ∷ []
judgeKeys = "batch_size" ∷ []
emailKeys = "timeout_seconds" ∷ "retry_seconds" ∷ "max_attempts" ∷ []
embeddingKeys = "batch_size" ∷ []

named : List String → Text → Bool
named [] key = false
named (name ∷ rest) key = does (key ≟Text toList name) ∨ named rest key

retired : Text → Bool
retired = named llmKeys

-- The checker and upgrader share the same retired key sets. Values, including
-- an old wrong type, never become a replacement policy or enter the message.
checkOptional : String → List String → Maybe V.Value → Text ⊎ ⊤
checkOptional section keys nothing = inj₂ tt
checkOptional section [] (just raw) = inj₂ tt
checkOptional section (name ∷ names) (just raw) with Input.view raw (toList name)
... | nothing = checkOptional section names (just raw)
... | just value = inj₁ (toList section ++ toList "." ++ toList name ++
  toList " is obsolete: run `mimir config upgrade` to remove retired application limits, then `mimir config check`. Other settings and comments are preserved")

Fields = List (Text × V.Value)

setField : Text → V.Value → Fields → Fields
setField name value [] = (name , value) ∷ []
setField name value ((key , old) ∷ rest) with name ≟Text key
... | yes _ = (key , value) ∷ rest
... | no _ = (key , old) ∷ setField name value rest

setFieldStable : ∀ name value fields → setField name value (setField name value fields) ≡ setField name value fields
setFieldStable name value [] with name ≟Text name
... | yes _ = refl
... | no impossible = ⊥-elim (impossible refl)
setFieldStable name value ((key , old) ∷ rest) with name ≟Text key in matching
... | yes _ rewrite matching = refl
... | no _ rewrite matching = cong ((key , old) ∷_) (setFieldStable name value rest)

module Filter (isRetired : Text → Bool) where
  removeRetired : Fields → Fields
  removeRetired [] = []
  removeRetired ((key , value) ∷ rest) with isRetired key
  ... | true = removeRetired rest
  ... | false = (key , value) ∷ removeRetired rest

  -- A receipt accounts for every input setting; only a retired key can disappear.
  data Migration : Fields → Fields → Set where
    empty : Migration [] []
    removed : ∀ key value before after → isRetired key ≡ true → Migration before after →
      Migration ((key , value) ∷ before) after
    preserved : ∀ key value before after → isRetired key ≡ false → Migration before after →
      Migration ((key , value) ∷ before) ((key , value) ∷ after)

  migrationComplete : ∀ fields → Migration fields (removeRetired fields)
  migrationComplete [] = empty
  migrationComplete ((key , value) ∷ rest) with isRetired key in eq
  ... | true = removed key value rest (removeRetired rest) eq (migrationComplete rest)
  ... | false = preserved key value rest (removeRetired rest) eq (migrationComplete rest)

  migrationIdempotent : ∀ fields → removeRetired (removeRetired fields) ≡ removeRetired fields
  migrationIdempotent [] = refl
  migrationIdempotent ((key , value) ∷ rest) with isRetired key in eq
  ... | true = migrationIdempotent rest
  ... | false rewrite eq = cong ((key , value) ∷_) (migrationIdempotent rest)

  -- Updating a retained key and removing retired keys commute. In particular
  -- an explicit logging directory survives exactly, without disturbing other
  -- user settings or gaining a different value on the next invocation.
  setRetained : ∀ name value fields → isRetired name ≡ false →
    removeRetired (setField name value fields) ≡ setField name value (removeRetired fields)
  setRetained name value [] retained rewrite retained = refl
  setRetained name value ((key , old) ∷ rest) retained with name ≟Text key in matching
  ... | yes refl rewrite retained | matching = refl
  ... | no different with isRetired key in removed
  ...   | true = setRetained name value rest retained
  ...   | false rewrite matching = cong ((key , old) ∷_) (setRetained name value rest retained)

module Llm = Filter retired
open Llm public

loggingRetired : Text → Bool
loggingRetired name = does (name ≟Text toList "max_file_bytes") ∨ does (name ≟Text toList "retained_files")

module Logging = Filter loggingRetired

directoryFields : Text → Fields → Fields
directoryFields directory = setField (toList "directory") (V.string directory)

directoryRetained : ∀ directory fields →
  directoryFields directory (Logging.removeRetired (directoryFields directory fields)) ≡
    Logging.removeRetired (directoryFields directory fields)
directoryRetained directory fields = trans
  (sym (Logging.setRetained (toList "directory") (V.string directory)
    (directoryFields directory fields) refl))
  (cong Logging.removeRetired (setFieldStable (toList "directory") (V.string directory) fields))

judgeRetired : Text → Bool
judgeRetired = named judgeKeys

module Judge = Filter judgeRetired

emailRetired : Text → Bool
emailRetired = named emailKeys

module Email = Filter emailRetired

module Embeddings = Filter (named embeddingKeys)

upgradeEmbeddings : Maybe Fields → Maybe Fields
upgradeEmbeddings nothing = nothing
upgradeEmbeddings (just fields) = just (Embeddings.removeRetired fields)

upgradeEmail : Maybe Fields → Maybe Fields
upgradeEmail nothing = nothing
upgradeEmail (just fields) = just (Email.removeRetired fields)

upgradeJudge : Maybe Fields → Maybe Fields
upgradeJudge nothing = nothing
upgradeJudge (just fields) = just (Judge.removeRetired fields)

upgradeLlm : Maybe Fields → Maybe Fields
upgradeLlm nothing = nothing
upgradeLlm (just fields) = just (removeRetired fields)

module Document (Payload : Set) where
  record Before : Set where
    constructor before
    field version : Maybe ℕ; logging : Fields; llm judge email embeddings : Maybe Fields; payload : Payload
  record After : Set where
    constructor after
    field operations : O.Admitted; logging : Fields; llm judge email embeddings : Maybe Fields; payload : Payload
  data Failure : Set where futureVersion : Failure; invalid : Fault → Failure

  validate : Before → Failure ⊎ After
  validate old with O.decodeLogging (V.object (Logging.removeRetired (Before.logging old)))
  ... | inj₁ fault = inj₁ (invalid fault)
  ... | inj₂ logs with O.admit (O.settings O.formatVersion logs)
  ...   | inj₁ fault = inj₁ (invalid fault)
  ...   | inj₂ accepted = inj₂ (after accepted (Logging.removeRetired (Before.logging old))
    (upgradeLlm (Before.llm old)) (upgradeJudge (Before.judge old))
    (upgradeEmail (Before.email old)) (upgradeEmbeddings (Before.embeddings old)) (Before.payload old))

  upgrade : Before → Failure ⊎ After
  upgrade old with Before.version old
  ... | nothing = validate old
  ... | just version with version ≟ O.formatVersion
  ...   | yes _ = validate old
  ...   | no _ = inj₁ futureVersion

  -- A successful upgrade is a complete document, not a sequence of settings
  -- to apply again. Readback retains every unrelated field and comment in
  -- payload, and exposes the admitted version for the next invocation.
  readback : After → Before
  readback current = before (just O.formatVersion) (After.logging current)
    (After.llm current) (After.judge current) (After.email current)
    (After.embeddings current) (After.payload current)

  optionalLlmFixed : ∀ fields → upgradeLlm (upgradeLlm fields) ≡ upgradeLlm fields
  optionalLlmFixed nothing = refl
  optionalLlmFixed (just fields) = cong just (migrationIdempotent fields)

  optionalJudgeFixed : ∀ fields → upgradeJudge (upgradeJudge fields) ≡ upgradeJudge fields
  optionalJudgeFixed nothing = refl
  optionalJudgeFixed (just fields) = cong just (Judge.migrationIdempotent fields)

  optionalEmailFixed : ∀ fields → upgradeEmail (upgradeEmail fields) ≡ upgradeEmail fields
  optionalEmailFixed nothing = refl
  optionalEmailFixed (just fields) = cong just (Email.migrationIdempotent fields)

  optionalEmbeddingsFixed : ∀ fields → upgradeEmbeddings (upgradeEmbeddings fields) ≡ upgradeEmbeddings fields
  optionalEmbeddingsFixed nothing = refl
  optionalEmbeddingsFixed (just fields) = cong just (Embeddings.migrationIdempotent fields)

  validatedReadback : ∀ old current → validate old ≡ inj₂ current →
    validate (readback current) ≡ inj₂ current
  validatedReadback old current proof
    with O.decodeLogging (V.object (Logging.removeRetired (Before.logging old))) in decoded
  ... | inj₁ fault with proof
  ...   | ()
  validatedReadback old current proof | inj₂ logs
    with O.admit (O.settings O.formatVersion logs) in admitted
  ... | inj₁ fault with proof
  ...   | ()
  validatedReadback old .(after accepted (Logging.removeRetired (Before.logging old))
      (upgradeLlm (Before.llm old)) (upgradeJudge (Before.judge old))
      (upgradeEmail (Before.email old)) (upgradeEmbeddings (Before.embeddings old)) (Before.payload old)) refl
      | inj₂ logs | inj₂ accepted
    rewrite Logging.migrationIdempotent (Before.logging old) | decoded | admitted
      | optionalLlmFixed (Before.llm old) | optionalJudgeFixed (Before.judge old)
      | optionalEmailFixed (Before.email old) | optionalEmbeddingsFixed (Before.embeddings old)
      | Logging.migrationIdempotent (Before.logging old) = refl

  -- Every successful transformation is a fixed point. A process interrupted
  -- after replacement may safely read the complete new file and retry; it
  -- cannot remove another setting or change the preserved payload on retry.
  upgradedReadback : ∀ old current → upgrade old ≡ inj₂ current →
    upgrade (readback current) ≡ inj₂ current
  upgradedReadback old current proof with Before.version old
  ... | nothing with O.formatVersion ≟ O.formatVersion
  ...   | yes _ = validatedReadback old current proof
  ...   | no different = ⊥-elim (different refl)
  upgradedReadback old current proof | just version with version ≟ O.formatVersion
  ... | no different with proof
  ...   | ()
  upgradedReadback old current proof | just version | yes same with O.formatVersion ≟ O.formatVersion
  ... | yes _ = validatedReadback old current proof
  ... | no different = ⊥-elim (different refl)

  withDirectory : Maybe Text → Before → Before
  withDirectory nothing old = old
  withDirectory (just directory) old = record old { logging = directoryFields directory (Before.logging old) }

  requestedUpgrade : Maybe Text → Before → Failure ⊎ After
  requestedUpgrade directory old = upgrade (withDirectory directory old)

  validatedLogging : ∀ old current → validate old ≡ inj₂ current →
    After.logging current ≡ Logging.removeRetired (Before.logging old)
  validatedLogging old current proof with O.decodeLogging (V.object (Logging.removeRetired (Before.logging old)))
  ... | inj₁ fault with proof
  ...   | ()
  validatedLogging old current proof | inj₂ logs with O.admit (O.settings O.formatVersion logs)
  ... | inj₁ fault with proof
  ...   | ()
  validatedLogging old .(after accepted (Logging.removeRetired (Before.logging old))
    (upgradeLlm (Before.llm old)) (upgradeJudge (Before.judge old))
    (upgradeEmail (Before.email old)) (upgradeEmbeddings (Before.embeddings old)) (Before.payload old)) refl
    | inj₂ logs | inj₂ accepted = refl

  upgradedLogging : ∀ old current → upgrade old ≡ inj₂ current →
    After.logging current ≡ Logging.removeRetired (Before.logging old)
  upgradedLogging old current proof with Before.version old
  ... | nothing = validatedLogging old current proof
  ... | just version with version ≟ O.formatVersion
  ...   | yes _ = validatedLogging old current proof
  ...   | no _ with proof
  ...     | ()

  requestedReadback : ∀ directory old current → requestedUpgrade directory old ≡ inj₂ current →
    requestedUpgrade directory (readback current) ≡ inj₂ current
  requestedReadback nothing old current upgraded = upgradedReadback old current upgraded
  requestedReadback (just directory) old current upgraded = trans
    (cong upgrade same) (upgradedReadback (withDirectory (just directory) old) current upgraded)
    where
    selected : After.logging current ≡ Logging.removeRetired (directoryFields directory (Before.logging old))
    selected = upgradedLogging (withDirectory (just directory) old) current upgraded
    fixed : directoryFields directory (After.logging current) ≡ After.logging current
    fixed = trans (cong (directoryFields directory) selected)
      (trans (directoryRetained directory (Before.logging old)) (sym selected))
    same : withDirectory (just directory) (readback current) ≡ readback current
    same = cong (λ fields → before (just O.formatVersion) fields
      (After.llm current) (After.judge current) (After.email current)
      (After.embeddings current) (After.payload current)) fixed

  -- A semantic command result does not expose the prepared document. Its
  -- successful reply stays successful on retry, including an unchanged file.
  Result = Failure ⊎ ⊤

  normalize : Maybe Text → Before → Before × Result
  normalize directory old with requestedUpgrade directory old
  ... | inj₁ failure = old , inj₁ failure
  ... | inj₂ current = readback current , inj₂ tt

  normalizeStable : ∀ directory old → normalize directory (proj₁ (normalize directory old)) ≡ normalize directory old
  normalizeStable directory old with requestedUpgrade directory old in upgraded
  ... | inj₁ failure rewrite upgraded = refl
  ... | inj₂ current rewrite requestedReadback directory old current upgraded = refl

  -- The complete selected file and every unrelated application component are
  -- observed together. Private preparation cannot alter this world. The final
  -- publication uses AtomicFile's complete-file replacement boundary, rather
  -- than exposing a partially edited target.
  module Replacement (Frame : Set) (directory : Maybe Text) where
    module Storage = AtomicFile.Storage Before Frame
    open Storage using (World; world)

    -- Keep both the visible file and its confirmed durable mapping. Successful
    -- completion establishes both; a failed validation changes neither one.
    outcome : World → World × Result
    outcome stateNow@(world old durable frame) with requestedUpgrade directory old
    ... | inj₁ failure = stateNow , inj₁ failure
    ... | inj₂ current = world (readback current) (readback current) frame , inj₂ tt

    outcomeStable : ∀ stateNow → outcome (proj₁ (outcome stateNow)) ≡ outcome stateNow
    outcomeStable (world old durable frame) with requestedUpgrade directory old in upgraded
    ... | inj₁ failure rewrite upgraded = refl
    ... | inj₂ current rewrite requestedReadback directory old current upgraded = refl

    framePreserved : ∀ stateNow → Storage.World.others (proj₁ (outcome stateNow)) ≡ Storage.World.others stateNow
    framePreserved (world old durable frame) with requestedUpgrade directory old
    ... | inj₁ failure = refl
    ... | inj₂ current = refl

    data Effect : Set where
      inspect : Effect
      prepareComplete : Before → Effect
      replaceComplete : Before → After → Effect
      syncParent : Effect

    Reply : Effect → Set
    Reply inspect = Before
    Reply _ = ⊤

    data Atomic : World → (effect : Effect) → Reply effect → World → Set where
      inspected : ∀ old durable frame → Atomic (world old durable frame) inspect old (world old durable frame)
      prepared : ∀ stateNow current → Atomic stateNow (prepareComplete current) tt stateNow
      replaced : ∀ old current durable frame → requestedUpgrade directory old ≡ inj₂ current →
        Atomic (world old durable frame) (replaceComplete old current) tt
          (Storage.renameValue (readback current) (world old durable frame))
      synced : ∀ old current durable frame → requestedUpgrade directory old ≡ inj₂ current →
        Atomic (world (readback current) durable frame) syncParent tt
          (Storage.syncValue (world (readback current) durable frame))

    module X = Recovery.Execution World Effect Reply Atomic
    module E = X.E
    module G = Recovery.Outcome World Result

    -- Private creation, complete write, sync and original-content recheck all
    -- precede replaceComplete and preserve the selected file. If any fails,
    -- execution is interrupted. An unchanged complete file may skip physical
    -- preparation/replacement; it has the same semantic observations.
    afterRead : Before → E.Script Result
    afterRead old with requestedUpgrade directory old
    ... | inj₁ failure = E.done (inj₁ failure)
    ... | inj₂ current = E.ask (prepareComplete (readback current)) λ _ →
      E.ask (replaceComplete old current) λ _ → E.ask syncParent λ _ → E.done (inj₂ tt)

    script : E.Script Result
    script = E.ask inspect afterRead

    replacementPreservesOutcome : ∀ old current durable frame → requestedUpgrade directory old ≡ inj₂ current →
      outcome (Storage.renameValue (readback current) (world old durable frame)) ≡ outcome (world old durable frame)
    replacementPreservesOutcome old current durable frame upgraded
      rewrite upgraded | requestedReadback directory old current upgraded = refl

    syncPreservesOutcome : ∀ old current durable frame → requestedUpgrade directory old ≡ inj₂ current →
      outcome (Storage.syncValue (world (readback current) durable frame)) ≡ outcome (world (readback current) durable frame)
    syncPreservesOutcome old current durable frame upgraded
      rewrite requestedReadback directory old current upgraded = refl

    atomicInvariant : ∀ stateNow effect reply nextState → Atomic stateNow effect reply nextState →
      outcome nextState ≡ outcome stateNow
    atomicInvariant _ _ _ _ (inspected old durable frame) = refl
    atomicInvariant _ _ _ _ (prepared stateNow current) = refl
    atomicInvariant _ _ _ _ (replaced old current durable frame upgraded) =
      replacementPreservesOutcome old current durable frame upgraded
    atomicInvariant _ _ _ _ (synced old current durable frame upgraded) =
      syncPreservesOutcome old current durable frame upgraded

    changesInvariant : ∀ stateNow events nextState → X.Changes stateNow events nextState → outcome nextState ≡ outcome stateNow
    changesInvariant stateNow .[] .stateNow (X.unchanged .stateNow) = refl
    changesInvariant stateNow _ finalState (X.changed _ effect reply middle physical rest) =
      trans (changesInvariant middle _ finalState rest) (atomicInvariant stateNow effect reply middle physical)

    interruptedInvariant : ∀ initialState finalState → X.Interrupted script initialState finalState → outcome finalState ≡ outcome initialState
    interruptedInvariant initialState finalState (X.atPrefix events residual .finalState prefix physical) =
      changesInvariant initialState events finalState physical
    interruptedInvariant initialState finalState
      (X.beforeReply events effect continuation current reply .finalState prefix physical publication) =
      trans (atomicInvariant current effect reply finalState publication) (changesInvariant initialState events current physical)

    readObservation : ∀ old durable frame finalState result events →
      E.Runs (afterRead old) events result → X.Changes (world old durable frame) events finalState →
      (finalState , result) ≡ outcome (world old durable frame)
    readObservation old durable frame finalState result events execution physical with requestedUpgrade directory old in upgraded
    ... | inj₁ failure with execution | physical
    ...   | E.returned _ | X.unchanged _ = refl
    readObservation old durable frame finalState result events execution physical | inj₂ current
      with execution | physical
    ... | E.replied _ _ tt (E.replied _ _ tt (E.replied _ _ tt (E.returned _)))
      | X.changed _ _ _ _ (prepared _ _) (X.changed _ _ _ _ (replaced _ _ _ _ _) (X.changed _ _ _ _ (synced _ _ _ _ _) (X.unchanged _))) = refl

    completedObservation : ∀ initialState finalState result → X.Completed script initialState finalState result →
      (finalState , result) ≡ outcome initialState
    completedObservation .(world old durable frame) finalState result
      (X.completed _ (E.replied _ _ old execution) (X.changed _ _ _ _ (inspected .old durable frame) physical)) =
      readObservation old durable frame finalState result _ execution physical

    readProgress : ∀ old durable frame → Σ World (λ finalState → Σ Result (λ result →
      X.Completed (afterRead old) (world old durable frame) finalState result))
    readProgress old durable frame with requestedUpgrade directory old in upgraded
    ... | inj₁ failure = world old durable frame , inj₁ failure , X.completed [] (E.returned _) (X.unchanged _)
    ... | inj₂ current = world (readback current) (readback current) frame , inj₂ tt , X.completed
      ((prepareComplete (readback current) , tt) ∷ (replaceComplete old current , tt) ∷ (syncParent , tt) ∷ [])
      (E.replied _ _ tt (E.replied _ _ tt (E.replied _ _ tt (E.returned _))))
      (X.changed _ _ _ _ (prepared _ _) (X.changed _ _ _ _ (replaced old current durable frame upgraded)
        (X.changed _ _ _ _ (synced old current durable frame upgraded) (X.unchanged _))))

    -- The existing filesystem model permits either old or new complete data
    -- after power loss before directory sync. Starting with a durable original,
    -- BOTH observations give the same intended completed retry.
    recoveredReplacement : ∀ old current frame recovered → requestedUpgrade directory old ≡ inj₂ current →
      Storage.Recovered (Storage.renameValue (readback current) (world old old frame)) recovered →
      outcome (world recovered recovered frame) ≡ outcome (world old old frame)
    recoveredReplacement old current frame .old upgraded Storage.previous = refl
    recoveredReplacement old current frame .(readback current) upgraded Storage.renamed
      rewrite upgraded | requestedReadback directory old current upgraded = refl

    intent : G.Intent ⊤
    intent = record { intended = λ _ initialState → proj₁ (outcome initialState); expectedReply = λ _ initialState → proj₂ (outcome initialState) }

    recoverable : Recovery.Recoverable World ⊤
    recoverable = record
      { Result = Result; Effect = Effect; Reply = Reply; script = λ _ → script; Atomic = Atomic; intent = intent
      ; converges = λ _ initial interrupted final reply crash completion →
          trans (completedObservation interrupted final reply completion) (interruptedInvariant initial interrupted crash)
      ; progress = λ { _ (world old durable frame) → prepend old durable frame (readProgress old durable frame) }
      }
      where
      prepend : ∀ old durable frame → Σ World (λ finalState → Σ Result (λ result → X.Completed (afterRead old) (world old durable frame) finalState result)) →
        Σ World (λ finalState → Σ Result (λ result → X.Completed script (world old durable frame) finalState result))
      prepend old durable frame (finalState , result , X.completed events execution physical) = finalState , result ,
        X.completed ((inspect , old) ∷ events) (E.replied _ _ old execution)
          (X.changed _ _ _ _ (inspected old durable frame) physical)

  payloadPreserved : ∀ old new → validate old ≡ inj₂ new → After.payload new ≡ Before.payload old
  payloadPreserved old new proof with O.decodeLogging (V.object (Logging.removeRetired (Before.logging old)))
  ... | inj₁ fault with proof
  ...   | ()
  payloadPreserved old new proof | inj₂ logs with O.admit (O.settings O.formatVersion logs)
  ... | inj₁ fault with proof
  ...   | ()
  payloadPreserved old .(after accepted (Logging.removeRetired (Before.logging old))
    (upgradeLlm (Before.llm old)) (upgradeJudge (Before.judge old))
    (upgradeEmail (Before.email old)) (upgradeEmbeddings (Before.embeddings old)) (Before.payload old)) refl | inj₂ logs | inj₂ accepted = refl

  -- Startup requires the admitted value, so the new package cannot execute
  -- application I/O using absent or incompatible operational settings.
  data Started : After → Set where start : ∀ ready → Started ready
  startedCompatible : ∀ ready → Started ready →
    O.Settings.version (O.Admitted.value (After.operations ready)) ≡ O.formatVersion
  startedCompatible ready _ = O.acceptedVersion (After.operations ready)
