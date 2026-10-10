{-# OPTIONS --safe #-}
-- General contracts for the Rust learning port. IDs/projects/versions are
-- abstract natural identities, not an encoding of UUID parsing or SQL I/O.
module Mimir.LearningContracts where

open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Nat.Properties using (suc-injective)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym; trans)
open import Data.Empty using (⊥-elim)

not-successor : ∀ n → n ≢ suc n
not-successor zero ()
not-successor (suc n) eq = not-successor n (suc-injective eq)

-- Pointwise equality avoids function extensionality or other added axioms.
module Ownership (Value : Set) where
  World = ℕ → Value

  write : ℕ → Value → World → World
  write key value world queried with queried ≟ key
  ... | yes _ = value
  ... | no _ = world queried

  write-own : ∀ key value world → write key value world key ≡ value
  write-own key value world with key ≟ key
  ... | yes _ = refl
  ... | no neq = ⊥-elim (neq refl)

  write-other : ∀ key other value world → other ≢ key →
    write key value world other ≡ world other
  write-other key other value world neq with other ≟ key
  ... | yes eq = ⊥-elim (neq eq)
  ... | no _ = refl

  -- Replacement discards every earlier contribution from this identity.
  replacement-forgets-old : ∀ key newer older world queried →
    write key newer (write key older world) queried ≡ write key newer world queried
  replacement-forgets-old key newer older world queried with queried ≟ key
  ... | yes _ = refl
  ... | no neq = write-other key queried older world neq

  -- Removing a review restores the independent base at that identity.
  retraction-restores-base : ∀ key value (base : World) world queried →
    write key (base key) (write key value world) queried ≡
    write key (base key) world queried
  retraction-restores-base key value base world queried =
    replacement-forgets-old key (base key) value world queried

  scoped : (ℕ → ℕ) → ℕ → World → World → World
  scoped owner project before proposed id with owner id ≟ project
  ... | yes _ = proposed id
  ... | no _ = before id

  foreign-write-refused : ∀ owner project before proposed id → owner id ≢ project →
    scoped owner project before proposed id ≡ before id
  foreign-write-refused owner project before proposed id neq with owner id ≟ project
  ... | yes eq = ⊥-elim (neq eq)
  ... | no _ = refl

-- A candidate's stable key is (experience, local candidate key). The assigned
-- node ID (belief or pattern) is retained when the contribution is retracted.
-- Kind/content validation precedes reservation in the adapter. These identity
-- laws do not turn a pattern declaration into an observed successful use.
module Candidates where
  open Ownership (Maybe ℕ) renaming (World to Slots)
  Registry = ℕ → Slots

  bind : ℕ → ℕ → ℕ → Registry → Registry
  bind experience key fresh registry = Ownership.write Slots experience
    (write key (just fresh) (registry experience)) registry

  bind-own : ∀ experience key fresh registry →
    bind experience key fresh registry experience key ≡ just fresh
  bind-own experience key fresh registry =
    trans (cong (λ slots → slots key)
      (Ownership.write-own Slots experience (write key (just fresh) (registry experience)) registry))
      (write-own key (just fresh) (registry experience))

  reserve : ℕ → ℕ → ℕ → Registry → Registry
  reserve experience key fresh registry with registry experience key
  ... | just existing = registry
  ... | nothing = bind experience key fresh registry

  existing-identity-stable : ∀ experience key fresh registry existing →
    registry experience key ≡ just existing →
    reserve experience key fresh registry ≡ registry
  existing-identity-stable experience key fresh registry existing eq
    rewrite eq = refl

  reserve-own : ∀ experience key fresh registry → registry experience key ≡ nothing →
    reserve experience key fresh registry experience key ≡ just fresh
  reserve-own experience key fresh registry absent rewrite absent =
    trans (cong (λ slots → slots key)
      (Ownership.write-own Slots experience (write key (just fresh) (registry experience)) registry))
      (write-own key (just fresh) (registry experience))

  reserve-idempotent : ∀ experience key fresh registry →
    reserve experience key fresh (reserve experience key fresh registry) ≡
    reserve experience key fresh registry
  reserve-idempotent experience key fresh registry with registry experience key in eq
  ... | just existing = existing-identity-stable experience key fresh registry existing eq
  ... | nothing = existing-identity-stable experience key fresh
      (bind experience key fresh registry) fresh
      (bind-own experience key fresh registry)

  reserve-preserves-other-experience : ∀ experience other key fresh registry →
    other ≢ experience →
    reserve experience key fresh registry other ≡ registry other
  reserve-preserves-other-experience experience other key fresh registry neq
    with registry experience key
  ... | just existing = refl
  ... | nothing = Ownership.write-other Slots experience other
    (write key (just fresh) (registry experience)) registry neq

  reserve-preserves-other-key : ∀ experience key other fresh registry → other ≢ key →
    reserve experience key fresh registry experience other ≡ registry experience other
  reserve-preserves-other-key experience key other fresh registry neq
    with registry experience key
  ... | just existing = refl
  ... | nothing = trans
    (cong (λ slots → slots other)
      (Ownership.write-own Slots experience (write key (just fresh) (registry experience)) registry))
    (write-other key other (just fresh) (registry experience) neq)

-- Separate immutable identity from the current source/review pointers.
module Revision (Payload : Set) (same : DecidableEquality Payload) where
  record Cell : Set where
    constructor cell
    field
      project current review acknowledged : ℕ
      contribution : Maybe Payload
  open Cell

  commit : Cell → Payload → Cell
  commit s payload = cell (project s) (current s) (suc (review s))
    (current s) (just payload)

  correct : Cell → Cell
  correct s = cell (project s) (suc (current s)) (review s) (current s) nothing

  active : Cell → Maybe Payload
  active s with acknowledged s ≟ current s
  ... | yes _ = contribution s
  ... | no _ = nothing

  replay : Cell → ℕ → Payload → Bool
  replay s expected payload with contribution s
  ... | nothing = false
  ... | just old with same payload old | acknowledged s ≟ current s
  ...   | no _ | _ = false
  ...   | yes _ | no _ = false
  ...   | yes _ | yes _ with suc expected ≟ review s
  ...     | yes _ = true
  ...     | no _ with expected ≟ review s
  ...       | yes _ = true
  ...       | no _ = false

  submit : Cell → ℕ → ℕ → ℕ → Payload → Bool → Maybe Cell
  submit s owner source expected payload validTargets
    with owner ≟ project s | source ≟ current s
  ... | no _ | _ = nothing
  ... | yes _ | no _ = nothing
  ... | yes _ | yes _ with replay s expected payload
  ...   | true = just s
  ...   | false with expected ≟ review s | validTargets
  ...     | yes _ | true = just (commit s payload)
  ...     | yes _ | false = nothing
  ...     | no _ | _ = nothing

  stale-source-refused : ∀ s owner source expected payload valid → source ≢ current s →
    submit s owner source expected payload valid ≡ nothing
  stale-source-refused s owner source expected payload valid neq
    with owner ≟ project s | source ≟ current s
  ... | no _ | _ = refl
  ... | yes _ | no _ = refl
  ... | yes _ | yes eq = ⊥-elim (neq eq)

  foreign-project-refused : ∀ s owner source expected payload valid → owner ≢ project s →
    submit s owner source expected payload valid ≡ nothing
  foreign-project-refused s owner source expected payload valid neq
    with owner ≟ project s | source ≟ current s
  ... | no _ | _ = refl
  ... | yes eq | _ = ⊥-elim (neq eq)

  -- The commit returns acknowledgement and contribution together.
  commit-acknowledges-current : ∀ s payload → acknowledged (commit s payload) ≡ current s
  commit-acknowledges-current s payload = refl

  commit-preserves-project : ∀ s payload → project (commit s payload) ≡ project s
  commit-preserves-project s payload = refl

  correction-retracts : ∀ s → contribution (correct s) ≡ nothing
  correction-retracts s = refl

  correction-is-pending : ∀ s → acknowledged (correct s) ≢ current (correct s)
  correction-is-pending s = not-successor (current s)

  stale-contribution-inactive : ∀ s → acknowledged s ≢ current s → active s ≡ nothing
  stale-contribution-inactive s neq with acknowledged s ≟ current s
  ... | yes eq = ⊥-elim (neq eq)
  ... | no _ = refl

  replay-after-commit : ∀ s payload → replay (commit s payload) (review s) payload ≡ true
  replay-after-commit s payload with same payload payload | current s ≟ current s
  ... | no neq | _ = ⊥-elim (neq refl)
  ... | yes _ | no neq = ⊥-elim (neq refl)
  ... | yes _ | yes _ with suc (review s) ≟ suc (review s)
  ...   | yes _ = refl
  ...   | no neq = ⊥-elim (neq refl)

  exact-retry-no-new-commit : ∀ s payload valid →
    submit (commit s payload) (project s) (current s) (review s) payload valid ≡
    just (commit s payload)
  exact-retry-no-new-commit s payload valid
    with project s ≟ project s | current s ≟ current s
  ... | no neq | _ = ⊥-elim (neq refl)
  ... | yes _ | no neq = ⊥-elim (neq refl)
  ... | yes _ | yes _ rewrite replay-after-commit s payload = refl

  stale-review-refused : ∀ s owner source expected payload valid →
    replay s expected payload ≡ false → expected ≢ review s →
    submit s owner source expected payload valid ≡ nothing
  stale-review-refused s owner source expected payload valid noReplay neq
    with owner ≟ project s | source ≟ current s
  ... | no _ | _ = refl
  ... | yes _ | no _ = refl
  ... | yes _ | yes _ rewrite noReplay with expected ≟ review s | valid
  ...   | yes eq | _ = ⊥-elim (neq eq)
  ...   | no _ | _ = refl

  invalid-targets-refused : ∀ s owner source expected payload →
    replay s expected payload ≡ false →
    submit s owner source expected payload false ≡ nothing
  invalid-targets-refused s owner source expected payload noReplay
    with owner ≟ project s | source ≟ current s
  ... | no _ | _ = refl
  ... | yes _ | no _ = refl
  ... | yes _ | yes _ rewrite noReplay with expected ≟ review s
  ...   | yes _ = refl
  ...   | no _ = refl

  committed-contribution-active : ∀ s payload → active (commit s payload) ≡ just payload
  committed-contribution-active s payload with current s ≟ current s
  ... | yes _ = refl
  ... | no neq = ⊥-elim (neq refl)

-- Independent manual data is never owned by a review.
module ManualFrame (Manual Evidence : Set) where
  record State : Set where
    constructor frame
    field
      manual : Manual
      owned : ℕ → Evidence
  change : ℕ → Evidence → State → State
  change id value s = frame (State.manual s)
    (Ownership.write Evidence id value (State.owned s))
  manual-preserved : ∀ id value s → State.manual (change id value s) ≡ State.manual s
  manual-preserved id value s = refl

module Outcomes where
  open import Data.Product using (_×_; _,_)
  data Outcome : Set where success failure unknown : Outcome
  data Source : Set where toolResult userFeedback agentReport : Source

  -- These are caller-reported provenance classes, not authenticated evidence.
  counts : Source → Outcome → ℕ × ℕ
  counts agentReport _ = 0 , 0
  counts toolResult success = 1 , 0
  counts toolResult failure = 0 , 1
  counts toolResult unknown = 0 , 0
  counts userFeedback success = 1 , 0
  counts userFeedback failure = 0 , 1
  counts userFeedback unknown = 0 , 0

  unknown-is-not-success-or-failure : ∀ source → counts source unknown ≡ (0 , 0)
  unknown-is-not-success-or-failure toolResult = refl
  unknown-is-not-success-or-failure userFeedback = refl
  unknown-is-not-success-or-failure agentReport = refl

  assertion-is-not-observation : ∀ outcome → counts agentReport outcome ≡ (0 , 0)
  assertion-is-not-observation outcome = refl
