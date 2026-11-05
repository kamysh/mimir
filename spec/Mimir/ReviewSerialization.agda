{-# OPTIONS --safe #-}
-- Two reviews based on the same revision cannot both append history once the
-- second reads the first publication. Lock participation and that fresh read
-- remain explicit native obligations; atomicity alone does not supply them.
-- ReviewCompetition connects the public review programs to native receipts.
module Mimir.ReviewSerialization where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; _≟_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym)
open import Mimir.SourceReview using (_≟Text_)
import Mimir.LearningContracts as Contracts
import Mimir.ReviewJournal as Journal

module Over (Payload Contribution : Set) (equal : DecidableEquality Payload)
  (materialize : Payload → Contribution) where
  module J = Journal.Over Payload Contribution equal materialize
  module R = J.R
  module P = J.P
  module C = J.C

  data Inert {before payload} : ∀ {after} → P.Plan before payload after → Set where
    refused : Inert P.refused
    replayed : Inert P.replayed

  staleClassification : ∀ before owner source expected payload valid → expected ≢ R.Cell.review before →
    Inert (P.classify before owner source expected payload valid)
  staleClassification before owner source expected payload valid stale
    with owner ≟Text R.Cell.project before | source ≟ R.Cell.current before
  ... | no _ | _ = refused
  ... | yes _ | no _ = refused
  ... | yes _ | yes _ with R.replay before expected payload
  ...   | true = replayed
  ...   | false with expected ≟ R.Cell.review before | valid
  ...     | no _ | _ = refused
  ...     | yes same | false = refused
  ...     | yes same | true = ⊥-elim (stale same)

  inertUnchanged : ∀ identity before payload {after} (classification : P.Plan (J.current before identity) payload after) →
    Inert classification → J.apply identity before payload classification ≡ before
  inertUnchanged identity before payload P.refused refused = refl
  inertUnchanged identity before payload P.replayed replayed = refl

  staleUnchanged : ∀ identity before submitted →
    C.Request.expected submitted ≢ R.Cell.review (J.current before identity) →
    J.proposed identity before submitted ≡ before
  staleUnchanged identity before submitted stale = inertUnchanged identity before (C.Request.payload submitted)
    (J.classify identity before submitted)
    (staleClassification (J.current before identity)
     (C.Request.owner submitted) (C.Request.source submitted)
     (C.Request.expected submitted) (C.Request.payload submitted)
     (C.Request.validTargets submitted) stale)

  freshCurrent : ∀ identity before payload →
    J.current (J.fresh identity before payload) identity ≡ R.commit (J.current before identity) payload
  freshCurrent identity before payload = J.L.installedCell identity
    (R.commit (J.current before identity) payload)
    (J.World.active before)

  secondCannotAppend : ∀ identity before first submitted →
    C.Request.expected submitted ≡ R.Cell.review (J.current before identity) →
    J.proposed identity (J.fresh identity before first) submitted ≡ J.fresh identity before first
  secondCannotAppend identity before first submitted expected = staleUnchanged identity (J.fresh identity before first) submitted
    (λ same →
       Contracts.not-successor (R.Cell.review (J.current before identity))
       (trans (sym expected)
        (trans same
         (cong R.Cell.review (freshCurrent identity before first)))))
