{-# OPTIONS --safe #-}
-- The signal controller's drop acknowledgement requires the concrete owned
-- work cleanup. The race returns the current checkpoint of the same future.
module Mimir.JudgeSignalBinding where

open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.StandardLibrary as Conversion
import Mimir.PublicEncoding as Encoding
import Mimir.JudgeHarnessAdapter as Harness
import Mimir.JudgeOwnedWork as Owned
import Mimir.JudgeSignal as Signal

module Bound (conversion : Conversion.Contract) (format : Encoding.Formatting) (libraries : Harness.Libraries)
  (Completion : Owned.Bound.Work conversion format libraries → ℕ → Set) where
  private module O = Owned.Bound conversion format libraries
  module S = Signal.For O.Work

  Initial : O.Work → Set
  Initial work = O.Work.activity work ≡ O.startup nothing ×
    (O.Resources.ownedClient (O.Work.resources work) ≡ nothing × O.Resources.locks (O.Work.resources work) ≡ [])

  run : (initial : O.Work) → Initial initial → S.Script ℕ
  run initial unpolled = S.run initial

  -- Current checkpoints are native observations. Their component prefixes
  -- retain actual acquisitions and progress. Matching future identity prevents
  -- a different owned job from satisfying this race's cleanup obligation.
  data Receipt : (effect : S.Effect) → S.Reply effect → Set where
    listeners : ∀ reply → Receipt S.installListeners reply
    completed : ∀ initial code → Completion initial code → Receipt (S.awaitRace initial) (Signal.completed code)
    stopped : ∀ initial current signal → O.Work.future initial ≡ O.Work.future current →
      Receipt (S.awaitRace initial) (Signal.stopped signal current)
    dropped : ∀ current events result → O.Runs (O.cleanup current) events result → Receipt (S.dropWork current) tt

  data Runs {Result : Set} : S.Script Result → List S.Event → Result → Set where
    returned : ∀ result → Runs (S.done result) [] result
    replied : ∀ effect continuation reply events result → Receipt effect reply → Runs (continuation reply) events result →
      Runs (S.ask effect continuation) ((effect , reply) ∷ events) result

  record Cleaned (current : O.Work) : Set where
    field events : List O.E.Event
          result : O.Stopped
          executed : O.Runs (O.cleanup current) events result
          reportPreserved : O.Stopped.savedReport result ≡ O.Work.savedReport current
          uncertaintyRetained : O.Stopped.pending result ≡ O.unconfirmed (O.Work.activity current)

  stoppedRequiresConcreteCleanup : ∀ current signal events code →
    Runs (S.afterRace (Signal.stopped signal current)) events code → Cleaned current × code ≡ 0
  stoppedRequiresConcreteCleanup current signal events code
    (replied _ _ tt _ _ (dropped .current cleanupEvents result execution) (returned .0)) =
    record { events = cleanupEvents ; result = result ; executed = execution
           ; reportPreserved = O.cleanupPreservesReport current cleanupEvents result execution
           ; uncertaintyRetained = O.cleanupRetainsUncertainty current cleanupEvents result execution } , refl

  -- The listener acknowledgement and race result are part of the full run;
  -- cleanup belongs to CURRENT, even when INITIAL owned no child or lock.
  fullStopCleansCurrent : ∀ initial unpolled current signal rest code →
    Runs (run initial unpolled)
      ((S.installListeners , inj₂ tt) ∷ (S.awaitRace initial , Signal.stopped signal current) ∷ rest) code →
    O.Work.future initial ≡ O.Work.future current × (Cleaned current × code ≡ 0)
  fullStopCleansCurrent initial unpolled current signal rest code
    (replied _ _ _ _ _ installed (replied _ _ _ _ _ (stopped .initial .current .signal same) execution)) =
    same , stoppedRequiresConcreteCleanup current signal rest code execution
