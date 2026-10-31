{-# OPTIONS --safe #-}
-- File::write_all uses the default Rust loop: partial progress, zero-write
-- failure, unchanged retry on Interrupted, and propagation of other errors.
-- Native successful counts carry the write(2) bound as explicit reply evidence.
-- No fairness or bound on the number of interruptions is postulated.
module Mimir.NativeWriteAll where

open import Data.List using (List; []; _∷_; _++_; length; take; drop; replicate)
open import Data.List.Properties using (++-assoc; ++-identityʳ; take++drop≡id; length-drop)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; +-monoʳ-≤; m∸n≤m)
open import Data.Product using (Σ; _,_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Mimir.Bits using (Byte)

module With (NativeError : Set) where
  data Failure : Set where zeroWrite : Failure; native : NativeError → Failure

  data State : Set where
    writing : List Byte → Byte → List Byte → State
    complete : List Byte → State
    failed : Failure → List Byte → List Byte → State

  data WriteReply (limit : ℕ) : Set where
    wrote : (count : ℕ) → count ≤ limit → WriteReply limit
    interrupted : WriteReply limit
    rejected : NativeError → WriteReply limit

  Reply : State → Set
  Reply (writing sent first pending) = WriteReply (suc (length pending))
  Reply (complete sent) = ⊥
  Reply (failed reason sent pending) = ⊥

  resume : List Byte → List Byte → State
  resume sent [] = complete sent
  resume sent (first ∷ pending) = writing sent first pending

  step : (state : State) → Reply state → State
  step (writing sent first pending) (wrote zero _) = failed zeroWrite sent (first ∷ pending)
  step (writing sent first pending) (wrote (suc count) bound) =
    resume (sent ++ take (suc count) (first ∷ pending)) (drop count pending)
  step (writing sent first pending) interrupted = writing sent first pending
  step (writing sent first pending) (rejected error) = failed (native error) sent (first ∷ pending)
  step (complete sent) ()
  step (failed reason sent pending) ()

  contents : State → List Byte
  contents (writing sent first pending) = sent ++ (first ∷ pending)
  contents (complete sent) = sent
  contents (failed reason sent pending) = sent ++ pending

  resumeContents : ∀ sent pending → contents (resume sent pending) ≡ sent ++ pending
  resumeContents sent [] = sym (++-identityʳ sent)
  resumeContents sent (_ ∷ _) = refl

  conserved : ∀ state reply → contents (step state reply) ≡ contents state
  conserved (writing sent first pending) (wrote zero _) = refl
  conserved (writing sent first pending) (wrote (suc count) bound) =
    trans (resumeContents (sent ++ take (suc count) (first ∷ pending)) (drop count pending))
      (trans (++-assoc sent (take (suc count) (first ∷ pending)) (drop count pending))
        (cong (sent ++_) (take++drop≡id (suc count) (first ∷ pending))))
  conserved (writing sent first pending) interrupted = refl
  conserved (writing sent first pending) (rejected error) = refl
  conserved (complete sent) ()
  conserved (failed reason sent pending) ()

  rank : State → ℕ
  rank (writing sent first pending) = suc (length pending)
  rank (complete sent) = 0
  rank (failed reason sent pending) = 0

  resumeRank : ∀ sent pending → rank (resume sent pending) ≡ length pending
  resumeRank sent [] = refl
  resumeRank sent (_ ∷ _) = refl

  cost : ∀ state → Reply state → ℕ
  cost (writing _ _ _) interrupted = 0
  cost (writing _ _ _) (wrote _ _) = 1
  cost (writing _ _ _) (rejected _) = 1
  cost (complete _) ()
  cost (failed _ _ _) ()

  dropBound : ∀ count (pending : List Byte) → length (drop count pending) ≤ length pending
  dropBound count pending = subst (_≤ length pending) (sym (length-drop count pending)) (m∸n≤m (length pending) count)

  progressBound : ∀ state reply → cost state reply + rank (step state reply) ≤ rank state
  progressBound (writing sent first pending) (wrote zero _) = s≤s z≤n
  progressBound (writing sent first pending) (wrote (suc count) bound)
    rewrite resumeRank (sent ++ take (suc count) (first ∷ pending)) (drop count pending) = s≤s (dropBound count pending)
  progressBound (writing sent first pending) interrupted = ≤-refl
  progressBound (writing sent first pending) (rejected error) = s≤s z≤n
  progressBound (complete sent) ()
  progressBound (failed reason sent pending) ()

  Event = Σ State Reply

  data Trace : State → List Event → State → Set where
    empty : ∀ state → Trace state [] state
    more : ∀ state reply {events final} → Trace (step state reply) events final →
      Trace state ((state , reply) ∷ events) final

  productive : List Event → ℕ
  productive [] = 0
  productive ((state , reply) ∷ events) = cost state reply + productive events

  traceBound : ∀ {before events after} → Trace before events after → productive events ≤ rank before
  traceBound (empty _) = z≤n
  traceBound (more state reply rest) =
    ≤-trans (+-monoʳ-≤ (cost state reply) (traceBound rest)) (progressBound state reply)

  traceConserved : ∀ {before events after} → Trace before events after → contents after ≡ contents before
  traceConserved (empty _) = refl
  traceConserved (more state reply rest) = trans (traceConserved rest) (conserved state reply)

  successfulBytes : ∀ bytes events sent → Trace (resume [] bytes) events (complete sent) → sent ≡ bytes
  successfulBytes bytes events sent run = trans (traceConserved run) (resumeContents [] bytes)

  writeBound : ∀ bytes events result → Trace (resume [] bytes) events result → productive events ≤ length bytes
  writeBound bytes events result run = subst (productive events ≤_) (resumeRank [] bytes) (traceBound run)

  arbitraryInterruptions : ∀ count sent first pending →
    Trace (writing sent first pending)
      (replicate count (writing sent first pending , interrupted)) (writing sent first pending)
  arbitraryInterruptions zero sent first pending = empty _
  arbitraryInterruptions (suc count) sent first pending = more _ interrupted (arbitraryInterruptions count sent first pending)
