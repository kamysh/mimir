{-# OPTIONS --safe #-}
-- GROUNDS writes and their numerical consequences share the learning lock and
-- transaction. Adding the same pair again creates another contribution; explicit
-- removal deletes every matching edge. It does not rewrite immutable reviews.
module Mimir.GroundingPublication where

open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.Float.Base using (Float)
open import Data.List using (List; []; _∷_; _++_; filterᵇ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Mimir.UUIDGroups using (UUID; _≟UUID_)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (does)
open import Mimir.Text using (Text)
import Mimir.ApplicationStore as Store
import Mimir.LearningStore as Learning
import Mimir.ReviewPreparationPublication as Publication
import Mimir.LearningRecompute as Recompute
import Mimir.PosteriorComputation as Posterior
import Mimir.RetrievalRanking as Ranking
import Mimir.GraphNumerics as Numeric
import Mimir.LearningTransaction as Transaction

data Request : Set where
  add : UUID → UUID → Float → Request -- chunk, belief, weight
  remove : UUID → UUID → Request

data Failure : Set where
  storageFailure : Text → Failure
  invalidWeight missingEndpoint invalidNumericInput invalidNumericWrite foreignTarget : Failure

admitted : Request → Bool
admitted (add chunk belief weight) = Numeric.probability weight
admitted (remove chunk belief) = true

unlink : UUID → UUID → Store.World → Store.World
unlink chunk belief before = record before { grounds = filterᵇ
  (λ e → not (does (chunk ≟UUID Store.Ground.chunk e) ∧ does (belief ≟UUID Store.Ground.belief e))) (Store.World.grounds before) }

module Operation (database : ℕ) (calculation : Posterior.Calculation) where
  module T = Transaction.Over Store.World ⊤ Failure database 671942183

  finish : Store.World → Recompute.Result → T.Decision
  finish proposed (Recompute.recomputed nodes warning) = T.replace (Store.setNodes nodes proposed) tt
  finish proposed Recompute.foreignTarget = T.reject foreignTarget
  finish proposed Recompute.invalidNumericInput = T.reject invalidNumericInput
  finish proposed Recompute.invalidNumericWrite = T.reject invalidNumericWrite

  recompute : UUID → Store.World → T.Decision
  recompute belief proposed = finish proposed (Recompute.runGlobal calculation (belief ∷ [])
    (Store.nodes proposed) (Publication.World.edges pub)
    (Recompute.activeReviewsScoped nothing (Learning.identities learn) (Publication.World.ledger pub))
    (Store.groundingMasses proposed))
    where learn = Store.World.learning proposed; pub = Learning.World.publication learn

  plan : Request → Store.World → T.Decision
  plan (remove chunk belief) before = recompute belief (unlink chunk belief before)
  plan (add chunk belief weight) before with Numeric.probability weight
  ... | false = T.reject invalidWeight
  ... | true with Store.chunk chunk (Store.World.chunks before) | Ranking.lookup belief (Store.beliefs before)
  ...   | nothing | _ = T.reject missingEndpoint
  ...   | just _ | nothing = T.reject missingEndpoint
  ...   | just _ | just _ = recompute belief (record before
    { grounds = Store.World.grounds before ++ (Store.ground chunk belief weight ∷ []) })

  module Run (request : Request) where
    module P = T.Plan (plan request)
    module Laws = T.Laws (plan request)

    -- Nothing is pre-transaction numeric rejection. It cannot acquire a lock,
    -- create an edge or trigger recomputation.
    start : Maybe (T.E.Script T.Outcome)
    start with admitted request
    ... | false = nothing
    ... | true = just P.start

    lockBeforeGrounding : T.Scoped T.outside P.start
    lockBeforeGrounding = Laws.startScoped
