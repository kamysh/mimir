{-# OPTIONS --safe #-}
-- The CLI owns one cancellable future spanning run/watch, including startup,
-- active model/tool work and the interval sleep. Signal listeners are installed
-- before polling that future. Dropping it invokes the owned model/MCP destructors
-- specified in JudgeProcess.cancelOwned and JudgeMcpLifecycle.dropClient.
module Mimir.JudgeSignal where
open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)
import Mimir.Effects as Effects

data Signal : Set where interrupt terminate : Signal
data Race : Set where completed : ℕ → Race; stopped : Signal → Race
module For (Work : Set) where
  data Effect : Set where
    installListeners : Effect
    awaitRace dropWork : Work → Effect
  Reply : Effect → Set
  Reply installListeners = Text ⊎ ⊤
  Reply (awaitRace work) = Race
  Reply (dropWork work) = ⊤
  open Effects.Protocol Effect Reply public

  afterRace : Work → Race → Script ℕ
  afterRace work (completed code) = done code
  afterRace work (stopped signal) = ask (dropWork work) (λ _ → done 0)

  afterInstall : Work → Reply installListeners → Script ℕ
  afterInstall work (inj₁ problem) = done 5
  afterInstall work (inj₂ tt) = ask (awaitRace work) (afterRace work)

  run : Work → Script ℕ
  run work = ask installListeners (afterInstall work)

  signalDropsActiveWork : ∀ work signal events code →
    Runs (afterRace work (stopped signal)) events code →
    events ≡ (dropWork work , tt) ∷ [] × code ≡ 0
  signalDropsActiveWork work signal ._ .0 (replied _ _ tt (returned .0)) = refl , refl

  normalExitPreserved : ∀ work code → afterRace work (completed code) ≡ done code
  normalExitPreserved work code = refl

  listenerFailureStartsNoWork : ∀ work problem events code →
    Runs (afterInstall work (inj₁ problem)) events code → events ≡ [] × code ≡ 5
  listenerFailureStartsNoWork work problem .[] .5 (returned .5) = refl , refl
