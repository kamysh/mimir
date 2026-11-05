{-# OPTIONS --safe #-}
-- Judge configuration reuses the core loader; it does not silently accept an
-- invented Core.Config at the coreLoad effect. Native paths preserve bytes.
module Mimir.JudgeConfigurationComposition where

open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.String using (toList)
import Mimir.FloatConversion as Conversion
import Mimir.JudgeConfiguration as Judge
import Mimir.ConfigurationProtocol as Core
import Mimir.ConfigurationPath as Path
import Mimir.UnixMetadata as Metadata

module Compose (conversion : Conversion.Contract) (sizeMaximum : ℕ) (libraries : Judge.Libraries)
  (unix : Bool) (owner : Metadata.UserId) where
  module J = Judge.Load conversion sizeMaximum libraries unix owner
  module C = Core.Run sizeMaximum

  data Receipt : (effect : J.Effect) → J.Reply effect → Set where
    cwd : ∀ reply → Receipt J.cwd reply
    metadata : ∀ path reply → Receipt (J.lstat path) reply
    loaded : ∀ path events config → Core.P.Runs (C.loadFrom (Path.native path)) events (inj₂ config) →
      Receipt (J.coreLoad path) (inj₂ config)
    failed : ∀ path events failure → Core.P.Runs (C.loadFrom (Path.native path)) events (inj₁ failure) →
      Receipt (J.coreLoad path) (inj₁ (toList "unable to load config"))

  data Runs : J.P.Script J.Result → List J.P.Event → J.Result → Set where
    returned : ∀ result → Runs (J.P.done result) [] result
    replied : ∀ effect continuation reply events result → Receipt effect reply → Runs (continuation reply) events result →
      Runs (J.P.ask effect continuation) ((effect , reply) ∷ events) result
