{-# OPTIONS --safe #-}
-- Whitespace, container entry and closing cleanup preserve value invariants.
import Mimir.FloatConversion
module Mimir.SerdeParserInvariant (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.List using ([]; _∷_)
open import Data.Sum using (inj₁)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Mimir.SerdeFlow as Flow
import Mimir.SerdeSuccess as S
import Mimir.SerdeScalar as ScalarDependency
private
  module Scalar = ScalarDependency floatConversion
import Mimir.SerdeContainer as Container
import Mimir.JsonWhitespace as White
import Mimir.JsonControls as Controls
module F = Flow.F

finalize : ∀ {Value input} (property : Value → Set) (result : Flow.Result Value input) finish →
  S.Ensures property result → S.Ensures property (Flow.finalize result finish)
finalize property (Flow.ordinary (F.success value position)) finish holds
  with finish (F.Cursor.remaining position)
... | Controls.C.success tt consumed remaining exact = holds
... | Controls.C.failure code consumed remaining exact = tt
finalize property (Flow.ordinary (F.failure error)) finish holds = tt
finalize property (Flow.panicked position) finish holds = tt

enter : ∀ {Value} (property : Value → Set) byte rest (result : Flow.Result Value rest) finish →
  S.Ensures property result → S.Ensures property (Flow.Productive.result (Container.enter byte rest result finish))
enter property byte rest result finish holds = S.prefix property (F.cursor (byte ∷ []) rest refl)
  (Flow.finalize result finish) (finalize property result finish holds)

whitespace : ∀ {Value} (property : Value → Set) (next : Flow.Parser Value) →
  (∀ input → S.Ensures property (Flow.Productive.result (next input))) →
  ∀ input → S.Ensures property (Flow.Productive.result (Scalar.whitespace input next))
whitespace property next valid input with White.take input
... | White.run consumed spaces remaining exact stopped =
  S.prefix property (F.cursor consumed remaining exact) (Flow.Productive.result (next remaining)) (valid remaining)

rejectAll : ∀ checks {Value} (property : Value → Set) failure input →
  S.Ensures property (Flow.Productive.result (Scalar.Parser.rejectAll checks failure input))
rejectAll checks property failure input =
  S.validate (λ scalar → inj₁ failure) property (λ scalar value ()) (Scalar.Parser.raw checks failure input)
