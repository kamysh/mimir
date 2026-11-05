{-# OPTIONS --safe #-}
-- AGE column adapters. Standard floating/RFC3339 parsing is a dependency;
-- required-column order, legacy fallbacks and reconstructed fields are Mimir
-- behavior. Both extended and simple query rows use these same adapters.
module Mimir.StoreRows where

open import Data.Bool using (true; false; _∧_)
open import Data.Float.Base using (Float)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (toList)
open import Mimir.Text using (Text)
import Mimir.PublicInput as Input
import Mimir.StructuredValue as JSON
import Mimir.CandidateGraph as Graph
import Mimir.LearningCandidates as Memory
import Mimir.PublicRequest as Request
import Mimir.PosteriorComputation as Beta
import Mimir.GraphNumerics as Numeric
import Mimir.DocumentStore as Document
import Mimir.Unsigned as UInt

Row = Text → Maybe Text

record Libraries : Set where
  field unsigned : UInt.Parser
        float : Text → Maybe Float
        rfc3339UTCNanoseconds : Text → Maybe ℤ
        stringArrayJSON : Text → Maybe (List Text)
        uuid : Text → Maybe ℕ

data Error : Set where
  missing malformed driverPanic : Text → Error
  invalidDerivedProbability invalidPatternProbability : Error

infixl 1 _>>=_
_>>=_ : ∀ {A B : Set} → Error ⊎ A → (A → Error ⊎ B) → Error ⊎ B
inj₁ error >>= next = inj₁ error
inj₂ value >>= next = next value

column : Text → Row → Error ⊎ Text
column name row with row name
... | nothing = inj₁ (missing name)
... | just value = inj₂ value

parse : ∀ {A : Set} → Text → (Text → Maybe A) → Text → Error ⊎ A
parse name decode text with decode text
... | nothing = inj₁ (malformed name)
... | just value = inj₂ value

optional : ∀ {A : Set} → (Text → Maybe A) → Maybe Text → Maybe A
optional decode nothing = nothing
optional decode (just text) = decode text

fallback : ∀ {A : Set} → A → Maybe A → A
fallback default nothing = default
fallback default (just value) = value

memory : Maybe Text → Memory.Memory
memory nothing = Memory.fact
memory (just text) with Request.memory (JSON.string text)
... | inj₁ _ = Memory.fact
... | inj₂ value = value

module Decode (libraries : Libraries) where
  uuid : Text → Maybe ℕ
  uuid = Libraries.uuid libraries

  reconstruct : ℕ → Text → Float → Float → ℤ → ℤ → Row → Error ⊎ Graph.BeliefValues
  reconstruct id content probability confidence created activated row
    with Numeric.probability mean ∧ Numeric.probability certainty
    where
    prior = Beta.prior probability confidence
    a₀ = fallback (Beta.Beta.alpha prior) (optional (Libraries.float libraries) (row (toList "alpha0")))
    b₀ = fallback (Beta.Beta.negative prior) (optional (Libraries.float libraries) (row (toList "beta0")))
    a = fallback a₀ (optional (Libraries.float libraries) (row (toList "alpha")))
    b = fallback b₀ (optional (Libraries.float libraries) (row (toList "beta")))
    mean = Beta.mean (Beta.beta a b)
    certainty = Beta.confidence (Beta.beta a b)
  ... | false = inj₁ invalidDerivedProbability
  ... | true = inj₂ (Graph.beliefValues id content (row (toList "project")) (memory (row (toList "memory_type")))
    created activated mean certainty a b a₀ b₀)
    where
    prior = Beta.prior probability confidence
    a₀ = fallback (Beta.Beta.alpha prior) (optional (Libraries.float libraries) (row (toList "alpha0")))
    b₀ = fallback (Beta.Beta.negative prior) (optional (Libraries.float libraries) (row (toList "beta0")))
    a = fallback a₀ (optional (Libraries.float libraries) (row (toList "alpha")))
    b = fallback b₀ (optional (Libraries.float libraries) (row (toList "beta")))
    mean = Beta.mean (Beta.beta a b)
    certainty = Beta.confidence (Beta.beta a b)

  belief : Row → Error ⊎ Graph.BeliefValues
  belief row = column (toList "id") row >>= λ idText → column (toList "content") row >>= λ content →
    column (toList "probability") row >>= λ probabilityText → column (toList "confidence") row >>= λ confidenceText →
    column (toList "created_at") row >>= λ createdText → column (toList "last_activated_at") row >>= λ activatedText →
    parse (toList "id") uuid idText >>= λ id →
    parse (toList "probability") (Libraries.float libraries) probabilityText >>= λ probability →
    parse (toList "confidence") (Libraries.float libraries) confidenceText >>= λ confidence →
    parse (toList "created_at") (Libraries.rfc3339UTCNanoseconds libraries) createdText >>= λ created →
    parse (toList "last_activated_at") (Libraries.rfc3339UTCNanoseconds libraries) activatedText >>= λ activated →
    reconstruct id content probability confidence created activated row

  unsigned32 : Text → Maybe ℕ
  unsigned32 text with UInt.parse (Libraries.unsigned libraries) 4294967295 text
  ... | inj₁ _ = nothing
  ... | inj₂ value = just (UInt.UInt.number value)

  patternRow : Row → Error ⊎ Graph.PatternValues
  patternRow row = column (toList "id") row >>= λ idText → column (toList "situation") row >>= λ situation →
    column (toList "approach") row >>= λ approach → column (toList "activation_count") row >>= λ countText →
    column (toList "success_rate") row >>= λ rateText → column (toList "created_at") row >>= λ createdText →
    parse (toList "id") uuid idText >>= λ id → parse (toList "activation_count") unsigned32 countText >>= λ count →
    parse (toList "success_rate") (Libraries.float libraries) rateText >>= λ rate →
    parse (toList "created_at") (Libraries.rfc3339UTCNanoseconds libraries) createdText >>= λ created →
    finish id situation approach count rate created
    where
    finish : ℕ → Text → Text → ℕ → Float → ℤ → Error ⊎ Graph.PatternValues
    finish id situation approach count rate created with Numeric.probability rate
    ... | false = inj₁ invalidPatternProbability
    ... | true = inj₂ (Graph.patternValues id situation approach (row (toList "project")) created count rate)

  driverColumn : Text → Row → Error ⊎ Text
  driverColumn name row with row name
  ... | nothing = inj₁ (driverPanic name)
  ... | just value = inj₂ value

  chunk : Row → Error ⊎ Document.Chunk
  chunk row = driverColumn (toList "id") row >>= λ idText →
    driverColumn (toList "document_path") row >>= λ path → driverColumn (toList "section_path") row >>= λ section →
    driverColumn (toList "content") row >>= λ content → parse (toList "id") uuid idText >>= λ id →
    inj₂ (Document.mkChunk id path (fallback [] (Libraries.stringArrayJSON libraries section)) content
      (optional uuid (row (toList "parent_id"))) (row (toList "project")))
