{-# OPTIONS --safe #-}
-- Connect compact JSON array spelling to the raw vector-reader composition.
import Mimir.FloatConversion
module Mimir.JsonArrayReadBack (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Bool using (true; false)
open import Data.Fin using (#_)
open import Data.List using (List; []; _∷_; _++_; map)
import Data.List.Properties as Lists
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Mimir.Bits using (Byte)
import Mimir.StructuredValue as JSON
import Mimir.JsonCompactRecords as Compact
import Mimir.JsonRecordSupport as Support
import Mimir.JsonSurface as Surface
import Mimir.SerdeFlow as Flow
import Mimir.SerdeVectorReadBack as VectorDependency
private
  module Vector = VectorDependency floatConversion

module Encoding (Value : Set) (child : Flow.Parser Value)
  (encode : Value → JSON.Value) (supported : ∀ value → Compact.Supported (encode value))
  (starts : ∀ value → Vector.Leading (Compact.bytes (encode value) (supported value))) where
  private
    bytes : Value → List Byte
    bytes value = Compact.bytes (encode value) (supported value)
    module S = Vector.Serialized Value child bytes starts

  bodySpelling : ∀ value values suffix →
    (Surface.arrayBody (just (Compact.arrayEntries (encode value) (map encode values)
      (supported value) (Support.arrayUniform encode supported values))) ++ suffix) ≡
    (bytes value ++ S.entries false values suffix)
  bodySpelling value [] suffix = Lists.++-assoc (bytes value) (# 93 ∷ []) suffix
  bodySpelling value (next ∷ values) suffix = trans
    (Lists.++-assoc (bytes value)
     (# 44 ∷
      Surface.arrayBody
      (just
       (Compact.arrayEntries (encode next) (map encode values)
        (supported next) (Support.arrayUniform encode supported values))))
     suffix)
    (cong (λ rest → bytes value ++ # 44 ∷ rest)
     (bodySpelling next values suffix))

  spelling : ∀ values suffix →
    (Compact.bytes (JSON.array (map encode values))
      (Compact.array (Support.arrayUniform encode supported values)) ++ suffix) ≡
    ((# 91) ∷ S.entries true values suffix)
  spelling [] suffix = refl
  spelling (value ∷ values) suffix = cong (# 91 ∷_) (bodySpelling value values suffix)
