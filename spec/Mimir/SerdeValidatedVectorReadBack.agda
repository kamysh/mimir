{-# OPTIONS --safe #-}
-- Array read-back keeps serialization validity and reader bounds as separate evidence.
import Mimir.FloatConversion
module Mimir.SerdeValidatedVectorReadBack (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (#_)
open import Data.List using (List; []; _∷_; _++_; map; reverse)
import Data.List.Properties as Lists
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
open import Mimir.Bits using (Byte)
import Mimir.SerdeFlow as Flow
import Mimir.SerdeVector as RawDependency
private
  module Raw = RawDependency floatConversion
import Mimir.SerdeVectorReadBack as VectorDependency
private
  module Vector = VectorDependency floatConversion
import Mimir.SerdeReadBack as Back
import Mimir.JsonControls as Controls
import Mimir.JsonCompactRecords as Compact
import Mimir.JsonRecordSupport as Support
import Mimir.JsonSurface as Surface
import Mimir.StructuredValue as JSON
import Mimir.SignedMachine as Machine
import Mimir.Validation as V

module Encoding (Value : Set) (validity : Value → Set) (encode : Value → JSON.Value)
  (supported : ∀ value → validity value → Compact.Supported (encode value)) where

  bytes : ∀ value → validity value → List Byte
  bytes value valid = Compact.bytes (encode value) (supported value valid)

  entries : Bool → ∀ values → All validity values → List Byte → List Byte
  entries first [] All.[] suffix = (# 93) ∷ suffix
  entries true (value ∷ values) (valid All.∷ rest) suffix = bytes value valid ++ entries false values rest suffix
  entries false (value ∷ values) (valid All.∷ rest) suffix = (# 44) ∷ (bytes value valid ++ entries false values rest suffix)

  delimited : ∀ values valid suffix → Vector.Delimited (entries false values valid suffix)
  delimited [] All.[] suffix = Vector.close suffix
  delimited (value ∷ values) (valid All.∷ rest) suffix = Vector.comma
    (bytes value valid ++ entries false values rest suffix)

  bodySpelling : ∀ value values valid rest suffix →
    (Surface.arrayBody (just (Compact.arrayEntries (encode value) (map encode values)
      (supported value valid) (Support.array encode supported values rest))) ++ suffix) ≡
    (bytes value valid ++ entries false values rest suffix)
  bodySpelling value [] valid All.[] suffix = Lists.++-assoc (bytes value valid) (# 93 ∷ []) suffix
  bodySpelling value (next ∷ values) valid (nextValid All.∷ rest) suffix = trans
    (Lists.++-assoc (bytes value valid)
     (# 44 ∷
      Surface.arrayBody
      (just
       (Compact.arrayEntries (encode next) (map encode values)
        (supported next nextValid)
        (Support.array encode supported values rest))))
     suffix)
    (cong (λ tail → bytes value valid ++ # 44 ∷ tail)
     (bodySpelling next values nextValid rest suffix))

  spelling : ∀ values valid suffix →
    (Compact.bytes (JSON.array (map encode values))
      (Compact.array (Support.array encode supported values valid)) ++ suffix) ≡
    ((# 91) ∷ entries true values valid suffix)
  spelling [] All.[] suffix = refl
  spelling (value ∷ values) (valid All.∷ rest) suffix = cong (# 91 ∷_) (bodySpelling value values valid rest suffix)

  module Body (child : Flow.Parser Value) (admitted : Value → Set)
    (starts : ∀ value valid → Vector.Leading (bytes value valid))
    (readElement : ∀ value valid → admitted value → ∀ suffix → Vector.Delimited suffix →
      Back.Returns child (bytes value valid ++ suffix) value suffix) where
    private
      module B = Raw.Body Value child
      module Proof = Vector.Body Value child

    firstEncoded : ∀ value valid suffix →
      Controls.arrayNext true (bytes value valid ++ suffix) ≡
        Controls.C.success true [] (bytes value valid ++ suffix) refl
    firstEncoded value valid suffix with starts value valid
    ... | Vector.leading byte rest exact stopped notClose rewrite exact = Vector.firstControl byte (rest ++ suffix) stopped notClose

    laterEncoded : ∀ value valid suffix →
      Controls.arrayNext false ((# 44) ∷ (bytes value valid ++ suffix)) ≡
        Controls.C.success true ((# 44) ∷ []) (bytes value valid ++ suffix) refl
    laterEncoded value valid suffix with starts value valid
    ... | Vector.leading byte rest exact stopped notClose rewrite exact = Vector.laterControl byte (rest ++ suffix) stopped notClose

    order : ∀ (value : Value) accumulated values →
      (reverse (value ∷ accumulated) ++ values) ≡ (reverse accumulated ++ (value ∷ values))
    order value accumulated values = trans
      (cong (λ prefix → prefix ++ values)
       (Lists.unfold-reverse value accumulated))
      (Lists.++-assoc (reverse accumulated) (value ∷ []) values)

    roundTrip : ∀ first accumulated values valid → All admitted values → ∀ suffix →
      Back.Returned (B.Run.read (first , accumulated) (entries first values valid suffix))
        (reverse accumulated ++ values) ((# 93) ∷ suffix)
    roundTrip first accumulated [] All.[] All.[] suffix = Back.retarget (Proof.closed first accumulated suffix)
      (sym (Lists.++-identityʳ (reverse accumulated))) refl
    roundTrip true accumulated (value ∷ values) (valid All.∷ rest) (accepted All.∷ tail) suffix = Proof.next true accumulated
      (bytes value valid ++ entries false values rest suffix) []
      (bytes value valid ++ entries false values rest suffix) refl value
      (entries false values rest suffix)
      (reverse accumulated ++ value ∷ values) (# 93 ∷ suffix)
      (firstEncoded value valid (entries false values rest suffix))
      (readElement value valid accepted
       (entries false values rest suffix) (delimited values rest suffix))
      (Back.retarget
       (roundTrip false (value ∷ accumulated) values rest tail suffix)
       (order value accumulated values) refl)
    roundTrip false accumulated (value ∷ values) (valid All.∷ rest) (accepted All.∷ tail) suffix = Proof.next false accumulated
      (# 44 ∷ bytes value valid ++ entries false values rest suffix)
      (# 44 ∷ []) (bytes value valid ++ entries false values rest suffix)
      refl value (entries false values rest suffix)
      (reverse accumulated ++ value ∷ values) (# 93 ∷ suffix)
      (laterEncoded value valid (entries false values rest suffix))
      (readElement value valid accepted
       (entries false values rest suffix) (delimited values rest suffix))
      (Back.retarget
       (roundTrip false (value ∷ accumulated) values rest tail suffix)
       (order value accumulated values) refl)

  module Parser (checks : Machine.OverflowChecks) (child : ℕ → Flow.Parser Value)
    (expected : V.Fault) (allowance : ℕ) (admitted : Value → Set)
    (starts : ∀ value valid → Vector.Leading (bytes value valid))
    (readElement : ∀ value valid → admitted value → ∀ suffix → Vector.Delimited suffix →
      Back.Returns (child allowance) (bytes value valid ++ suffix) value suffix) where
    private
      module P = Raw.Parser checks Value child expected
      module B = Body (child allowance) admitted starts readElement
      module Close = Vector.Parser checks Value child expected

    roundTrip : ∀ values valid → All admitted values → ∀ suffix →
      Back.Returns (P.read (suc allowance))
        (Compact.bytes (JSON.array (map encode values))
          (Compact.array (Support.array encode supported values valid)) ++ suffix) values suffix
    roundTrip values valid accepted suffix = subst
      (λ input →
         Back.Returns (P.read (suc allowance)) input values suffix)
      (sym (spelling values valid suffix))
      (Close.closeContainer allowance (entries true values valid suffix)
       values suffix (B.roundTrip true [] values valid accepted suffix))
