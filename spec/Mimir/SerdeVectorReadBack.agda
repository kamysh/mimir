{-# OPTIONS --safe #-}
-- Successful vector-element reads compose in source order.
import Mimir.FloatConversion
module Mimir.SerdeVectorReadBack (floatConversion : Mimir.FloatConversion.Contract) where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (#_; _≟_)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _++_; reverse)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_,_; _×_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; trans; sym)
import Data.List.Properties as Lists
open import Mimir.Bits using (Byte)
import Mimir.SignedMachine as Machine
import Mimir.Validation as V
import Mimir.SerdeVector as VectorDependency
private
  module Vector = VectorDependency floatConversion
import Mimir.SerdeFlow as Flow
import Mimir.SerdeLoop as Loop
import Mimir.SerdeLoopReadBack as LoopBackDependency
private
  module LoopBack = LoopBackDependency floatConversion
import Mimir.SerdeReadBack as Back
import Mimir.SerdeReadBackComposition as ComposeDependency
private
  module Compose = ComposeDependency floatConversion
import Mimir.JsonControls as Controls
import Mimir.JsonWhitespace as White

firstControl : ∀ byte rest → White.Stopped (byte ∷ rest) → byte ≢ (# 93) →
  Controls.arrayNext true (byte ∷ rest) ≡ Controls.C.done true (byte ∷ rest)
firstControl byte rest stopped notClose with White.space? byte
... | yes space = ⊥-elim (stopped space)
... | no notSpace with byte ≟ (# 93)
...   | yes closed = ⊥-elim (notClose closed)
...   | no notClosed = refl

laterControl : ∀ byte rest → White.Stopped (byte ∷ rest) → byte ≢ (# 93) →
  Controls.arrayNext false ((# 44) ∷ byte ∷ rest) ≡
    Controls.C.success true ((# 44) ∷ []) (byte ∷ rest) refl
laterControl byte rest stopped notClose with White.space? byte
... | yes space = ⊥-elim (stopped space)
... | no notSpace with byte ≟ (# 93)
...   | yes closed = ⊥-elim (notClose closed)
...   | no notClosed = refl

module Body (Value : Set) (child : Flow.Parser Value) where
  private
    module B = Vector.Body Value child
    module Steps = LoopBack.Machine B.State (List Value) B.transition

  closed : ∀ first values suffix →
    Back.Returned (B.Run.read (first , values) ((# 93) ∷ suffix))
      (reverse values) ((# 93) ∷ suffix)
  closed first values suffix = Steps.finish (first , values) (# 93 ∷ suffix) (reverse values)
    (# 93 ∷ suffix)
    (Back.returned (Flow.F.initial (# 93 ∷ suffix)) refl refl)

  advance : ∀ first values input consumed middle exact value suffix →
    Controls.arrayNext first input ≡ Controls.C.success true consumed middle exact →
    Back.Returns child middle value suffix →
    Back.Returned (Loop.Step.result (B.transition (first , values) input))
      (inj₁ (false , value ∷ values)) suffix
  advance first values input consumed middle exact value suffix selected receipt
    rewrite selected with child middle | receipt
  ... | Flow.productive result progress | evidence = Compose.map (λ value → inj₁ (false , value ∷ values))
    (Compose.prefix (Flow.F.cursor consumed middle exact) evidence)

  next : ∀ first values input consumed middle exact value after result suffix →
    Controls.arrayNext first input ≡ Controls.C.success true consumed middle exact →
    Back.Returns child middle value after →
    Back.Returned (B.Run.read (false , value ∷ values) after) result suffix →
    Back.Returned (B.Run.read (first , values) input) result suffix
  next first values input consumed middle exact value after result suffix selected head tail = Steps.next (first , values) input (false , value ∷ values) after
    result suffix
    (advance first values input consumed middle exact value after
     selected head)
    tail

record Leading (input : List Byte) : Set where
  constructor leading
  field
    byte : Byte
    rest : List Byte
    exact : input ≡ byte ∷ rest
    stopped : White.Stopped (byte ∷ rest)
    notClose : byte ≢ (# 93)

data Delimited : List Byte → Set where
  comma : ∀ suffix → Delimited ((# 44) ∷ suffix)
  close : ∀ suffix → Delimited ((# 93) ∷ suffix)

module Serialized (Value : Set) (child : Flow.Parser Value)
  (encode : Value → List Byte) (starts : ∀ value → Leading (encode value)) where
  private module B = Vector.Body Value child
  private module Proof = Body Value child

  entries : Bool → List Value → List Byte → List Byte
  entries first [] suffix = (# 93) ∷ suffix
  entries true (value ∷ values) suffix = encode value ++ entries false values suffix
  entries false (value ∷ values) suffix = (# 44) ∷ (encode value ++ entries false values suffix)

  firstEncoded : ∀ value suffix →
    Controls.arrayNext true (encode value ++ suffix) ≡
      Controls.C.success true [] (encode value ++ suffix) refl
  firstEncoded value suffix with starts value
  ... | leading byte rest exact stopped notClose rewrite exact = firstControl byte (rest ++ suffix) stopped notClose

  laterEncoded : ∀ value suffix →
    Controls.arrayNext false ((# 44) ∷ (encode value ++ suffix)) ≡
      Controls.C.success true ((# 44) ∷ []) (encode value ++ suffix) refl
  laterEncoded value suffix with starts value
  ... | leading byte rest exact stopped notClose rewrite exact = laterControl byte (rest ++ suffix) stopped notClose

  delimited : ∀ values suffix → Delimited (entries false values suffix)
  delimited [] suffix = close suffix
  delimited (value ∷ values) suffix = comma (encode value ++ entries false values suffix)

  order : ∀ (value : Value) accumulated values →
    (reverse (value ∷ accumulated) ++ values) ≡ (reverse accumulated ++ (value ∷ values))
  order value accumulated values = trans
    (cong (λ prefix → prefix ++ values)
     (Lists.unfold-reverse value accumulated))
    (Lists.++-assoc (reverse accumulated) (value ∷ []) values)

  module Complete
    (readElement : ∀ value suffix → Delimited suffix →
      Back.Returns child (encode value ++ suffix) value suffix) where

    roundTrip : ∀ first accumulated values suffix →
      Back.Returned (B.Run.read (first , accumulated) (entries first values suffix))
        (reverse accumulated ++ values) ((# 93) ∷ suffix)
    roundTrip first accumulated [] suffix = Back.retarget (Proof.closed first accumulated suffix)
      (sym (Lists.++-identityʳ (reverse accumulated))) refl
    roundTrip true accumulated (value ∷ values) suffix = Proof.next true accumulated
      (encode value ++ entries false values suffix) []
      (encode value ++ entries false values suffix) refl value
      (entries false values suffix)
      (reverse accumulated ++ value ∷ values) (# 93 ∷ suffix)
      (firstEncoded value (entries false values suffix))
      (readElement value (entries false values suffix)
       (delimited values suffix))
      (Back.retarget
       (roundTrip false (value ∷ accumulated) values suffix)
       (order value accumulated values) refl)
    roundTrip false accumulated (value ∷ values) suffix = Proof.next false accumulated
      (# 44 ∷ encode value ++ entries false values suffix) (# 44 ∷ [])
      (encode value ++ entries false values suffix) refl value
      (entries false values suffix)
      (reverse accumulated ++ value ∷ values) (# 93 ∷ suffix)
      (laterEncoded value (entries false values suffix))
      (readElement value (entries false values suffix)
       (delimited values suffix))
      (Back.retarget
       (roundTrip false (value ∷ accumulated) values suffix)
       (order value accumulated values) refl)

module Parser (checks : Machine.OverflowChecks) (Value : Set)
  (child : ℕ → Flow.Parser Value) (expected : V.Fault) where
  private module P = Vector.Parser checks Value child expected

  closeContainer : ∀ allowance rest values suffix →
    Back.Returned (P.body allowance rest) values ((# 93) ∷ suffix) →
    Back.Returns (P.read (suc allowance)) ((# 91) ∷ rest) values suffix
  closeContainer allowance rest values suffix receipt = Compose.noWhitespace (P.dispatch (suc allowance)) (# 91) rest
    (λ ())
    (Compose.container (# 91) rest Controls.arrayEnd receipt
     (# 93 ∷ []) suffix refl refl)

  module Encoded (allowance : ℕ) (encode : Value → List Byte)
    (starts : ∀ value → Leading (encode value))
    (readElement : ∀ value suffix → Delimited suffix →
      Back.Returns (child allowance) (encode value ++ suffix) value suffix) where
    private
      module S = Serialized Value (child allowance) encode starts
      module C = S.Complete readElement

    roundTrip : ∀ values suffix →
      Back.Returns (P.read (suc allowance)) ((# 91) ∷ S.entries true values suffix) values suffix
    roundTrip values suffix = closeContainer allowance (S.entries true values suffix) values
      suffix (C.roundTrip true [] values suffix)
