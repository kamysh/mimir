{-# OPTIONS --safe #-}
-- Lossless JSON surface grammar. Object members retain order and duplicates;
-- normalization for Value maps and direct record decoding happens afterwards.
module Mimir.JsonSurface where

open import Data.Fin using (#_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Relation.Unary.All using (All)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; suc; _⊔_; _≤_; _<_; _<?_; s≤s; z≤n)
open import Relation.Nullary using (Dec)
open import Mimir.Bits using (Byte)
import Mimir.JsonWhitespace as White
import Mimir.JsonNumber as Number
import Mimir.JsonNumberWire as NumberWire
import Mimir.JsonString as String

record Gap : Set where
  constructor gap
  field bytes : List Byte; spaces : All White.Space bytes

-- A comma always has another element after it. Empty containers have no
-- separated sequence, so trailing commas cannot enter this grammar.
data Separated (A : Set) : Set where
  last : A → Gap → Separated A
  more : A → Gap → Gap → Separated A → Separated A

mutual
  data Value : Set where
    null true false : Value
    number : Number.Syntax → Value
    string : String.StringValue → Value
    array : Gap → Maybe (Separated Value) → Value
    object : Gap → Maybe (Separated Member) → Value

  data Member : Set where
    member : String.StringValue → Gap → Gap → Value → Member

mutual
  spell : Value → List Byte
  spell null = (# 110) ∷ (# 117) ∷ (# 108) ∷ (# 108) ∷ []
  spell true = (# 116) ∷ (# 114) ∷ (# 117) ∷ (# 101) ∷ []
  spell false = (# 102) ∷ (# 97) ∷ (# 108) ∷ (# 115) ∷ (# 101) ∷ []
  spell (number form) = NumberWire.spell form
  spell (string value) = String.spellString (String.StringValue.body value)
  spell (array before values) = (# 91) ∷ (Gap.bytes before ++ arrayBody values)
  spell (object before members) = (# 123) ∷ (Gap.bytes before ++ objectBody members)

  arrayBody : Maybe (Separated Value) → List Byte
  arrayBody nothing = (# 93) ∷ []
  arrayBody (just (last value after)) = spell value ++ (Gap.bytes after ++ ((# 93) ∷ []))
  arrayBody (just (more value after before rest)) =
    spell value ++ (Gap.bytes after ++ ((# 44) ∷ (Gap.bytes before ++ arrayBody (just rest))))

  objectBody : Maybe (Separated Member) → List Byte
  objectBody nothing = (# 125) ∷ []
  objectBody (just (last value after)) = spellMember value ++ (Gap.bytes after ++ ((# 125) ∷ []))
  objectBody (just (more value after before rest)) =
    spellMember value ++ (Gap.bytes after ++ ((# 44) ∷ (Gap.bytes before ++ objectBody (just rest))))

  spellMember : Member → List Byte
  spellMember (member key before after value) = String.spellString (String.StringValue.body key) ++
    (Gap.bytes before ++ ((# 58) ∷ (Gap.bytes after ++ spell value)))

mutual
  depth : Value → ℕ
  depth null = 0
  depth true = 0
  depth false = 0
  depth (number form) = 0
  depth (string value) = 0
  depth (array before values) = suc (arrayDepth values)
  depth (object before members) = suc (objectDepth members)

  arrayDepth : Maybe (Separated Value) → ℕ
  arrayDepth nothing = 0
  arrayDepth (just (last value after)) = depth value
  arrayDepth (just (more value after before rest)) = depth value ⊔ arrayDepth (just rest)

  objectDepth : Maybe (Separated Member) → ℕ
  objectDepth nothing = 0
  objectDepth (just (last value after)) = memberDepth value
  objectDepth (just (more value after before rest)) = memberDepth value ⊔ objectDepth (just rest)

  memberDepth : Member → ℕ
  memberDepth (member key before after value) = depth value

-- serde_json starts at 128, decrements on container entry, and refuses entry
-- when the result is zero. Scalar values consume no nesting budget.
Admitted : ℕ → Value → Set
Admitted budget value = depth value < budget

admitted? : ∀ budget value → Dec (Admitted budget value)
admitted? budget value = depth value <? budget

ProductionAdmitted : Value → Set
ProductionAdmitted = Admitted 128

spellPositive : ∀ value → 1 ≤ length (spell value)
spellPositive null = s≤s z≤n
spellPositive true = s≤s z≤n
spellPositive false = s≤s z≤n
spellPositive (number form) = NumberWire.spellPositive form
spellPositive (string value) = s≤s z≤n
spellPositive (array before values) = s≤s z≤n
spellPositive (object before members) = s≤s z≤n

record Document : Set where
  constructor document
  field before : Gap; value : Value; after : Gap

spellDocument : Document → List Byte
spellDocument (document before value after) = Gap.bytes before ++ (spell value ++ Gap.bytes after)
