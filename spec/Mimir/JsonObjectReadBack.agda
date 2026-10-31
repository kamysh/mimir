{-# OPTIONS --safe #-}
-- Right-associated compact object bytes for raw member-reader composition.
module Mimir.JsonObjectReadBack where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (#_)
open import Data.List using (List; []; _∷_; _++_)
import Data.List.Properties as Lists
open import Data.List.Relation.Unary.All using (All)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Mimir.Text using (Text)
open import Mimir.Bits using (Byte)
import Mimir.StructuredValue as JSON
import Mimir.JsonCompactRecords as Compact
import Mimir.JsonSurface as Surface
import Mimir.JsonString as String
import Mimir.JsonTextWriter as Writer

member : ∀ entry → Compact.FieldSupported entry → List Byte → List Byte
member (name , value) (nameValid , valid) suffix =
  String.spellString (String.StringValue.body (Writer.render name nameValid)) ++
    ((# 58) ∷ (Compact.bytes value valid ++ suffix))

members : Bool → ∀ fields → All Compact.FieldSupported fields → List Byte → List Byte
members first [] All.[] suffix = (# 125) ∷ suffix
members true (entry ∷ fields) (valid All.∷ rest) suffix = member entry valid (members false fields rest suffix)
members false (entry ∷ fields) (valid All.∷ rest) suffix = (# 44) ∷ member entry valid (members false fields rest suffix)

data Delimited : List Byte → Set where
  comma : ∀ suffix → Delimited ((# 44) ∷ suffix)
  close : ∀ suffix → Delimited ((# 125) ∷ suffix)

delimited : ∀ fields valid suffix → Delimited (members false fields valid suffix)
delimited [] All.[] suffix = close suffix
delimited (entry ∷ fields) (valid All.∷ rest) suffix = comma (member entry valid (members false fields rest suffix))

memberSpelling : ∀ entry valid suffix →
  (Surface.spellMember (Compact.renderField entry valid) ++ suffix) ≡ member entry valid suffix
memberSpelling (name , value) (nameValid , valid) suffix = Lists.++-assoc
  (String.spellString
   (String.StringValue.body (Writer.render name nameValid)))
  (# 58 ∷ Compact.bytes value valid) suffix

bodySpelling : ∀ entry fields valid rest suffix →
  (Surface.objectBody (just (Compact.objectEntries entry fields valid rest)) ++ suffix) ≡
  member entry valid (members false fields rest suffix)
bodySpelling entry [] valid All.[] suffix = trans
  (Lists.++-assoc
   (Surface.spellMember (Compact.renderField entry valid))
   (# 125 ∷ []) suffix)
  (memberSpelling entry valid (# 125 ∷ suffix))
bodySpelling entry (next ∷ fields) valid (nextValid All.∷ rest) suffix = trans
  (Lists.++-assoc
   (Surface.spellMember (Compact.renderField entry valid))
   (# 44 ∷
    Surface.objectBody
    (just (Compact.objectEntries next fields nextValid rest)))
   suffix)
  (trans
   (cong
    (λ tail →
       Surface.spellMember (Compact.renderField entry valid) ++
       # 44 ∷ tail)
    (bodySpelling next fields nextValid rest suffix))
   (memberSpelling entry valid
    (# 44 ∷ member next nextValid (members false fields rest suffix))))

spelling : ∀ fields valid suffix →
  (Compact.bytes (JSON.object fields) (Compact.object valid) ++ suffix) ≡
  ((# 123) ∷ members true fields valid suffix)
spelling [] All.[] suffix = refl
spelling (entry ∷ fields) (valid All.∷ rest) suffix = cong (# 123 ∷_) (bodySpelling entry fields valid rest suffix)
