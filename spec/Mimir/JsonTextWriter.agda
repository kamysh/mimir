{-# OPTIONS --safe #-}
-- Exact text preservation when the canonical scalar JSON writer is used by
-- Char-based record fields. Character conversion is the checked scalar bridge.
module Mimir.JsonTextWriter where

import Data.Char as Char
import Data.Char.Properties as Char
open import Data.List using (List; []; _∷_)
open import Data.List.Properties using (∷-injectiveˡ; ∷-injectiveʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong₂)
import Mimir.Text as Text
import Mimir.UnicodeText as Unicode
import Mimir.UTF8Packet as Packet
import Mimir.ScalarCharacter as Character
import Mimir.DecodedText as Decoded
import Mimir.JsonString as String
import Mimir.JsonStringWriter as Writer

samePoints : ∀ first second → Writer.codes first ≡ Writer.codes second → Decoded.text first ≡ Decoded.text second
samePoints [] [] same = refl
samePoints [] (_ ∷ _) ()
samePoints (_ ∷ _) [] ()
samePoints (first ∷ rest) (second ∷ tail) same = cong₂ _∷_
  (Char.toℕ-injective (Character.character first) (Character.character second)
    (trans (Character.exact first) (trans (∷-injectiveˡ same) (sym (Character.exact second)))))
  (samePoints rest tail (∷-injectiveʳ same))

render : ∀ text → Unicode.Valid text → String.StringValue
render text valid = Writer.render (Unicode.encodeValues valid)

preservesText : ∀ text valid → Decoded.text (String.values (render text valid)) ≡ text
preservesText text valid = trans (samePoints (String.values (render text valid)) (Unicode.encodeValues valid)
  (Writer.renderMeaning (Unicode.encodeValues valid))) (Decoded.roundTrip valid)
