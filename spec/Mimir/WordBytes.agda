{-# OPTIONS --safe #-}
-- Exact, invertible byte/word conversion. Byte order is explicit and no
-- padding, truncation or target-endianness premise is hidden in conversion.
module Mimir.WordBytes where

open import Data.Vec using (Vec; []; _∷_; map; reverse)
open import Data.Vec.Properties using (reverse-involutive)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans)
open import Mimir.Bits using (Byte; Word; packByte; unpackByte; unpackPack; packUnpack)
open import Mimir.VectorChunks using (size; chunks; flatten; flattenChunks; chunksFlatten)

mapInverse : ∀ {A B : Set} (f : A → B) (g : B → A) → (∀ value → g (f value) ≡ value) →
  ∀ {count} (values : Vec A count) → map g (map f values) ≡ values
mapInverse f g inverse [] = refl
mapInverse f g inverse (value ∷ rest) = cong₂ _∷_ (inverse value) (mapInverse f g inverse rest)

little : ∀ count → Word (size 8 count) → Vec Byte count
little count word = map packByte (chunks 8 count word)

fromLittle : ∀ count → Vec Byte count → Word (size 8 count)
fromLittle count bytes = flatten (map unpackByte bytes)

littleWordRoundTrip : ∀ count word → fromLittle count (little count word) ≡ word
littleWordRoundTrip count word = trans
  (cong flatten (mapInverse packByte unpackByte unpackPack (chunks 8 count word)))
  (flattenChunks 8 count word)

littleBytesRoundTrip : ∀ count bytes → little count (fromLittle count bytes) ≡ bytes
littleBytesRoundTrip count bytes = trans
  (cong (map packByte) (chunksFlatten (map unpackByte bytes)))
  (mapInverse unpackByte packByte (packUnpack 8) bytes)

big : ∀ count → Word (size 8 count) → Vec Byte count
big count word = reverse (little count word)

fromBig : ∀ count → Vec Byte count → Word (size 8 count)
fromBig count bytes = fromLittle count (reverse bytes)

bigWordRoundTrip : ∀ count word → fromBig count (big count word) ≡ word
bigWordRoundTrip count word = trans (cong (fromLittle count) (reverse-involutive (little count word)))
  (littleWordRoundTrip count word)

bigBytesRoundTrip : ∀ count bytes → big count (fromBig count bytes) ≡ bytes
bigBytesRoundTrip count bytes = trans (cong reverse (littleBytesRoundTrip count (reverse bytes))) (reverse-involutive bytes)

words : ∀ byteWidth count → Vec Byte (size byteWidth count) → Vec (Word (size 8 byteWidth)) count
words byteWidth count bytes = map (fromBig byteWidth) (chunks byteWidth count bytes)

bytes : ∀ byteWidth count → Vec (Word (size 8 byteWidth)) count → Vec Byte (size byteWidth count)
bytes byteWidth count input = flatten (map (big byteWidth) input)

wordsRoundTrip : ∀ byteWidth count input → words byteWidth count (bytes byteWidth count input) ≡ input
wordsRoundTrip byteWidth count input = trans
  (cong (map (fromBig byteWidth)) (chunksFlatten (map (big byteWidth) input)))
  (mapInverse (big byteWidth) (fromBig byteWidth) (bigWordRoundTrip byteWidth) input)

bytesRoundTrip : ∀ byteWidth count input → bytes byteWidth count (words byteWidth count input) ≡ input
bytesRoundTrip byteWidth count input = trans
  (cong flatten (mapInverse (fromBig byteWidth) (big byteWidth) (bigBytesRoundTrip byteWidth) (chunks byteWidth count input)))
  (flattenChunks byteWidth count input)
