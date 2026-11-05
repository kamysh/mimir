{-# OPTIONS --safe #-}
-- All 128-bit UUID values. Spelling and formatting belong to the library.
-- This type includes nil/non-v4 values accepted by the stored-data reader.
module Mimir.UUIDGroups where

open import Data.Vec using (Vec)
open import Mimir.Bits using (Byte)

UUID = Vec Byte 16
