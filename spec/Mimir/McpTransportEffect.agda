{-# OPTIONS --safe #-}
-- Transport effects and their replies do not depend on numeric conversion.
module Mimir.McpTransportEffect where

open import Data.List using (List)
open import Data.Sum using (_⊎_)
open import Mimir.Bits using (Byte)
open import Mimir.Text using (Text)
open import Mimir.Validation using (Fault)
import Mimir.StructuredValue as V
import Mimir.McpClientLine as Line
import Mimir.McpSendBytes as Send

data Effect : Set where
  serialize : Text → Text → V.Value → Effect
  sending : Send.Effect → Effect
  receiving : Line.Effect → Effect

Reply : Effect → Set
Reply (serialize identity method params) = Fault ⊎ List Byte
Reply (sending operation) = Send.Reply operation
Reply (receiving operation) = Line.Reply operation
