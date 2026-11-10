{-# OPTIONS --safe #-}
-- Pure operation envelopes shared by application output and intended-outcome
-- evaluation. Keeping these downstream avoids changing the core value codec
-- whenever an operation response is factored for the evaluator.
module Mimir.OperationEncoding where

open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.String using (toList)
open import Mimir.Text using (Text)
import Mimir.ApplicationStore as Store
import Mimir.PublicEncoding as Encoding
import Mimir.StructuredValue as V

module Encode (format : Encoding.Formatting) where
  open Encoding using (object; optional)
  open Encoding.Encode format using (uuid; timestamp)

  originalRequest : Store.BindingRow → V.Value
  originalRequest binding = object
    (("operation_token" , uuid (Store.BindingRow.token binding)) ∷
     ("bound_at" , timestamp (Store.BindingRow.boundAt binding)) ∷
     ("request" , object (("operation" , V.string (Store.BindingRow.operation binding)) ∷
       ("arguments" , Store.BindingRow.arguments binding) ∷
       ("settings" , Store.BindingRow.settings binding) ∷ [])) ∷ [])

  savedReply : Store.SavedReplyRow → V.Value
  savedReply row = object (("operation_token" , uuid (Store.SavedReplyRow.token row)) ∷
    ("step" , V.string (Store.SavedReplyRow.step row)) ∷
    ("reply" , Store.SavedReplyRow.reply row) ∷ [])

  nextStep : Text → Maybe Text → Text → V.Value
  nextStep site name identity = object (("site" , V.string site) ∷
    ("key" , optional V.string name) ∷ ("id" , V.string identity) ∷ [])

  completedReadback : ℕ → Store.BindingRow → V.Value → V.Value
  completedReadback token binding value = object
    (("operation_token" , uuid token) ∷ ("status" , V.string (toList "completed")) ∷
     ("original_request" , originalRequest binding) ∷ ("result" , value) ∷ [])
