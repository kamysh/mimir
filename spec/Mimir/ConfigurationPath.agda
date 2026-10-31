{-# OPTIONS --safe #-}
-- Native paths preserve OS bytes. UTF-8 environment lookup failures are already
-- represented by nothing for XDG_CONFIG_HOME/HOME, as in std::env::var().
-- MIMIR_CONFIG uses var_os, so non-UTF-8 and empty explicit paths are retained.
module Mimir.ConfigurationPath where

open import Data.Fin using (Fin)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.String using (toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Mimir.Text using (Text)

NativePath = List (Fin 256)

data Path : Set where
  native : NativePath → Path
  utf8 : Text → Path
  join : Path → Text → Path

emptyText : Text
emptyText = Data.List.[]

homeBase : Maybe Text → Path
homeBase nothing = join (utf8 emptyText) (toList ".config")
homeBase (just home) = join (utf8 home) (toList ".config")

defaultPath : Maybe Text → Maybe Text → Path
defaultPath (just xdg) home = join (join (utf8 xdg) (toList "mimir")) (toList "config.toml")
defaultPath nothing home = join (join (homeBase home) (toList "mimir")) (toList "config.toml")

select : Maybe NativePath → Maybe Text → Maybe Text → Path
select (just configured) xdg home = native configured
select nothing xdg home = defaultPath xdg home

configuredPathPreserved : ∀ configured xdg home → select (just configured) xdg home ≡ native configured
configuredPathPreserved configured xdg home = refl

xdgPrecedence : ∀ xdg home → select nothing (just xdg) home ≡
  join (join (utf8 xdg) (toList "mimir")) (toList "config.toml")
xdgPrecedence xdg home = refl

homeFallback : ∀ home → select nothing nothing (just home) ≡
  join (join (join (utf8 home) (toList ".config")) (toList "mimir")) (toList "config.toml")
homeFallback home = refl
