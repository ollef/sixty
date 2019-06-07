{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
module Scope where

import Protolude

import Data.HashMap.Lazy (HashMap)

import Name (Name)
import qualified Name

data Key
  = Type
  | Definition
  deriving (Eq, Ord, Show, Generic, Hashable)

data KeyedName = KeyedName !Key !Name.Qualified
  deriving (Eq, Ord, Show, Generic, Hashable)

type Visibility = Key

type Scope =
  HashMap Name Visibility

type Scopes =
  HashMap (Name, Key) Scope
