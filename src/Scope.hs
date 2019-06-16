{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
module Scope where

import Protolude

import Data.HashMap.Lazy (HashMap)
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet

import Name (Name)
import qualified Name

data Key
  = Type
  | Definition
  deriving (Eq, Ord, Show, Generic, Hashable)

data KeyedName = KeyedName !Key !Name.Qualified
  deriving (Eq, Ord, Show, Generic, Hashable)

data Entry
  = Name !Name.Qualified
  | Ambiguous (HashSet Name.Qualified)
  deriving (Show, Generic, Hashable)

type Scope =
  HashMap Name.Pre Entry

type Visibility =
  HashMap Name.Qualified Key

type Module =
  HashMap (Name, Key) (Scope, Visibility)

instance Semigroup Entry where
  Name name1 <> Name name2
    | name1 == name2 =
      Name name1

    | otherwise =
      Ambiguous $ HashSet.fromList [name1, name2]

  Ambiguous names <> Name name =
    Ambiguous (names <> HashSet.singleton name)

  Name name <> Ambiguous names =
    Ambiguous (HashSet.singleton name <> names)

  Ambiguous names1 <> Ambiguous names2 =
    Ambiguous (names1 <> names2)
