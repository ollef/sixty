{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
module Scope where

import Protolude

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
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
  | Constructors (HashSet Name.QualifiedConstructor)
  | Ambiguous (HashSet Name.QualifiedConstructor) (HashSet Name.Qualified)
  deriving (Show, Generic, Hashable)

entryConstructors :: Entry -> HashSet Name.QualifiedConstructor
entryConstructors entry =
  case entry of
    Name _ ->
      mempty

    Constructors cs ->
      cs

    Ambiguous cs _ ->
      cs

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
      Ambiguous mempty $ HashSet.fromList [name1, name2]

  Constructors constrs1 <> Constructors constrs2 =
    Constructors (constrs1 <> constrs2)

  Name name <> entry =
    Ambiguous mempty (HashSet.singleton name) <> entry

  entry <> Name name =
    entry <> Ambiguous mempty (HashSet.singleton name)

  Constructors constrs <> entry =
    Ambiguous constrs mempty <> entry

  entry <> Constructors constrs =
    entry <> Ambiguous constrs mempty

  Ambiguous constrs1 names1 <> Ambiguous constrs2 names2 =
    Ambiguous (constrs1 <> constrs2) (names1 <> names2)

aliases
  :: Scope
  -> (HashMap Name.QualifiedConstructor (HashSet Name.Pre), HashMap Name.Qualified (HashSet Name.Pre))
aliases scope =
  bimap (HashMap.fromListWith (<>)) (HashMap.fromListWith (<>)) $
    partitionEithers $
    concat
    [ case entry of
        Name name ->
          [Right (name, HashSet.singleton prename)]

        Constructors constrs ->
          [ Left (constr, HashSet.singleton prename)
          | constr <- HashSet.toList constrs
          ]

        Ambiguous constrs names ->
          [ Left (constr, HashSet.singleton prename)
          | constr <- HashSet.toList constrs
          ]
          <>
          [ Right (name, HashSet.singleton prename)
          | name <- HashSet.toList names
          ]
    | (prename, entry) <- HashMap.toList scope
    ]
