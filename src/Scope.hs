{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Scope where

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import qualified Name
import Orphans ()
import Protolude

data DefinitionKind = Type | Definition
  deriving (Eq, Ord, Show, Generic, Hashable)

data Entry
  = Name !Name.Qualified
  | -- | Only data
    Constructors (HashSet Name.QualifiedConstructor) (HashSet Name.Qualified)
  | Ambiguous (HashSet Name.QualifiedConstructor) (HashSet Name.Qualified)
  deriving (Eq, Show, Generic, Hashable)

entryConstructors :: Entry -> HashSet Name.QualifiedConstructor
entryConstructors entry =
  case entry of
    Name _ ->
      mempty
    Constructors cs _ ->
      cs
    Ambiguous cs _ ->
      cs

type Scope =
  HashMap Name.Surface Entry

instance Semigroup Entry where
  Name name1 <> Name name2
    | name1 == name2 =
        Name name1
    | otherwise =
        Ambiguous mempty $ HashSet.fromList [name1, name2]
  Constructors constrs1 data1 <> Constructors constrs2 data2 =
    Constructors (constrs1 <> constrs2) (data1 <> data2)
  entry@(Constructors _ data_) <> Name name
    | name `HashSet.member` data_ =
        entry
  Name name <> entry@(Constructors _ data_)
    | name `HashSet.member` data_ =
        entry
  Name name <> entry =
    Ambiguous mempty (HashSet.singleton name) <> entry
  entry <> Name name =
    entry <> Ambiguous mempty (HashSet.singleton name)
  Constructors constrs data_ <> entry =
    Ambiguous constrs data_ <> entry
  entry <> Constructors constrs data_ =
    entry <> Ambiguous constrs data_
  Ambiguous constrs1 names1 <> Ambiguous constrs2 names2 =
    Ambiguous (constrs1 <> constrs2) (names1 <> names2)

aliases
  :: Scope
  -> (HashMap Name.QualifiedConstructor (HashSet Name.Surface), HashMap Name.Qualified (HashSet Name.Surface))
aliases scope =
  bimap (HashMap.fromListWith (<>)) (HashMap.fromListWith (<>)) $
    partitionEithers $
      concat
        [ case entry of
          Name name ->
            [Right (name, HashSet.singleton surfaceName)]
          Constructors constrs dataNames ->
            [ Left (constr, HashSet.singleton surfaceName)
            | constr <- HashSet.toList constrs
            ]
              <> [ Right (name, HashSet.singleton surfaceName)
                 | name <- HashSet.toList dataNames
                 ]
          Ambiguous constrs names ->
            [ Left (constr, HashSet.singleton surfaceName)
            | constr <- HashSet.toList constrs
            ]
              <> [ Right (name, HashSet.singleton surfaceName)
                 | name <- HashSet.toList names
                 ]
        | (surfaceName, entry) <- HashMap.toList scope
        ]
