{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DuplicateRecordFields #-}
module Module where

import Protolude

import Data.HashSet (HashSet)

import qualified Name

data Header = Header
  { _name :: !Name.Module
  , _exposedNames :: !ExposedNames
  , _imports :: [Import]
  } deriving (Eq, Show, Generic, Hashable)

data ExposedNames
  = Exposed (HashSet Name.Pre)
  | AllExposed
  deriving (Eq, Show, Generic, Hashable)

noneExposed :: ExposedNames
noneExposed = Exposed mempty

data Import = Import
  { _module :: !Name.Module
  , _alias :: !Name.Pre
  , _exposedNames :: !ExposedNames
  } deriving (Eq, Show, Generic, Hashable)
