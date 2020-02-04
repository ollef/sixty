{-# language DeriveAnyClass #-}
{-# language DuplicateRecordFields #-}
module Module where

import Protolude

import Data.HashSet (HashSet)

import qualified Name
import qualified Span

data Header = Header
  { _exposedNames :: !ExposedNames
  , _imports :: [Import]
  } deriving (Eq, Show)

instance Semigroup Header where
  Header exposed1 imports1 <> Header exposed2 imports2 =
    Header (exposed1 <> exposed2) (imports1 <> imports2)

instance Monoid Header where
  mempty =
    Header
      { _exposedNames = mempty
      , _imports = mempty
      }

data ExposedNames
  = Exposed (HashSet Name.Pre)
  | AllExposed
  deriving (Eq, Show)

instance Semigroup ExposedNames where
  Exposed names1 <> Exposed names2 =
    Exposed $ names1 <> names2

  AllExposed <> _ =
    AllExposed

  _ <> AllExposed =
    AllExposed

instance Monoid ExposedNames where
  mempty =
    Exposed mempty

data Import = Import
  { _span :: !Span.Absolute
  , _module :: !Name.Module
  , _alias :: !Name.Pre
  , _importedNames :: !ExposedNames
  } deriving (Eq, Show)
