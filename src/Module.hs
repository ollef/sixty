{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DuplicateRecordFields #-}

module Module where

import Data.HashSet (HashSet)
import Data.Persist
import qualified Name
import Orphans ()
import Protolude
import qualified Span

data Header = Header
  { _exposedNames :: !ExposedNames
  , _imports :: [Import]
  }
  deriving (Eq, Show, Generic, Persist, Hashable)

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
  = Exposed (HashSet Name.Surface)
  | AllExposed
  deriving (Eq, Show, Generic, Persist, Hashable)

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
  , _alias :: !(Span.Absolute, Name.Surface)
  , _importedNames :: !ExposedNames
  }
  deriving (Eq, Show, Generic, Persist, Hashable)
