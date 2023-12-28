{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DuplicateRecordFields #-}

module Module where

import Data.HashSet (HashSet)
import qualified Name
import Orphans ()
import Protolude
import qualified Span

data Header = Header
  { exposedNames :: !ExposedNames
  , imports :: [Import]
  }
  deriving (Eq, Show, Generic, Hashable)

instance Semigroup Header where
  Header exposed1 imports1 <> Header exposed2 imports2 =
    Header (exposed1 <> exposed2) (imports1 <> imports2)

instance Monoid Header where
  mempty =
    Header
      { exposedNames = mempty
      , imports = mempty
      }

data ExposedNames
  = Exposed (HashSet Name.Surface)
  | AllExposed
  deriving (Eq, Show, Generic, Hashable)

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
  { span :: !Span.Absolute
  , module_ :: !Name.Module
  , alias :: !(Span.Absolute, Name.Surface)
  , importedNames :: !ExposedNames
  }
  deriving (Eq, Show, Generic, Hashable)
