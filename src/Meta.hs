{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}

module Meta where

import Data.Persist
import Orphans ()
import Prettyprinter
import Protolude hiding (IntMap)

newtype Index = Index Int
  deriving (Eq, Ord, Show)
  deriving newtype (Enum, Persist, Hashable, Num)

instance Pretty Index where
  pretty (Index i) =
    "?" <> pretty i
