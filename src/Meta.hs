{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}

module Meta where

import Orphans ()
import Prettyprinter
import Protolude hiding (IntMap)

newtype Index = Index Int
  deriving (Eq, Ord, Show)
  deriving newtype (Enum, Hashable, Num)

instance Pretty Index where
  pretty (Index i) =
    "?" <> pretty i
