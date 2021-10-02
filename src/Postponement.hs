{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}

module Postponement where

import Data.Persist
import Prettyprinter
import Orphans ()
import Protolude hiding (IntMap)

newtype Index = Index Int
  deriving (Eq, Ord, Show)
  deriving newtype (Persist, Hashable, Num)

instance Pretty Index where
  pretty (Index i) =
    "?" <> pretty i

data CanPostpone
  = Can'tPostpone
  | CanPostpone
  deriving (Show)
