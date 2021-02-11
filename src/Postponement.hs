{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
{-# language DerivingStrategies #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language OverloadedStrings #-}
module Postponement where

import Data.Persist
import Data.Text.Prettyprint.Doc
import Orphans ()
import Protolude hiding (IntMap)

newtype Index = Index Int
  deriving (Eq, Ord, Show)
  deriving newtype (Persist, Hashable, Num)

instance Pretty Index where
  pretty (Index i) =
    "?" <> pretty i
