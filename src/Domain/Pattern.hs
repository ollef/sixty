{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
module Domain.Pattern where

import Protolude

import qualified Name
import Plicity

data Pattern
  = Wildcard
  | Con !Name.QualifiedConstructor [(Plicity, Pattern)]
  | Int !Integer
  deriving (Eq, Show, Generic, Hashable)
