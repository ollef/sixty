{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric  #-}

module Plicity where

import           Protolude

data Plicity
  = Explicit
  | Implicit
  deriving (Eq, Show, Generic, Hashable)
