{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Var where

import Protolude

newtype Var = Var Int
  deriving (Eq, Enum, Ord, Show, Hashable)
