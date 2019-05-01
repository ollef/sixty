{-# language GeneralizedNewtypeDeriving #-}
module Var where

import Protolude

newtype Var = Var Int
  deriving (Eq, Hashable, Show)
