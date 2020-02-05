{-# language GeneralizedNewtypeDeriving #-}
module Var where

import Protolude

import Data.Persist

newtype Var = Var Int
  deriving (Eq, Ord, Show, Hashable, Persist)
