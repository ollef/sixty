{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Var where

import Data.Persist
import Protolude

newtype Var = Var Int
  deriving (Eq, Ord, Show, Hashable, Persist)
