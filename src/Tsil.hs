module Tsil where

import Protolude

data Tsil v = Nil | Snoc (Tsil v) v
  deriving Show

