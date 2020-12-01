{-# language GeneralizedNewtypeDeriving #-}
module Index where

import Protolude

import Data.Persist

-------------------------------------------------------------------------------
-- Indices

newtype Index v = Index Int
  deriving (Eq, Ord, Show, Persist, Hashable)

-------------------------------------------------------------------------------
-- Phantom types

type Scope f v = f (Succ v)

data Succ v

zero :: Index (Succ v)
zero = Index 0

succ :: Index v -> Index (Succ v)
succ (Index v) = Index $ v + 1
