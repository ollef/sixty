{-# language GeneralizedNewtypeDeriving #-}
module Index where

import Protolude

import Data.Persist

-------------------------------------------------------------------------------
-- Indices

newtype Index v = Index Int
  deriving (Eq, Show, Persist, Hashable)

-------------------------------------------------------------------------------
-- Phantom types

type Scope f v = f (Succ v)

data Succ v
