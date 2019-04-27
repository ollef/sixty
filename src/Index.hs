{-# language GADTs #-}
{-# language OverloadedStrings #-}
{-# language PatternSynonyms #-}
{-# language StandaloneDeriving #-}
{-# language UndecidableInstances #-}
{-# language ViewPatterns #-}
module Index
  ( Index
  , pattern Zero
  , pattern Succ
  , absurdIndex

  , Scope(Scope)
  , Succ

  , Level
  , toLevel
  , fromLevel
  ) where

import Protolude

import Data.Coerce

-------------------------------------------------------------------------------
-- Indices

newtype Index v = Index Int
  deriving (Eq, Show)

pattern Zero :: Index (Succ v)
pattern Zero = Index 0

pattern Succ :: Index v -> Index (Succ v)
pattern Succ index <- ((\(Index i) -> Index (i - 1)) -> index)
  where
    Succ (Index v) = Index (v + 1)

absurdIndex :: Index Void -> a
absurdIndex = panic "Absurd index"

-------------------------------------------------------------------------------
-- Phantom types

newtype Scope f v = Scope (f (Succ v))

data Succ v

deriving instance Show (f (Succ v)) => Show (Scope f v)

-------------------------------------------------------------------------------
-- Levels

newtype Level = Level Int
  deriving (Eq, Show)

toLevel :: Index (Succ v) -> Index (Succ (Succ v)) -> Level
toLevel i size = Level $ coerce size - coerce i - 1

fromLevel :: Level -> Index (Succ v) -> Index v
fromLevel l size = Index $ coerce size - coerce l - 1
