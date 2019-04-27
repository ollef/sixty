{-# language OverloadedStrings #-}
{-# language GADTs #-}
{-# language PatternSynonyms #-}
{-# language ViewPatterns #-}
module Index
  ( Index
  , pattern Zero
  , pattern Succ
  , absurdIndex
  , Level
  , toLevel
  , fromLevel
  ) where

import Protolude

import Bound.Var as Bound
import Data.Coerce

newtype Index v = Index Int
  deriving (Eq, Show)

pattern Zero :: (v ~ Bound.Var b v') => Index v
pattern Zero = Index 0

pattern Succ :: (v ~ (Bound.Var b v')) => Index v' -> Index v
pattern Succ index <- ((\(Index i) -> Index (i - 1)) -> index)
  where
    Succ (Index v) = Index (v + 1)

absurdIndex :: Index Void -> a
absurdIndex = panic "Absurd index"

newtype Level = Level Int
  deriving (Eq, Show)

toLevel :: Index (Var b2 v) -> Index (Var b1 (Var b2 v)) -> Level
toLevel i size = Level $ coerce size - coerce i - 1

fromLevel :: Level -> Index (Var b v) -> Index v
fromLevel l size = Index $ coerce size - coerce l - 1
