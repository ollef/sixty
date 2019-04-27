{-# language OverloadedStrings #-}
{-# language GADTs #-}
{-# language PatternSynonyms #-}
{-# language ViewPatterns #-}
module Index
  ( Index
  , pattern Zero
  , pattern Succ
  , absurdIndex
  ) where

import Protolude

import Bound.Var as Bound

newtype Index v = Index Int
  deriving (Eq, Ord, Show)

pattern Zero :: (v ~ Bound.Var b v') => Index v
pattern Zero = Index 0

pattern Succ :: (v' ~ (Bound.Var b v)) => Index v -> Index v'
pattern Succ index <- ((\(Index i) -> Index (i - 1)) -> index)
  where
    Succ (Index v) = Index (v + 1)

absurdIndex :: Index Void -> a
absurdIndex i = panic "Absurd index"
