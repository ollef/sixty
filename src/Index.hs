{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Index where

import Protolude hiding (pred)

-------------------------------------------------------------------------------
-- Indices

newtype Index v = Index Int
  deriving (Eq, Ord, Show, Hashable)

-------------------------------------------------------------------------------
-- Phantom types

type Scope f v = f (Succ v)

data Zero

data Succ v

pattern Zero :: Index (Succ v)
pattern Zero = Index 0

pattern Succ :: Index v -> Index (Succ v)
pattern Succ i <-
  (pred -> Just i)
  where
    Succ (Index v) = Index $ v + 1

pred :: Index (Succ v) -> Maybe (Index v)
pred (Index 0) = Nothing
pred (Index n) = Just $ Index $ n - 1

{-# COMPLETE Zero, Succ #-}
