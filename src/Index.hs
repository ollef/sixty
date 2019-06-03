{-# language GeneralizedNewtypeDeriving #-}
{-# language PatternSynonyms #-}
module Index where

import Protolude

-------------------------------------------------------------------------------
-- Indices

newtype Index v = Index Int
  deriving (Eq, Show, Hashable)

-------------------------------------------------------------------------------
-- Phantom types

type Scope f v = f (Succ v)

data Succ v

pattern Zero :: Index (Succ v)
pattern Zero = Index 0
