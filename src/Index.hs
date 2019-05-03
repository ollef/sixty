{-# language StandaloneDeriving #-}
{-# language UndecidableInstances #-}
module Index where

import Protolude

-------------------------------------------------------------------------------
-- Indices

newtype Index v = Index Int
  deriving (Eq, Show)

-------------------------------------------------------------------------------
-- Phantom types

type Scope f v = f (Succ v)

data Succ v
