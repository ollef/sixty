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

newtype Scope f v = Scope (f (Succ v))

deriving instance Show (f (Succ v)) => Show (Scope f v)

data Succ v
