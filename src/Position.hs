{-# language DeriveGeneric #-}
{-# language GeneralizedNewtypeDeriving #-}
module Position where

import Protolude

newtype Absolute = Absolute Int
  deriving (Show, Generic, Hashable, Num)

newtype Relative = Relative Int
  deriving (Show, Generic, Hashable, Num)

relativeTo :: Absolute -> Absolute -> Relative
relativeTo (Absolute base) (Absolute pos) =
  Relative (pos - base)
