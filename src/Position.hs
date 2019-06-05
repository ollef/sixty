{-# language DeriveGeneric #-}
{-# language GeneralizedNewtypeDeriving #-}
module Position where

import Protolude

newtype Absolute = Absolute Int
  deriving (Eq, Ord, Show, Generic, Hashable, Num)

newtype Relative = Relative Int
  deriving (Eq, Ord, Show, Generic, Hashable, Num)

relativeTo :: Absolute -> Absolute -> Relative
relativeTo (Absolute base) (Absolute pos) =
  Relative (pos - base)

add :: Absolute -> Relative -> Absolute
add (Absolute base) (Relative rel) = Absolute $ base + rel
