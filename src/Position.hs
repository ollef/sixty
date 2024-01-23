{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}

module Position where

import Protolude

newtype Absolute = Absolute Int
  deriving stock (Eq, Ord, Show)
  deriving newtype (Num, Hashable, NFData)

newtype Relative = Relative Int
  deriving stock (Eq, Ord, Show)
  deriving newtype (Num, Hashable)

relativeTo :: Absolute -> Absolute -> Relative
relativeTo (Absolute base) (Absolute pos) =
  Relative (pos - base)

add :: Absolute -> Relative -> Absolute
add (Absolute base) (Relative rel) = Absolute $ base + rel

data LineColumn = LineColumn !Int !Int
  deriving (Eq, Ord, Show, Generic, NFData)

addLine :: LineColumn -> LineColumn
addLine (LineColumn line _) =
  LineColumn (line + 1) 0

addColumns :: LineColumn -> Int -> LineColumn
addColumns (LineColumn line column) delta =
  LineColumn line $ column + delta
