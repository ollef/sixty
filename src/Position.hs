{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
{-# language DerivingStrategies #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language OverloadedStrings #-}
module Position where

import Protolude

import qualified Data.Text.Unsafe as Text
import qualified Data.Text as Text

newtype Absolute = Absolute Int
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (Hashable, Num)

newtype Relative = Relative Int
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (Hashable, Num)

relativeTo :: Absolute -> Absolute -> Relative
relativeTo (Absolute base) (Absolute pos) =
  Relative (pos - base)

add :: Absolute -> Relative -> Absolute
add (Absolute base) (Relative rel) = Absolute $ base + rel

data LineColumn = LineColumn !Int !Int
  deriving (Eq, Ord, Show, Generic, Hashable)

lineColumn :: Absolute -> Text -> LineColumn
lineColumn (Absolute index) text =
  let
    prefix =
      Text.takeWord16 index text
  in
  LineColumn
    (Text.count "\n" prefix)
    (Text.lengthWord16 $ Text.takeWhileEnd (/= '\n') prefix)
