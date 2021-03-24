{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
{-# language DerivingStrategies #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language OverloadedStrings #-}
module Position where

import Protolude

import Data.Persist

import qualified Data.Text.Unsafe as Text
import qualified Data.Text as Text

newtype Absolute = Absolute Int
  deriving stock (Eq, Ord, Show)
  deriving newtype (Num, Hashable, Persist, NFData)

newtype Relative = Relative Int
  deriving stock (Eq, Ord, Show)
  deriving newtype (Num, Hashable, Persist)

relativeTo :: Absolute -> Absolute -> Relative
relativeTo (Absolute base) (Absolute pos) =
  Relative (pos - base)

add :: Absolute -> Relative -> Absolute
add (Absolute base) (Relative rel) = Absolute $ base + rel

data LineColumn = LineColumn !Int !Int
  deriving (Eq, Ord, Show, Generic, Persist, NFData)

addLine :: LineColumn -> LineColumn
addLine (LineColumn line _) =
  LineColumn (line + 1) 0

addColumns :: LineColumn -> Int -> LineColumn
addColumns (LineColumn line column) delta =
  LineColumn line $ column + delta

lineColumn :: Absolute -> Text -> (LineColumn, Text)
lineColumn (Absolute index) text =
  let
    prefix =
      Text.takeWord16 index text

    suffix =
      Text.dropWord16 index text

    linePrefixLength =
      Text.lengthWord16 $ Text.takeWhileEnd (/= '\n') prefix

    lineSuffixLength =
      Text.lengthWord16 $ Text.takeWhile (/= '\n') suffix

    lineStart =
      index - linePrefixLength

    lineLength =
      linePrefixLength + lineSuffixLength

    line =
      Text.takeWord16 lineLength $
      Text.dropWord16 lineStart text
  in
  ( LineColumn
    (Text.count "\n" prefix)
    linePrefixLength
  , line
  )
