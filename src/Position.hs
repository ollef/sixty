{-# language DerivingStrategies #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language OverloadedStrings #-}
module Position where

import Protolude

import qualified Data.Text.Unsafe as Text
import qualified Data.Text as Text

newtype Absolute = Absolute Int
  deriving stock (Eq, Ord, Show)
  deriving newtype (Num, Hashable)

newtype Relative = Relative Int
  deriving stock (Eq, Ord, Show)
  deriving newtype (Num, Hashable)

relativeTo :: Absolute -> Absolute -> Relative
relativeTo (Absolute base) (Absolute pos) =
  Relative (pos - base)

add :: Absolute -> Relative -> Absolute
add (Absolute base) (Relative rel) = Absolute $ base + rel

data LineColumn = LineColumn !Int !Int
  deriving (Eq, Ord, Show)

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
